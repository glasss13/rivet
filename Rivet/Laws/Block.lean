module
public import Rivet.Interpreter.Machine
public import Rivet.Laws.Memory
public import Rivet.Laws.Program
public import Rivet.Laws.Operands
public import Rivet.Laws.Changes
import all Rivet.Interpreter.Machine
-- Block contracts: what execution reaches from a state, and what it changed on the way.
@[expose] public section
namespace Rivet

@[simp] private theorem FlagChoices.drop_zero (choices : FlagChoices) : choices.drop 0 = choices := by
  funext index
  simp [drop]

@[simp] private theorem FlagChoices.drop_drop (choices : FlagChoices) (first second : Nat) :
    (choices.drop first).drop second = choices.drop (first + second) := by
  funext index
  simp [drop, Nat.add_assoc]

private theorem execute_zero (image : Image) (state : MachineState) (choices : FlagChoices) :
    execute image 0 state choices = state := by
  rw [execute]

private theorem execute_succ (image : Image) (steps : Nat) (state : MachineState) (choices : FlagChoices) :
    execute image (steps + 1) state choices =
      execute image steps (step image state (choices 0)) (choices.drop 1) := by
  rw [execute]

private theorem execute_add (image : Image) (firstSteps secondSteps : Nat) (state : MachineState)
    {choices : FlagChoices} :
    execute image (firstSteps + secondSteps) state choices =
      execute image secondSteps (execute image firstSteps state choices) (choices.drop firstSteps) := by
  induction firstSteps generalizing state choices with
  | zero => simp [execute_zero]
  | succ firstSteps inductionHypothesis =>
    simpa [Nat.succ_add, execute_succ, Nat.add_comm] using
      inductionHypothesis (step image state (choices 0)) (choices := choices.drop 1)

-- From `current`, for every value of the undefined flags, execution reaches in finitely many steps a
-- state that is `start` except for `changes` and satisfies `post`. A contract is stated from its start
-- (`current` is `start`); while stepping through it, `current` is the state reached so far.
structure Block (image : Image) (start : MachineState) (changes : Changes) (post : MachineState → Prop)
    (current : MachineState := start) : Prop where
  private mk ::
  private allChoices : ∀ choices : FlagChoices, ∃ final,
    (∃ steps, execute image steps current choices = final) ∧ final.Except start changes ∧ post final

private theorem Block.of_step {c : Changes} {post : MachineState → Prop}
    (kept : ∀ final, post final → final.Except initial c)
    (transition : ∀ undefinedFlags, post (step image initial undefinedFlags)) :
    Block image initial c post :=
  ⟨fun choices => ⟨step image initial (choices 0), ⟨1, by rw [execute_succ, execute_zero]⟩,
    kept _ (transition (choices 0)), transition (choices 0)⟩⟩

-- The rules below prove a block from a state `t` it has reached, so they also apply at its start.

theorem Block.done {image : Image} {s t : MachineState} {c : Changes} {Q : MachineState → Prop}
    (holds : Q t) (kept : t.Except s c := by rivet_changes) : Block image s c Q t :=
  ⟨fun choices => ⟨t, ⟨0, execute_zero image t choices⟩, kept, holds⟩⟩

-- One contract from `t`, then the rest of the block from every state it can end in. `rivet_step`
-- uses it with an instruction's contract; the first contract's change is not needed.
theorem Block.then {image : Image} {s t : MachineState} {c₁ c : Changes} {P Q : MachineState → Prop}
    (first : Block image t c₁ P) (rest : ∀ next, P next → Block image s c Q next) :
    Block image s c Q t := by
  constructor
  intro choices
  obtain ⟨middle, ⟨earlier, rfl⟩, -, holds⟩ := first.allChoices choices
  obtain ⟨final, ⟨later, reached⟩, result⟩ := (rest _ holds).allChoices (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

theorem Block.seq {image : Image} {s t : MachineState} {c₁ c : Changes} {P Q : MachineState → Prop}
    (first : Block image t c₁ P) (rest : ∀ next, next.Except t c₁ → P next → Block image next c Q)
    (within : c₁.Within c := by rivet_changes) (kept : t.Except s c := by rivet_changes) :
    Block image s c Q t := by
  constructor
  intro choices
  obtain ⟨middle, ⟨earlier, rfl⟩, same, holds⟩ := first.allChoices choices
  obtain ⟨final, ⟨later, reached⟩, last, result⟩ := (rest _ same holds).allChoices (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩,
    last.trans ((same.mono within).trans kept), result⟩

theorem Block.loop {image : Image} {s t : MachineState} {c : Changes} {exit : MachineState → Prop}
    (invariant : MachineState → Prop) (measure : MachineState → Nat) (holds : invariant t)
    (body : ∀ current, current.Except t c → invariant current →
      Block image current c (fun next => invariant next ∧ measure next < measure current ∨ exit next))
    (kept : t.Except s c := by rivet_changes) :
    Block image s c exit t := by
  suffices loop : ∀ current, current.Except t c → invariant current → Block image s c exit current from
    loop t .refl holds
  intro current same inv
  constructor
  intro choices
  induction bound : measure current using Nat.strongRecOn generalizing current choices with
  | ind bound inductionHypothesis =>
    obtain ⟨middle, ⟨earlier, rfl⟩, step, ⟨again, smaller⟩ | out⟩ := (body current same inv).allChoices choices
    · obtain ⟨final, ⟨later, reached⟩, result⟩ :=
        inductionHypothesis _ (by omega) _ (step.trans same) again (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩
    · exact ⟨_, ⟨earlier, rfl⟩, (step.trans same).trans kept, out⟩

end Rivet
