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

private theorem execute_zero (program : Program) (state : MachineState) (choices : FlagChoices) :
    execute program 0 state choices = state := by
  rw [execute]

private theorem execute_succ (program : Program) (steps : Nat) (state : MachineState) (choices : FlagChoices) :
    execute program (steps + 1) state choices =
      execute program steps (step program state (choices 0)) (choices.drop 1) := by
  rw [execute]

private theorem execute_add (program : Program) (firstSteps secondSteps : Nat) (state : MachineState)
    {choices : FlagChoices} :
    execute program (firstSteps + secondSteps) state choices =
      execute program secondSteps (execute program firstSteps state choices) (choices.drop firstSteps) := by
  induction firstSteps generalizing state choices with
  | zero => simp [execute_zero]
  | succ firstSteps inductionHypothesis =>
    simpa [Nat.succ_add, execute_succ, Nat.add_comm] using
      inductionHypothesis (step program state (choices 0)) (choices := choices.drop 1)

-- From `current`, for every value of the undefined flags, execution reaches in finitely many steps a
-- state that is `start` except for `changes` and satisfies `post`. A contract is stated from its start
-- (`current` is `start`); while stepping through it, `current` is the state reached so far.
structure Block (program : Program) (start : MachineState) (changes : Changes) (post : MachineState → Prop)
    (current : MachineState := start) : Prop where
  private mk ::
  private allChoices : ∀ choices : FlagChoices, ∃ final,
    (∃ steps, execute program steps current choices = final) ∧ final.Except start changes ∧ post final

private theorem Block.of_step {c : Changes} {post : MachineState → Prop}
    (kept : ∀ final, post final → final.Except initial c)
    (transition : ∀ undefinedFlags, post (step program initial undefinedFlags)) :
    Block program initial c post :=
  ⟨fun choices => ⟨step program initial (choices 0), ⟨1, by rw [execute_succ, execute_zero]⟩,
    kept _ (transition (choices 0)), transition (choices 0)⟩⟩

-- `done` and `then` prove a block from a state `t` it has reached, so they also apply at its start.
-- `done` proves `Q` and the change by reading `t` back to `s`, unless given proofs.

theorem Block.done {program : Program} {s t : MachineState} {c : Changes} {Q : MachineState → Prop}
    (holds : Q t := by rivet_known) (kept : t.Except s c := by rivet_known) : Block program s c Q t :=
  ⟨fun choices => ⟨t, ⟨0, execute_zero program t choices⟩, kept, holds⟩⟩

-- A nested block from `t`, then the rest of this block from every state it can end in, knowing what
-- the nested block left alone. The nested block may change anything on the way: only this block's
-- end is compared with its start.
theorem Block.then {program : Program} {s t : MachineState} {c₁ c : Changes} {P Q : MachineState → Prop}
    (inner : Block program t c₁ P) (rest : ∀ next, next.Except t c₁ → P next → Block program s c Q next) :
    Block program s c Q t := by
  constructor
  intro choices
  obtain ⟨middle, ⟨earlier, rfl⟩, kept, holds⟩ := inner.allChoices choices
  obtain ⟨final, ⟨later, reached⟩, result⟩ := (rest _ kept holds).allChoices (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

-- A loop whose head is `t`, as a block of its own. Each pass is the rest of that block from the
-- state the last pass ended in.
theorem Block.loop {program : Program} {t : MachineState} {c : Changes} {exit : MachineState → Prop}
    (invariant : MachineState → Prop) (measure : MachineState → Nat) (holds : invariant t)
    (body : ∀ current, current.Except t c → invariant current →
      Block program t c (fun next => invariant next ∧ measure next < measure current ∨ exit next) current) :
    Block program t c exit := by
  suffices loop : ∀ current, current.Except t c → invariant current → Block program t c exit current from
    loop t Internal.MachineState.Except.refl holds
  intro current same inv
  constructor
  intro choices
  induction bound : measure current using Nat.strongRecOn generalizing current choices with
  | ind bound inductionHypothesis =>
    obtain ⟨middle, ⟨earlier, rfl⟩, kept, ⟨again, smaller⟩ | out⟩ := (body current same inv).allChoices choices
    · obtain ⟨final, ⟨later, reached⟩, result⟩ :=
        inductionHypothesis _ (by omega) _ kept again (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩
    · exact ⟨_, ⟨earlier, rfl⟩, kept, out⟩

end Rivet
