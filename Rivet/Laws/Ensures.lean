module
public import Rivet.Interpreter.Machine
public import Rivet.Laws.Memory
public import Rivet.Laws.Program
public import Rivet.Laws.Operands
public import Rivet.Laws.Changes
import all Rivet.Interpreter.Machine
-- Laws of execution: `Ensures`, and block contracts (`Block`) that also say what changed.
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

structure Ensures (image : Image) (initial : MachineState) (postcondition : MachineState → Prop) : Prop where
  private mk ::
  private allChoices : ∀ choices : FlagChoices,
    ∃ final, (∃ steps, execute image steps initial choices = final) ∧ postcondition final

private theorem Ensures.of_step
    (transition : ∀ undefinedFlags, postcondition (step image initial undefinedFlags)) :
    Ensures image initial postcondition :=
  ⟨fun choices => ⟨step image initial (choices 0), ⟨1, by rw [execute_succ, execute_zero]⟩,
    transition (choices 0)⟩⟩

private theorem Ensures.done {state : MachineState} (holds : postcondition state) :
    Ensures image state postcondition :=
  ⟨fun choices => ⟨state, ⟨0, execute_zero image state choices⟩, holds⟩⟩

theorem Ensures.bind (first : Ensures image state intermediate)
    (continuation : ∀ next, intermediate next → Ensures image next postcondition) :
    Ensures image state postcondition := by
  constructor
  intro choices
  obtain ⟨middle, ⟨earlier, rfl⟩, holds⟩ := first.allChoices choices
  obtain ⟨final, ⟨later, reached⟩, result⟩ := (continuation _ holds).allChoices (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

private theorem Ensures.consequence (contract : Ensures image state postcondition)
    (weaken : ∀ final, postcondition final → weakerPostcondition final) :
    Ensures image state weakerPostcondition := by
  constructor
  intro choices
  obtain ⟨final, reached, result⟩ := contract.allChoices choices
  exact ⟨final, reached, weaken _ result⟩

private theorem Ensures.loop (invariant : MachineState → Prop) (measure : MachineState → Nat)
    (holds : invariant state)
    (body : ∀ current, invariant current →
      Ensures image current (fun next =>
        invariant next ∧ measure next < measure current ∨ postcondition next)) :
    Ensures image state postcondition := by
  constructor
  intro choices
  induction bound : measure state using Nat.strongRecOn generalizing state choices with
  | ind bound inductionHypothesis =>
    obtain ⟨middle, ⟨earlier, rfl⟩, ⟨holds, decreases⟩ | exits⟩ := (body state holds).allChoices choices
    · obtain ⟨final, ⟨later, reached⟩, result⟩ :=
        inductionHypothesis _ (by omega) holds (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩
    · exact ⟨_, ⟨earlier, rfl⟩, exits⟩

-- From `s`, execution ends in a state that is `s` except for `c` and satisfies `Q`.
abbrev Block (image : Image) (s : MachineState) (c : Changes) (Q : MachineState → Prop) : Prop :=
  Ensures image s (fun final => final.Except s c ∧ Q final)

theorem Block.ensures {image : Image} {s : MachineState} {c : Changes} {Q : MachineState → Prop}
    (block : Block image s c Q) : Ensures image s Q :=
  Ensures.consequence block fun _ post => post.2

-- The rules below prove a block from a state `t` it has reached, so they also apply at its start.

theorem Block.done {image : Image} {s t : MachineState} {c : Changes} {Q : MachineState → Prop}
    (holds : Q t) (kept : t.Except s c := by rivet_changes) :
    Ensures image t (fun final => final.Except s c ∧ Q final) :=
  Ensures.done ⟨kept, holds⟩

theorem Block.seq {image : Image} {s t : MachineState} {c₁ c : Changes} {P Q : MachineState → Prop}
    (first : Block image t c₁ P) (rest : ∀ next, next.Except t c₁ → P next → Block image next c Q)
    (within : c₁.Within c := by rivet_changes) (kept : t.Except s c := by rivet_changes) :
    Ensures image t (fun final => final.Except s c ∧ Q final) :=
  Ensures.bind first fun next post =>
    Ensures.consequence (rest next post.1 post.2) fun _ final =>
      ⟨final.1.trans ((post.1.mono within).trans kept), final.2⟩

theorem Block.loop {image : Image} {s t : MachineState} {c : Changes} {exit : MachineState → Prop}
    (invariant : MachineState → Prop) (measure : MachineState → Nat) (holds : invariant t)
    (body : ∀ current, current.Except t c → invariant current →
      Block image current c (fun next => invariant next ∧ measure next < measure current ∨ exit next))
    (kept : t.Except s c := by rivet_changes) :
    Ensures image t (fun final => final.Except s c ∧ exit final) :=
  Ensures.loop (fun current => current.Except t c ∧ invariant current) measure ⟨.refl, holds⟩
    fun current inv => Ensures.consequence (body current inv.1 inv.2) fun _ post =>
      match post.2 with
      | .inl again => .inl ⟨⟨post.1.trans inv.1, again.1⟩, again.2⟩
      | .inr out => .inr ⟨(post.1.trans inv.1).trans kept, out⟩

end Rivet
