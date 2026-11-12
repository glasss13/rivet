module
public import Rivet.Interpreter.Machine
public import Rivet.Laws.Memory
public import Rivet.Laws.Program
public import Rivet.Laws.Operands
import all Rivet.Interpreter.Machine
-- Laws of execution: block contracts (`Ensures`) and what execution preserves.
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

theorem Ensures.done {state : MachineState} (holds : postcondition state) :
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

theorem Ensures.consequence (contract : Ensures image state postcondition)
    (weaken : ∀ final, postcondition final → weakerPostcondition final) :
    Ensures image state weakerPostcondition := by
  constructor
  intro choices
  obtain ⟨final, reached, result⟩ := contract.allChoices choices
  exact ⟨final, reached, weaken _ result⟩

theorem Ensures.loop (invariant : MachineState → Prop) (measure : MachineState → Nat)
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

-- Execution proofs are implementation details of `Ensures.preserves_unwritable`.
private abbrev WritesWithin (image : Image) (before after : Memory) : Prop :=
  before.SameOutside after (image.writable · = true)

private theorem WritesWithin.storeBytes (memory : Memory) (base : BitVec 64) (length : Nat)
    (bytes : BitVec 64 → Fin 256) (allowed : permits image.writable base length = true) :
    WritesWithin image memory (memory.storeBytes base length bytes) :=
  Memory.SameOutside.refl.storeBytes (permits_iff.mp allowed).2

private theorem WritesWithin.writeMemory (state : MachineState) (address : BitVec 64) (width : Width)
    (value : BitVec 64)
    (allowed : permits image.writable address width.bytes = true) :
    WritesWithin image state.memory (state.writeMemory address width value).memory :=
  WritesWithin.storeBytes state.memory _ _ _ allowed

private theorem WritesWithin.writeOperand (state : MachineState) (destination : Operand) (value : BitVec 64)
    (allowed : state.canWrite image destination = true) :
    WritesWithin image state.memory (state.writeOperand64 destination value).memory := by
  cases destination <;> simp only [MachineState.writeOperand64] <;> try exact Memory.SameOutside.refl
  case memory width address =>
    rw [MachineState.canWrite_memory] at allowed
    exact WritesWithin.writeMemory state _ width value allowed

private theorem op_writes_within (operation : Op) (state : MachineState) (nextPC : BitVec 64) (flags : FlagValues) :
    WritesWithin image state.memory (stepOp image operation nextPC state flags).memory := by
  cases operation with
  | binary operation destination source =>
    simp only [stepOp, MachineState.binary]
    split
    · split
      · apply WritesWithin.writeOperand
        simp_all [Bool.and_eq_true]
      · exact Memory.SameOutside.refl
    · exact Memory.SameOutside.refl
  | mov destination source | not destination | setcc condition destination =>
    simp only [stepOp]
    split
    · apply WritesWithin.writeOperand
      simp_all [Bool.and_eq_true]
    · exact Memory.SameOutside.refl
  | shift operation destination count =>
    simp only [stepOp]
    split
    · split <;> apply WritesWithin.writeOperand <;>
        cases destination <;> simp_all [validShift]
    · exact Memory.SameOutside.refl
  | imul destination source immediate | cmovcc condition destination source =>
    simp only [stepOp]
    split
    · apply WritesWithin.writeOperand
      cases destination <;> simp_all [validImul, validConditionalMove]
    · exact Memory.SameOutside.refl
  | storeXmm kind destination source =>
    simp only [stepOp]
    split
    · exact WritesWithin.storeBytes state.memory _ _ _ (by assumption)
    · exact Memory.SameOutside.refl
  | push source | call target =>
    simp only [stepOp]
    split
    · apply WritesWithin.writeMemory
      assumption
    · exact Memory.SameOutside.refl
  | _ =>
    simp only [stepOp]
    first
    | exact Memory.SameOutside.refl
    | (split <;> exact Memory.SameOutside.refl)

private theorem step_writes_within (image : Image) (state : MachineState) (flags : FlagValues) :
    WritesWithin image state.memory (step image state flags).memory := by
  unfold step
  split
  · split
    · exact op_writes_within _ _ _ _
    · exact Memory.SameOutside.refl
  · exact Memory.SameOutside.refl

private theorem execute_writes_within (image : Image) (steps : Nat) (state : MachineState) (choices : FlagChoices) :
    WritesWithin image state.memory (execute image steps state choices).memory := by
  induction steps generalizing state choices with
  | zero => rw [execute_zero]; exact Memory.SameOutside.refl
  | succ steps ih =>
    rw [execute_succ]
    exact (step_writes_within image state (choices 0)).trans
      (ih (step image state (choices 0)) (choices.drop 1))

theorem Ensures.preserves_unwritable (contract : Ensures image initial postcondition) :
    Ensures image initial (fun final =>
      postcondition final ∧ initial.memory.SameOutside final.memory (image.writable · = true)) := by
  constructor
  intro choices
  obtain ⟨final, ⟨steps, reached⟩, result⟩ := contract.allChoices choices
  exact ⟨final, ⟨steps, reached⟩, result, reached ▸ execute_writes_within image steps initial choices⟩

end Rivet
