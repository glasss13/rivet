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

/-- `Ensures image precondition postcondition` means: for every initial state satisfying
`precondition` and every supply of undefined-flag values, some finite number of interpreter
steps from that state reaches a state satisfying `postcondition`. Zero steps is allowed. The
number of steps may depend on the initial state and the supply, and no step count is exposed. -/
structure Ensures (image : Image) (precondition postcondition : MachineState → Prop) : Prop where
  private mk ::
  private allChoices : ∀ initial, precondition initial → ∀ choices : FlagChoices,
    ∃ final, (∃ steps, execute image steps initial choices = final) ∧ postcondition final

/-- Prove a contract separately for each initial state satisfying the precondition. -/
theorem Ensures.intro
    (body : ∀ initial, precondition initial → Ensures image (· = initial) postcondition) :
    Ensures image precondition postcondition :=
  ⟨fun initial assumption => (body initial assumption).allChoices initial rfl⟩

/-- Internal bridge from one interpreter step to an instruction contract. -/
private theorem Ensures.of_step
    (transition : ∀ initial, precondition initial → ∀ undefinedFlags,
      postcondition (step image initial undefinedFlags)) :
    Ensures image precondition postcondition := by
  constructor
  intro initial assumption choices
  exact ⟨step image initial (choices 0), ⟨1, by rw [execute_succ, execute_zero]⟩,
    transition initial assumption (choices 0)⟩

theorem Ensures.refl : Ensures image predicate predicate :=
  ⟨fun initial assumption choices => ⟨initial, ⟨0, execute_zero image initial choices⟩, assumption⟩⟩

theorem Ensures.seq (first : Ensures image precondition intermediate)
    (second : Ensures image intermediate postcondition) : Ensures image precondition postcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨middle, ⟨earlier, rfl⟩, holds⟩ := first.allChoices initial assumption choices
  obtain ⟨final, ⟨later, reached⟩, result⟩ := second.allChoices _ holds (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

/-- Continue from each state the first contract can reach, as a named state.
For an exact-state contract (`· = e`), the continuation receives a fresh state
`t` with `t = e` rather than the expression `e` itself. -/
theorem Ensures.bind (first : Ensures image precondition intermediate)
    (continuation : ∀ state, intermediate state → Ensures image (· = state) postcondition) :
    Ensures image precondition postcondition :=
  first.seq (Ensures.intro continuation)

theorem Ensures.consequence (contract : Ensures image precondition postcondition)
    (strengthenPrecondition : ∀ state, strongerPrecondition state → precondition state)
    (weakenPostcondition : ∀ state, postcondition state → weakerPostcondition state) :
    Ensures image strongerPrecondition weakerPostcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨final, reached, result⟩ := contract.allChoices initial (strengthenPrecondition _ assumption) choices
  exact ⟨final, reached, weakenPostcondition _ result⟩

/-- Iterate blocks while a natural-valued measure decreases. No instruction counts enter the rule. -/
theorem Ensures.loop (invariant finished : MachineState → Prop) (measure : MachineState → Nat)
    (body : ∀ initial, invariant initial → ¬ finished initial →
      Ensures image (· = initial) (fun final => invariant final ∧ measure final < measure initial)) :
    Ensures image invariant (fun final => invariant final ∧ finished final) := by
  constructor
  intro initial assumption choices
  induction bound : measure initial using Nat.strongRecOn generalizing initial choices with
  | ind bound inductionHypothesis =>
    by_cases done : finished initial
    · exact ⟨initial, ⟨0, execute_zero image initial choices⟩, assumption, done⟩
    · obtain ⟨middle, ⟨earlier, rfl⟩, holds, decreases⟩ := (body initial assumption done).allChoices initial rfl choices
      obtain ⟨final, ⟨later, reached⟩, result⟩ := inductionHypothesis _ (by omega) _ holds (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

-- Execution proofs are implementation details of `Ensures.preserves_unwritable`.
/-- Memory changes only at writable addresses: stores check write permission. -/
private abbrev WritesWithin (image : Image) (before after : Memory) : Prop :=
  before.SameOutside after (image.writable · = true)

private theorem WritesWithin.storeBytes (memory : Memory) (start stop : BitVec 64)
    (bytes : BitVec 64 → Fin 256) (allowed : permits image.writable start stop = true) :
    WritesWithin image memory (memory.storeBytes start stop bytes) :=
  Memory.SameOutside.refl.storeBytes (permits_iff.mp allowed).2

private theorem WritesWithin.writeMemory (state : MachineState) (address : BitVec 64) (width : Width)
    (value : BitVec 64)
    (allowed : permits image.writable address (address + BitVec.ofNat 64 width.bytes) = true) :
    WritesWithin image state.memory (state.writeMemory address width value).memory :=
  WritesWithin.storeBytes state.memory _ _ _ allowed

private theorem WritesWithin.writeOperand (state : MachineState) (destination : Operand) (value : BitVec 64)
    (allowed : state.canWrite image destination = true) :
    WritesWithin image state.memory (state.writeOperand destination value).memory := by
  cases destination <;>
    simp only [MachineState.writeOperand_reg8, MachineState.writeOperand_reg16,
      MachineState.writeOperand_reg32, MachineState.writeOperand_reg64,
      MachineState.writeOperand_memory, MachineState.writeOperand_immediate] <;>
    try exact Memory.SameOutside.refl
  case memory width address =>
    rw [MachineState.canWrite_memory] at allowed
    exact WritesWithin.writeMemory state _ width value allowed

/-- The memory effect of one decoded operation, including faulting paths. -/
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

/-- Execution changes memory only where the image allows writes, including when it
faults: read-only data and unmapped addresses keep their bytes. -/
theorem Ensures.preserves_unwritable (contract : Ensures image (· = initial) postcondition) :
    Ensures image (· = initial) (fun final =>
      postcondition final ∧ initial.memory.SameOutside final.memory (image.writable · = true)) := by
  constructor
  intro actual equal choices
  subst actual
  obtain ⟨final, ⟨steps, reached⟩, result⟩ := contract.allChoices initial rfl choices
  exact ⟨final, ⟨steps, reached⟩, result, reached ▸ execute_writes_within image steps initial choices⟩

end Rivet
