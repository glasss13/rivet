module
public import Rivet.Model
import all Rivet.Model
@[expose] public section
namespace Rivet

/-- Some finite execution reaches the final state. This alone does not guarantee
termination or correctness for every choice of undefined flags. -/
def Reaches (image : Image) (initial final : MachineState) : Prop :=
  ∃ (choices : FlagChoices) (steps : Nat), execute image steps initial choices = final

/-- Use a finite prefix of one supply, then continue with another. -/
private def appendChoices (choices : FlagChoices) (count : Nat) (rest : FlagChoices) : FlagChoices :=
  fun index => if index < count then choices index else rest (index - count)

@[simp] private theorem drop_appendChoices (choices rest : FlagChoices) (count : Nat) :
    (appendChoices choices count rest).drop count = rest := by
  funext index
  simp [FlagChoices.drop, appendChoices, Nat.not_lt_of_ge (Nat.le_add_right count index)]

/-- Bounded execution only depends on the corresponding finite prefix of choices. -/
private theorem execute_congr_choices (image : Image) (steps : Nat) (state : MachineState)
    (first second : FlagChoices) (agree : ∀ index < steps, first index = second index) :
    execute image steps state first = execute image steps state second := by
  induction steps generalizing state first second with
  | zero => rfl
  | succ steps inductionHypothesis =>
    simp only [execute, agree 0 (Nat.zero_lt_succ _)]
    apply inductionHypothesis
    intro index bound
    exact agree (1 + index) (by omega)

@[simp] private theorem execute_appendChoices (image : Image) (steps : Nat) (state : MachineState)
    (choices rest : FlagChoices) :
    execute image steps state (appendChoices choices steps rest) = execute image steps state choices := by
  apply execute_congr_choices
  intro index bound
  simp [appendChoices, bound]

theorem Reaches.trans (first : Reaches image initial intermediate)
    (second : Reaches image intermediate final) : Reaches image initial final := by
  obtain ⟨choices, earlier, rfl⟩ := first
  obtain ⟨rest, later, rfl⟩ := second
  exact ⟨appendChoices choices earlier rest, earlier + later, by simp [execute_add]⟩

/-- For every choice supply, a block eventually satisfies its postcondition.
The witness may depend on the supply; no instruction budget is required of callers. -/
structure Ensures (image : Image) (precondition postcondition : MachineState → Prop) : Prop where
  private mk ::
  private allChoices : ∀ initial, precondition initial → ∀ choices : FlagChoices,
    ∃ final, (∃ steps, execute image steps initial choices = final) ∧ postcondition final

/-- Obtain one reachable result. The contract itself guarantees the postcondition
for every choice supply; this theorem does not expose that implementation detail. -/
theorem Ensures.run (contract : Ensures image precondition postcondition)
    (initial : MachineState) (assumption : precondition initial) :
    ∃ final, Reaches image initial final ∧ postcondition final := by
  let choices : FlagChoices := fun _ => ⟨false, false⟩
  obtain ⟨final, reached, result⟩ := contract.allChoices initial assumption choices
  exact ⟨final, ⟨choices, reached⟩, result⟩

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
  exact ⟨step image initial (choices 0), ⟨1, rfl⟩, transition initial assumption (choices 0)⟩

/-- Retain reachability alongside a block's result, for deriving facts about the
initial/final state pair without opening the execution witness. -/
theorem Ensures.with_reachability (contract : Ensures image (· = initial) postcondition) :
    Ensures image (· = initial) (fun final => Reaches image initial final ∧ postcondition final) := by
  constructor
  intro actual equal choices
  subst actual
  obtain ⟨final, reached, result⟩ := contract.allChoices initial rfl choices
  exact ⟨final, reached, ⟨choices, reached⟩, result⟩

theorem Ensures.refl : Ensures image predicate predicate :=
  ⟨fun initial assumption _ => ⟨initial, ⟨0, rfl⟩, assumption⟩⟩

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
    · exact ⟨initial, ⟨0, rfl⟩, assumption, done⟩
    · obtain ⟨middle, ⟨earlier, rfl⟩, holds, decreases⟩ := (body initial assumption done).allChoices initial rfl choices
      obtain ⟨final, ⟨later, reached⟩, result⟩ := inductionHypothesis _ (by omega) _ holds (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

/-- A stopped state remains unchanged under any further bounded execution. -/
theorem execute_stopped (image : Image) (steps : Nat) (state : MachineState) {choices : FlagChoices} (stopped : state.status.isRunning = false) :
    execute image steps state choices = state := by
  have stepUnchanged (undefinedFlags : FlagValues) : step image state undefinedFlags = state := by
    cases status : state.status <;> simp_all [step, ExecutionStatus.isRunning]
  induction steps generalizing choices with
  | zero => rfl
  | succ steps inductionHypothesis => simpa [execute, stepUnchanged] using inductionHypothesis (choices := choices.drop 1)

theorem Reaches.stopped (reached : Reaches image initial final)
    (stopped : initial.status.isRunning = false) : final = initial := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_stopped _ _ _ stopped

theorem Reaches.not_fault (reached : Reaches image initial final)
    (notFaulted : final.status ≠ .fault) : initial.status ≠ .fault := by
  intro faulted
  have equal := reached.stopped (by simp [faulted, ExecutionStatus.isRunning])
  subst final
  exact notFaulted faulted

-- Execution proofs are implementation details of the reachability guarantees.
@[simp] private theorem writeMemory_registers (state : MachineState) (address : BitVec 64) (width : Width)
    (value : BitVec 64) : (state.writeMemory address width value).registers = state.registers := rfl

@[simp] private theorem writeMemory_readHistory (state : MachineState) (address : BitVec 64) (width : Width)
    (value : BitVec 64) : (state.writeMemory address width value).readHistory = state.readHistory := rfl

@[simp] private theorem writeOperand_readHistory (state : MachineState) (operand : Operand)
    (value : BitVec 64) : (state.writeOperand operand value).readHistory = state.readHistory := by
  cases operand <;> simp [MachineState.writeOperand, MachineState.write]

private theorem op_preserves (image : Image) (operation : Op) (state : MachineState) (register : Reg) {undefinedFlags : FlagValues} {nextAddress : BitVec 64} (unchanged : modifies operation register = false) :
    (stepOp image operation nextAddress state undefinedFlags).registers register = state.registers register := by
  cases operation with
  | binary operation destination source =>
    simp only [stepOp, MachineState.binary]
    split
    · split
      · cases operation <;> cases destination <;>
          simp_all [BinaryOp.writes, modifies, next, MachineState.writeOperand, MachineState.write, Ne.symm]
      · rfl
    · rfl
  | shift operation destination count =>
    simp only [stepOp]
    split
    · split <;> cases destination <;>
        simp_all [modifies, next, MachineState.writeOperand, MachineState.write, Ne.symm]
    · rfl
  | imul destination source immediate | not destination | mov destination source | setcc _ destination | cmovcc _ destination source =>
    simp only [stepOp]
    split
    · cases destination <;>
        simp_all [modifies, next, MachineState.writeOperand, MachineState.write, Ne.symm]
    · rfl
  | _ =>
    simp_all [modifies, stepOp, next, MachineState.write, Ne.symm] <;>
      split <;> simp_all [Ne.symm]

private theorem step_preserves (image : Image) (state : MachineState) (register : Reg) {undefinedFlags : FlagValues}
    (unchanged : ∀ instruction ∈ image.program, modifies instruction.op register = false) :
    (step image state undefinedFlags).registers register = state.registers register := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      apply op_preserves
      exact unchanged instruction (List.mem_of_find?_eq_some instructionAtIndex)
    · rfl
  · rfl

/-- A register untouched by every instruction is preserved for any amount of fuel. -/
private theorem execute_preserves (image : Image) (steps : Nat) (state : MachineState) (register : Reg) {choices : FlagChoices}
    (unchanged : ∀ instruction ∈ image.program, modifies instruction.op register = false) :
    (execute image steps state choices).registers register = state.registers register := by
  induction steps generalizing state choices with
  | zero => rfl
  | succ steps inductionHypothesis => rw [execute, inductionHypothesis, step_preserves image state register unchanged]

private theorem step_reads_monotone (image : Image) (state : MachineState) (access : Access) {undefinedFlags : FlagValues}
    (recorded : access ∈ state.readHistory) : access ∈ (step image state undefinedFlags).readHistory := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      cases instruction.op with
      | binary operation destination source =>
        simp only [stepOp, MachineState.binary]
        split
        · cases destination <;> cases source <;> simp_all [next, MachineState.recordRead]
        · exact recorded
      | shift operation destination count =>
        simp only [stepOp]
        split
        · split <;> simp_all [next]
        · exact recorded
      | imul destination source immediate | not source | mov destination source | movzx destination source | movsxd destination source
      | cmovcc _ destination source =>
        simp only [stepOp]
        split
        · cases source <;> simp_all [next, MachineState.recordRead, MachineState.write]
        · exact recorded
      | _ =>
        simp_all [stepOp, next, MachineState.write] <;> split <;> simp_all
    · exact recorded
  · exact recorded

private theorem execute_reads_monotone (image : Image) (state : MachineState) (steps : Nat) (access : Access) {choices : FlagChoices}
    (recorded : access ∈ state.readHistory) : access ∈ (execute image steps state choices).readHistory := by
  induction steps generalizing state choices with
  | zero => exact recorded
  | succ steps inductionHypothesis =>
    exact inductionHypothesis (step image state (choices 0)) (step_reads_monotone image state access recorded)

theorem Reaches.reads_mono (reached : Reaches image initial final)
    (recorded : access ∈ initial.readHistory) : access ∈ final.readHistory := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_reads_monotone _ _ steps _ recorded

theorem Reaches.preserves_register (reached : Reaches image initial final) (register : Reg)
    (unchanged : image.program.all (fun instruction => !(modifies instruction.op register)) = true) :
    final.registers register = initial.registers register := by
  obtain ⟨choices, steps, rfl⟩ := reached
  apply execute_preserves
  intro instruction member
  have := (List.all_eq_true.mp unchanged) instruction member
  simpa using this

/-- Memory changes only at writable addresses: stores check write permission. -/
private abbrev WritesWithin (image : Image) (before after : Memory) : Prop :=
  before.SameOutside after (image.writable · = true)

private theorem WritesWithin.storeBytes (memory : Memory) (start stop : BitVec 64)
    (bytes : BitVec 64 → Fin 256) (allowed : permits image.writable start stop = true) :
    WritesWithin image memory (memory.storeBytes start stop bytes) :=
  (Memory.SameOutside.refl _ _).storeBytes bytes ((permits_iff _ _ _).mp allowed).2

private theorem WritesWithin.writeMemory (state : MachineState) (address : BitVec 64) (width : Width)
    (value : BitVec 64)
    (allowed : permits image.writable address (address + BitVec.ofNat 64 width.bytes) = true) :
    WritesWithin image state.memory (state.writeMemory address width value).memory :=
  WritesWithin.storeBytes state.memory _ _ _ allowed

private theorem WritesWithin.writeOperand (state : MachineState) (destination : Operand) (value : BitVec 64)
    (allowed : state.canWrite image destination = true) :
    WritesWithin image state.memory (state.writeOperand destination value).memory := by
  cases destination <;> try exact Memory.SameOutside.refl _ _
  case memory width address => exact WritesWithin.writeMemory state _ width value allowed

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
      · exact Memory.SameOutside.refl _ _
    · exact Memory.SameOutside.refl _ _
  | mov destination source | not destination | setcc condition destination =>
    simp only [stepOp]
    split
    · apply WritesWithin.writeOperand
      simp_all [Bool.and_eq_true]
    · exact Memory.SameOutside.refl _ _
  | shift operation destination count =>
    simp only [stepOp]
    split
    · split <;> apply WritesWithin.writeOperand <;>
        cases destination <;> simp_all [validShift, MachineState.canWrite]
    · exact Memory.SameOutside.refl _ _
  | imul destination source immediate | cmovcc condition destination source =>
    simp only [stepOp]
    split
    · apply WritesWithin.writeOperand
      cases destination <;> simp_all [validImul, validConditionalMove, MachineState.canWrite]
    · exact Memory.SameOutside.refl _ _
  | storeXmm kind destination source =>
    simp only [stepOp]
    split
    · exact WritesWithin.storeBytes state.memory _ _ _ (by assumption)
    · exact Memory.SameOutside.refl _ _
  | push source | call target =>
    simp only [stepOp]
    split
    · apply WritesWithin.writeMemory
      assumption
    · exact Memory.SameOutside.refl _ _
  | _ =>
    simp only [stepOp]
    first
    | exact Memory.SameOutside.refl _ _
    | (split <;> exact Memory.SameOutside.refl _ _)

private theorem step_writes_within (image : Image) (state : MachineState) (flags : FlagValues) :
    WritesWithin image state.memory (step image state flags).memory := by
  unfold step
  split
  · split
    · exact op_writes_within _ _ _ _
    · exact Memory.SameOutside.refl _ _
  · exact Memory.SameOutside.refl _ _

private theorem execute_writes_within (image : Image) (steps : Nat) (state : MachineState) (choices : FlagChoices) :
    WritesWithin image state.memory (execute image steps state choices).memory := by
  induction steps generalizing state choices with
  | zero => exact Memory.SameOutside.refl _ _
  | succ steps ih =>
    exact (step_writes_within image state (choices 0)).trans
      (ih (step image state (choices 0)) (choices.drop 1))

/-- Execution changes memory only where the image allows writes, including when it
faults. Read-only data and unmapped addresses are unchanged. -/
theorem Reaches.preserves_unwritable (reached : Reaches image initial final) :
    initial.memory.SameOutside final.memory (image.writable · = true) := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_writes_within image steps initial choices

end Rivet
