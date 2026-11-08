module
public import Rivet.Model
import Rivet.ExecutionProperties
@[expose] public section
namespace Rivet

/-- Some finite execution reaches the final state. This alone does not guarantee
termination or correctness for every choice of undefined flags. -/
def Reaches (program : Program) (initial final : MachineState) : Prop :=
  ∃ (choices : FlagChoices) (steps : Nat), execute program steps initial choices = final

/-- Use a finite prefix of one supply, then continue with another. -/
private def appendChoices (choices : FlagChoices) (count : Nat) (rest : FlagChoices) : FlagChoices :=
  fun index => if index < count then choices index else rest (index - count)

@[simp] private theorem drop_appendChoices (choices rest : FlagChoices) (count : Nat) :
    (appendChoices choices count rest).drop count = rest := by
  funext index
  simp [FlagChoices.drop, appendChoices, Nat.not_lt_of_ge (Nat.le_add_right count index)]

/-- Bounded execution only depends on the corresponding finite prefix of choices. -/
private theorem execute_congr_choices (program : Program) (steps : Nat) (state : MachineState)
    (first second : FlagChoices) (agree : ∀ index < steps, first index = second index) :
    execute program steps state first = execute program steps state second := by
  induction steps generalizing state first second with
  | zero => rfl
  | succ steps inductionHypothesis =>
    simp only [execute, agree 0 (Nat.zero_lt_succ _)]
    apply inductionHypothesis
    intro index bound
    exact agree (1 + index) (by omega)

@[simp] private theorem execute_appendChoices (program : Program) (steps : Nat) (state : MachineState)
    (choices rest : FlagChoices) :
    execute program steps state (appendChoices choices steps rest) = execute program steps state choices := by
  apply execute_congr_choices
  intro index bound
  simp [appendChoices, bound]

theorem Reaches.trans (first : Reaches program initial intermediate)
    (second : Reaches program intermediate final) : Reaches program initial final := by
  obtain ⟨choices, earlier, rfl⟩ := first
  obtain ⟨rest, later, rfl⟩ := second
  exact ⟨appendChoices choices earlier rest, earlier + later, by simp [execute_add]⟩

/-- For every choice supply, a block eventually satisfies its postcondition.
The witness may depend on the supply; no instruction budget is required of callers. -/
structure Ensures (program : Program) (precondition postcondition : MachineState → Prop) : Prop where
  private mk ::
  private allChoices : ∀ initial, precondition initial → ∀ choices : FlagChoices,
    ∃ final, (∃ steps, execute program steps initial choices = final) ∧ postcondition final

/-- Obtain one reachable result. The contract itself guarantees the postcondition
for every choice supply; this theorem does not expose that implementation detail. -/
theorem Ensures.run (contract : Ensures program precondition postcondition)
    (initial : MachineState) (assumption : precondition initial) :
    ∃ final, Reaches program initial final ∧ postcondition final := by
  let choices : FlagChoices := fun _ => ⟨false, false⟩
  obtain ⟨final, reached, result⟩ := contract.allChoices initial assumption choices
  exact ⟨final, ⟨choices, reached⟩, result⟩

/-- Prove a contract separately for each initial state satisfying the precondition. -/
theorem Ensures.intro
    (body : ∀ initial, precondition initial → Ensures program (· = initial) postcondition) :
    Ensures program precondition postcondition :=
  ⟨fun initial assumption => (body initial assumption).allChoices initial rfl⟩

/-- Establish a contract by one instruction, for every permitted undefined flag value.
Instruction rules use this when the model has no more specific rule yet. -/
theorem Ensures.of_step
    (transition : ∀ initial, precondition initial → ∀ undefinedFlags,
      postcondition (step program initial undefinedFlags)) :
    Ensures program precondition postcondition := by
  constructor
  intro initial assumption choices
  exact ⟨step program initial (choices 0), ⟨1, rfl⟩, transition initial assumption (choices 0)⟩

/-- Retain reachability alongside a block's result, for deriving facts about the
initial/final state pair without opening the execution witness. -/
theorem Ensures.with_reachability (contract : Ensures program (· = initial) postcondition) :
    Ensures program (· = initial) (fun final => Reaches program initial final ∧ postcondition final) := by
  constructor
  intro actual equal choices
  subst actual
  obtain ⟨final, reached, result⟩ := contract.allChoices initial rfl choices
  exact ⟨final, reached, ⟨choices, reached⟩, result⟩

theorem Ensures.refl : Ensures program predicate predicate :=
  ⟨fun initial assumption _ => ⟨initial, ⟨0, rfl⟩, assumption⟩⟩

theorem Ensures.seq (first : Ensures program precondition intermediate)
    (second : Ensures program intermediate postcondition) : Ensures program precondition postcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨middle, ⟨earlier, rfl⟩, holds⟩ := first.allChoices initial assumption choices
  obtain ⟨final, ⟨later, reached⟩, result⟩ := second.allChoices _ holds (choices.drop earlier)
  exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

theorem Ensures.consequence (contract : Ensures program precondition postcondition)
    (strengthenPrecondition : ∀ state, strongerPrecondition state → precondition state)
    (weakenPostcondition : ∀ state, postcondition state → weakerPostcondition state) :
    Ensures program strongerPrecondition weakerPostcondition := by
  constructor
  intro initial assumption choices
  obtain ⟨final, reached, result⟩ := contract.allChoices initial (strengthenPrecondition _ assumption) choices
  exact ⟨final, reached, weakenPostcondition _ result⟩

/-- Iterate blocks while a natural-valued measure decreases. No instruction counts enter the rule. -/
theorem Ensures.loop (invariant finished : MachineState → Prop) (measure : MachineState → Nat)
    (body : ∀ initial, invariant initial → ¬ finished initial →
      Ensures program (· = initial) (fun final => invariant final ∧ measure final < measure initial)) :
    Ensures program invariant (fun final => invariant final ∧ finished final) := by
  constructor
  intro initial assumption choices
  induction bound : measure initial using Nat.strongRecOn generalizing initial choices with
  | ind bound inductionHypothesis =>
    by_cases done : finished initial
    · exact ⟨initial, ⟨0, rfl⟩, assumption, done⟩
    · obtain ⟨middle, ⟨earlier, rfl⟩, holds, decreases⟩ := (body initial assumption done).allChoices initial rfl choices
      obtain ⟨final, ⟨later, reached⟩, result⟩ := inductionHypothesis _ (by omega) _ holds (choices.drop earlier) rfl
      exact ⟨final, ⟨earlier + later, by simpa [execute_add] using reached⟩, result⟩

theorem Reaches.stopped (reached : Reaches program initial final)
    (stopped : initial.status.isRunning = false) : final = initial := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_stopped _ _ _ stopped

theorem Reaches.not_fault (reached : Reaches program initial final)
    (notFaulted : final.status ≠ .fault) : initial.status ≠ .fault := by
  intro faulted
  have equal := reached.stopped (by simp [faulted, ExecutionStatus.isRunning])
  subst final
  exact notFaulted faulted

-- Execution proofs are implementation details of the reachability guarantees.
@[simp] private theorem writeMemory_registers (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : (state.writeMemory address width value).registers = state.registers := rfl

@[simp] private theorem writeMemory_readHistory (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : (state.writeMemory address width value).readHistory = state.readHistory := rfl

@[simp] private theorem writeOperand_readHistory (state : MachineState) (operand : Operand)
    (value : BitVec 64) : (state.writeOperand operand value).readHistory = state.readHistory := by
  cases operand <;> simp [MachineState.writeOperand, MachineState.write]

private theorem op_preserves (operation : Op) (state : MachineState) (register : Reg) {undefinedFlags : FlagValues} {nextAddress : Nat} (unchanged : modifies operation register = false) :
    (stepOp operation nextAddress state undefinedFlags).registers register = state.registers register := by
  cases operation with
  | binary operation destination source =>
    simp only [stepOp, MachineState.binary]
    split
    · split
      · cases destination <;> simp_all [modifies, next, MachineState.writeOperand, MachineState.write, Ne.symm]
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

private theorem step_preserves (program : Program) (state : MachineState) (register : Reg) {undefinedFlags : FlagValues}
    (unchanged : ∀ instruction ∈ program, modifies instruction.op register = false) :
    (step program state undefinedFlags).registers register = state.registers register := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      apply op_preserves
      exact unchanged instruction (List.mem_of_find?_eq_some instructionAtIndex)
    · rfl
  · rfl

/-- A register untouched by every instruction is preserved for any amount of fuel. -/
private theorem execute_preserves (program : Program) (steps : Nat) (state : MachineState) (register : Reg) {choices : FlagChoices}
    (unchanged : ∀ instruction ∈ program, modifies instruction.op register = false) :
    (execute program steps state choices).registers register = state.registers register := by
  induction steps generalizing state choices with
  | zero => rfl
  | succ steps inductionHypothesis => rw [execute, inductionHypothesis, step_preserves program state register unchanged]

private theorem step_reads_monotone (program : Program) (state : MachineState) (access : Access) {undefinedFlags : FlagValues}
    (recorded : access ∈ state.readHistory) : access ∈ (step program state undefinedFlags).readHistory := by
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

private theorem execute_reads_monotone (program : Program) (state : MachineState) (steps : Nat) (access : Access) {choices : FlagChoices}
    (recorded : access ∈ state.readHistory) : access ∈ (execute program steps state choices).readHistory := by
  induction steps generalizing state choices with
  | zero => exact recorded
  | succ steps inductionHypothesis =>
    exact inductionHypothesis (step program state (choices 0)) (step_reads_monotone program state access recorded)

theorem Reaches.reads_mono (reached : Reaches program initial final)
    (recorded : access ∈ initial.readHistory) : access ∈ final.readHistory := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact execute_reads_monotone _ _ steps _ recorded

theorem Reaches.preserves_register (reached : Reaches program initial final) (register : Reg)
    (unchanged : program.all (fun instruction => !(modifies instruction.op register)) = true) :
    final.registers register = initial.registers register := by
  obtain ⟨choices, steps, rfl⟩ := reached
  apply execute_preserves
  intro instruction member
  have := (List.all_eq_true.mp unchanged) instruction member
  simpa using this

private structure MemoryInvariant (before after : Memory) : Prop where
  readable : after.readable = before.readable
  writable : after.writable = before.writable
  unwritable : ∀ address, before.writable address = false → after address = before address

private theorem MemoryInvariant.refl (memory : Memory) : MemoryInvariant memory memory := ⟨rfl, rfl, by intros; rfl⟩

private theorem MemoryInvariant.trans (first : MemoryInvariant before middle) (second : MemoryInvariant middle after) :
    MemoryInvariant before after := by
  refine ⟨second.readable.trans first.readable, second.writable.trans first.writable, ?_⟩
  intro address readonly
  rw [second.unwritable address (by rw [first.writable]; exact readonly), first.unwritable address readonly]

private theorem MemoryInvariant.storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256)
    (allowed : permits memory.writable address size = true) :
    MemoryInvariant memory (memory.storeBytes address size bytes) := by
  refine ⟨Memory.readable_storeBytes _ _ _ _, Memory.writable_storeBytes _ _ _ _, ?_⟩
  intro other readonly
  apply Memory.read_storeBytes_outside
  by_cases before : other < address
  · exact Or.inl before
  · by_cases after : address + size ≤ other
    · exact Or.inr after
    · have permitted := (permits_iff _ _ _).mp allowed |>.2 (other - address) (by omega)
      rw [Nat.add_sub_of_le (by omega), readonly] at permitted
      contradiction

private theorem MemoryInvariant.writeMemory (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) (allowed : permits state.memory.writable address width.bytes = true) :
    MemoryInvariant state.memory (state.writeMemory address width value).memory := by
  exact MemoryInvariant.storeBytes state.memory address width.bytes
    (fun offset => ⟨value.toNat / 256^offset % 256, Nat.mod_lt _ (by decide)⟩) allowed

private theorem MemoryInvariant.writeOperand (state : MachineState) (destination : Operand) (value : BitVec 64)
    (allowed : state.canWrite destination = true) :
    MemoryInvariant state.memory (state.writeOperand destination value).memory := by
  cases destination <;> try exact MemoryInvariant.refl _
  case memory width address => exact MemoryInvariant.writeMemory state _ width value allowed

/-- The memory effect of one decoded operation, including faulting paths. -/
private theorem op_memory_invariant (operation : Op) (state : MachineState) (nextPC : Nat) (flags : FlagValues) :
    MemoryInvariant state.memory (stepOp operation nextPC state flags).memory := by
  cases operation with
  | binary operation destination source =>
    simp only [stepOp, MachineState.binary]
    split
    · split
      · apply MemoryInvariant.writeOperand
        simp_all [Bool.and_eq_true]
      · exact MemoryInvariant.refl _
    · exact MemoryInvariant.refl _
  | mov destination source | not destination | setcc condition destination =>
    simp only [stepOp]
    split
    · apply MemoryInvariant.writeOperand
      simp_all [Bool.and_eq_true]
    · exact MemoryInvariant.refl _
  | shift operation destination count =>
    simp only [stepOp]
    split
    · split <;> apply MemoryInvariant.writeOperand <;>
        cases destination <;> simp_all [validShift, MachineState.canWrite]
    · exact MemoryInvariant.refl _
  | imul destination source immediate | cmovcc condition destination source =>
    simp only [stepOp]
    split
    · apply MemoryInvariant.writeOperand
      cases destination <;> simp_all [validImul, validConditionalMove, MachineState.canWrite]
    · exact MemoryInvariant.refl _
  | storeXmm kind destination source =>
    simp only [stepOp]
    split
    · exact MemoryInvariant.storeBytes state.memory (destination.evaluate state.registers).toNat 16
        (fun offset => ⟨(state.xmmRegisters source).toNat / 256^offset % 256, Nat.mod_lt _ (by decide)⟩) (by assumption)
    · exact MemoryInvariant.refl _
  | push source | call target =>
    simp only [stepOp]
    split
    · apply MemoryInvariant.writeMemory
      assumption
    · exact MemoryInvariant.refl _
  | _ =>
    simp only [stepOp]
    first
    | exact MemoryInvariant.refl _
    | (split <;> exact MemoryInvariant.refl _)

private theorem step_memory_invariant (program : Program) (state : MachineState) (flags : FlagValues) :
    MemoryInvariant state.memory (step program state flags).memory := by
  unfold step
  split
  · split
    · exact op_memory_invariant _ _ _ _
    · exact MemoryInvariant.refl _
  · exact MemoryInvariant.refl _

private theorem execute_memory_invariant (program : Program) (steps : Nat) (state : MachineState) (choices : FlagChoices) :
    MemoryInvariant state.memory (execute program steps state choices).memory := by
  induction steps generalizing state choices with
  | zero => exact MemoryInvariant.refl _
  | succ steps ih =>
    exact (step_memory_invariant program state (choices 0)).trans
      (ih (step program state (choices 0)) (choices.drop 1))

/-- Execution preserves the readable permission map, including when it faults. -/
theorem Reaches.preserves_readable (reached : Reaches program initial final) :
    final.memory.readable = initial.memory.readable := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact (execute_memory_invariant program steps initial choices).readable

/-- Execution preserves the writable permission map, including when it faults. -/
theorem Reaches.preserves_writable (reached : Reaches program initial final) :
    final.memory.writable = initial.memory.writable := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact (execute_memory_invariant program steps initial choices).writable

/-- Every initially unwritable byte is preserved by execution, including faulting
executions. This covers read-only data and unmapped addresses alike. -/
theorem Reaches.preserves_unwritable (reached : Reaches program initial final) (address : Nat)
    (readonly : initial.memory.writable address = false) :
    final.memory address = initial.memory address := by
  obtain ⟨choices, steps, rfl⟩ := reached
  exact (execute_memory_invariant program steps initial choices).unwritable address readonly

end Rivet
