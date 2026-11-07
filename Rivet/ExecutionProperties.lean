module
public import Rivet.Model
@[expose] public section
namespace Rivet

@[simp] private theorem writeMemory_registers (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : (state.writeMemory address width value).registers = state.registers := by
  unfold MachineState.writeMemory
  generalize List.range width.bytes = offsets
  induction offsets generalizing state with
  | nil => rfl
  | cons offset offsets inductionHypothesis =>
    simpa [List.foldl, MachineState.storeByte] using inductionHypothesis
      (state.storeByte (address + offset) ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩)

@[simp] theorem MachineState.writeMemory_status (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : (state.writeMemory address width value).status = state.status := by
  unfold MachineState.writeMemory
  generalize List.range width.bytes = offsets
  induction offsets generalizing state with
  | nil => rfl
  | cons offset offsets inductionHypothesis =>
    simpa [List.foldl, MachineState.storeByte] using inductionHypothesis
      (state.storeByte (address + offset) ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩)

@[simp] theorem MachineState.writeOperand_status (state : MachineState) (operand : Operand)
    (value : BitVec 64) : (state.writeOperand operand value).status = state.status := by
  cases operand <;> simp [MachineState.writeOperand, MachineState.write]

@[simp] private theorem writeMemory_readHistory (state : MachineState) (address : Nat) (width : Width)
    (value : BitVec 64) : (state.writeMemory address width value).readHistory = state.readHistory := by
  unfold MachineState.writeMemory
  generalize List.range width.bytes = offsets
  induction offsets generalizing state with
  | nil => rfl
  | cons offset offsets inductionHypothesis =>
    simpa [List.foldl, MachineState.storeByte] using inductionHypothesis
      (state.storeByte (address + offset)
        ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩)

@[simp] private theorem writeOperand_readHistory (state : MachineState) (operand : Operand)
    (value : BitVec 64) : (state.writeOperand operand value).readHistory = state.readHistory := by
  cases operand <;> simp [MachineState.writeOperand, MachineState.write]

theorem op_preserves (operation : Op) (state : MachineState) (register : Reg) {undefinedFlags : FlagValues} (unchanged : modifies operation register = false) :
    (stepOp operation state undefinedFlags).registers register = state.registers register := by
  cases operation with
  | binary operation destination source =>
    simp only [stepOp, MachineState.binary]
    split
    · split
      · cases destination <;> simp_all [modifies, Operand.register, next, MachineState.writeOperand, MachineState.write, Ne.symm]
      · rfl
    · rfl
  | not destination | mov destination source | setcc _ destination | cmovcc _ destination source =>
    simp only [stepOp]
    split
    · cases destination <;>
        simp_all [modifies, Operand.register, next, MachineState.writeOperand, MachineState.write, Ne.symm]
    · rfl
  | _ =>
    simp_all [modifies, stepOp, next, MachineState.write, Ne.symm] <;>
      split <;> simp_all [Ne.symm]

theorem step_preserves (program : Program) (state : MachineState) (register : Reg) {undefinedFlags : FlagValues}
    (unchanged : ∀ instruction ∈ program, modifies instruction.op register = false) :
    (step program state undefinedFlags).registers register = state.registers register := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      apply op_preserves
      exact unchanged instruction (List.mem_of_getElem? instructionAtIndex)
    · rfl
  · rfl

/-- A register untouched by every instruction is preserved for any amount of fuel. -/
theorem execute_preserves (program : Program) (steps : Nat) (state : MachineState) (register : Reg) {choices : FlagChoices}
    (unchanged : ∀ instruction ∈ program, modifies instruction.op register = false) :
    (execute program steps state choices).registers register = state.registers register := by
  induction steps generalizing state choices with
  | zero => rfl
  | succ steps inductionHypothesis => rw [execute, inductionHypothesis, step_preserves program state register unchanged]

theorem execute_stopped (program : Program) (steps : Nat) (state : MachineState) {choices : FlagChoices} (stopped : state.status.isRunning = false) :
    execute program steps state choices = state := by
  have stepUnchanged (undefinedFlags : FlagValues) : step program state undefinedFlags = state := by
    cases status : state.status <;> simp_all [step, ExecutionStatus.isRunning]
  induction steps generalizing choices with
  | zero => rfl
  | succ steps inductionHypothesis => simpa [execute, stepUnchanged] using inductionHypothesis (choices := choices.drop 1)

theorem step_reads_monotone (program : Program) (state : MachineState) (access : Access) {undefinedFlags : FlagValues}
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
      | not source | mov destination source | movzx destination source | movsxd destination source
      | cmovcc _ destination source =>
        simp only [stepOp]
        split
        · cases source <;> simp_all [next, MachineState.recordRead, MachineState.write]
        · exact recorded
      | _ =>
        simp_all [stepOp, next, MachineState.write] <;> split <;> simp_all
    · exact recorded
  · exact recorded

theorem execute_reads_monotone (program : Program) (state : MachineState) (steps : Nat) (access : Access) {choices : FlagChoices}
    (recorded : access ∈ state.readHistory) : access ∈ (execute program steps state choices).readHistory := by
  induction steps generalizing state choices with
  | zero => exact recorded
  | succ steps inductionHypothesis =>
    exact inductionHypothesis (step program state (choices 0)) (step_reads_monotone program state access recorded)

end Rivet
