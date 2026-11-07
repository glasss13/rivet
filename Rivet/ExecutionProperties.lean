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

theorem op_preserves (operation : Op) (state : MachineState) (register : Reg) (unchanged : modifies operation register = false) :
    (stepOp operation state).registers register = state.registers register := by
  cases operation with
  | mov destination source =>
    simp only [stepOp]
    split
    · cases destination <;>
        simp_all [modifies, Operand.register, next, MachineState.writeOperand, MachineState.write, Ne.symm]
    · rfl
  | _ =>
    simp_all [modifies, stepOp, next, MachineState.write, Ne.symm] <;>
      split <;> simp_all [Ne.symm]

theorem step_preserves (program : Program) (state : MachineState) (register : Reg)
    (unchanged : ∀ instruction ∈ program, modifies instruction.op register = false) :
    (step program state).registers register = state.registers register := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      apply op_preserves
      exact unchanged instruction (List.mem_of_getElem? instructionAtIndex)
    · rfl
  · rfl

/-- A register untouched by every instruction is preserved for any amount of fuel. -/
theorem execute_preserves (program : Program) (steps : Nat) (state : MachineState) (register : Reg)
    (unchanged : ∀ instruction ∈ program, modifies instruction.op register = false) :
    (execute program steps state).registers register = state.registers register := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis => rw [execute, inductionHypothesis, step_preserves program state register unchanged]

theorem execute_stopped (program : Program) (steps : Nat) (state : MachineState) (stopped : state.status.isRunning = false) :
    execute program steps state = state := by
  have stepUnchanged : step program state = state := by
    cases status : state.status <;> simp_all [step, ExecutionStatus.isRunning]
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis => simpa [execute, stepUnchanged] using inductionHypothesis

theorem step_reads_monotone (program : Program) (state : MachineState) (access : Access)
    (recorded : access ∈ state.readHistory) : access ∈ (step program state).readHistory := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      cases instruction.op with
      | mov destination source =>
        simp only [stepOp]
        split
        · cases source <;> simp_all [next, MachineState.recordRead]
        · exact recorded
      | _ =>
        simp_all [stepOp, next, MachineState.write] <;> split <;> simp_all
    · exact recorded
  · exact recorded

theorem execute_reads_monotone (program : Program) (state : MachineState) (steps : Nat) (access : Access)
    (recorded : access ∈ state.readHistory) : access ∈ (execute program steps state).readHistory := by
  induction steps generalizing state with
  | zero => exact recorded
  | succ steps inductionHypothesis =>
    exact inductionHypothesis (step program state) (step_reads_monotone program state access recorded)

end Rivet
