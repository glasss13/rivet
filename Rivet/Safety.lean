module
public import Rivet.Model
@[expose] public section
namespace Rivet

def CalleeSaved (register : Reg) : Prop :=
  register = .rbx ∨ register = .rbp ∨ register = .r12 ∨ register = .r13 ∨ register = .r14 ∨ register = .r15

theorem op_preserves (operation : Op) (state : MachineState) (register : Reg) (unchanged : modifies operation register = false) :
    (stepOp operation state).registers register = state.registers register := by
  cases operation <;> simp_all [modifies, stepOp, next, put, Ne.symm] <;> split <;> simp_all [Ne.symm]

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
theorem run_preserves (program : Program) (steps : Nat) (state : MachineState) (register : Reg)
    (unchanged : ∀ instruction ∈ program, modifies instruction.op register = false) :
    (run program steps state).registers register = state.registers register := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis => rw [run, inductionHypothesis, step_preserves program state register unchanged]

theorem run_stopped (program : Program) (steps : Nat) (state : MachineState) (stopped : state.status.isRunning = false) :
    run program steps state = state := by
  have stepUnchanged : step program state = state := by
    cases status : state.status <;> simp_all [step, ExecutionStatus.isRunning]
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis => simpa [run, stepUnchanged] using inductionHypothesis

theorem step_reads_monotone (program : Program) (state : MachineState) (access : Access)
    (recorded : access ∈ state.readHistory) : access ∈ (step program state).readHistory := by
  unfold step
  split
  · split
    · rename_i instruction instructionAtIndex
      cases instruction.op <;> simp_all [stepOp, next, put] <;> split <;> simp_all
    · exact recorded
  · exact recorded

theorem run_reads_monotone (program : Program) (state : MachineState) (steps : Nat) (access : Access)
    (recorded : access ∈ state.readHistory) : access ∈ (run program steps state).readHistory := by
  induction steps generalizing state with
  | zero => exact recorded
  | succ steps inductionHypothesis =>
    exact inductionHypothesis (step program state) (step_reads_monotone program state access recorded)

end Rivet
