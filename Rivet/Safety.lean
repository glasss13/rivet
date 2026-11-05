module
public import Rivet.Model
@[expose] public section
namespace Rivet

def CalleeSaved (r : Reg) : Prop :=
  r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15

theorem op_preserves (op : Op) (s : MachineState) (r : Reg) (h : modifies op r = false) :
    (stepOp op s).registers r = s.registers r := by
  cases op <;> simp_all [modifies, stepOp, next, put, Ne.symm] <;> split <;> simp_all [Ne.symm]

theorem step_preserves (p : Program) (s : MachineState) (r : Reg)
    (h : ∀ i ∈ p, modifies i.op r = false) : (step p s).registers r = s.registers r := by
  unfold step
  split
  · split
    · rename_i i he
      apply op_preserves
      exact h i (List.mem_of_getElem? he)
    · rfl
  · rfl

/-- A register untouched by every instruction is preserved for any amount of fuel. -/
theorem run_preserves (p : Program) (n : Nat) (s : MachineState) (r : Reg)
    (unchanged : ∀ i ∈ p, modifies i.op r = false) :
    (run p n s).registers r = s.registers r := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run, ih, step_preserves p s r unchanged]

theorem run_stopped (p : Program) (n : Nat) (s : MachineState) (h : s.status.isRunning = false) :
    run p n s = s := by
  have hs : step p s = s := by
    cases status : s.status <;> simp_all [step, ExecutionStatus.isRunning]
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, hs] using ih

theorem step_reads_monotone (p : Program) (s : MachineState) (e : Access)
    (h : e ∈ s.readHistory) : e ∈ (step p s).readHistory := by
  unfold step
  split
  · split
    · rename_i i hi
      cases i.op <;> simp_all [stepOp, next, put] <;> split <;> simp_all
    · exact h
  · exact h

theorem run_reads_monotone (p : Program) (s : MachineState) (n : Nat) (e : Access)
    (h : e ∈ s.readHistory) : e ∈ (run p n s).readHistory := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih (step p s) (step_reads_monotone p s e h)

end Rivet
