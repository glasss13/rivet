module
public import Verification.Model
@[expose] public section
namespace Verification

def CalleeSaved (r : Reg) : Prop :=
  r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15

def modifies : Op → Reg → Bool
  | .xor d _, r | .movzx d _, r => d.parent == r
  | .add d _, r | .inc d, r | .dec d, r => d == r
  | .ret, r => r == .rsp
  | _, _ => false

theorem op_preserves (op : Op) (s : State) (r : Reg) (h : modifies op r = false) :
    (stepOp op s).regs r = s.regs r := by
  cases op <;> simp_all [modifies, stepOp, next, put, Ne.symm] <;> split <;> simp_all [Ne.symm]

theorem step_preserves (p : Program) (s : State) (r : Reg)
    (h : ∀ i ∈ p, modifies i.op r = false) : (step p s).regs r = s.regs r := by
  unfold step
  split
  · split
    · rename_i i he
      apply op_preserves
      exact h i (List.mem_of_getElem? he)
    · rfl
  · rfl

theorem run_stopped (p : Program) (n : Nat) (s : State) (h : s.status ≠ .running) :
    run p n s = s := by
  have hs : step p s = s := by unfold step; split <;> simp_all
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, hs] using ih

theorem step_reads_monotone (p : Program) (s : State) (e : Access)
    (h : e ∈ s.reads) : e ∈ (step p s).reads := by
  unfold step
  split
  · split
    · rename_i i hi
      cases i.op <;> simp_all [stepOp, next, put] <;> split <;> simp_all
    · exact h
  · exact h

theorem run_reads_monotone (p : Program) (s : State) (n : Nat) (e : Access)
    (h : e ∈ s.reads) : e ∈ (run p n s).reads := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih (step p s) (step_reads_monotone p s e h)

end Verification
