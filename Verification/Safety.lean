import Verification.Proof
namespace Verification
open Imported

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

theorem callee_saved (s : State) (n : Nat) (r : Reg) (h : CalleeSaved r) :
    (run program n s).regs r = s.regs r := by
  have hp : ∀ i ∈ program, modifies i.op r = false := by
    intro i hi
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi|hi|hi|hi|hi|hi|hi|hi|hi <;> subst i <;>
      rcases h with h|h|h|h|h|h <;> subst r <;> decide
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run, ih, step_preserves program s r hp]

theorem buffer_read_member (a n : Nat) (e : Access) (h : e ∈ bufferReads a n) :
    e.size = 1 ∧ a ≤ e.address ∧ e.address < a+n := by
  induction n generalizing a with
  | zero => simp [bufferReads] at h
  | succ n ih =>
    simp only [bufferReads, List.mem_cons] at h
    rcases h with h | h
    · subst e; simp
    · have := ih (a+1) h; constructor; exact this.1; omega

def Permitted (s : State) (a n : Nat) (e : Access) : Prop :=
  (e.size = 1 ∧ a ≤ e.address ∧ e.address < a+n) ∨
  (e.address = s.regs .rsp ∧ e.size = 8)

theorem access_safety (s : State) (a n : Nat) (h : Preconditions s a n)
    (e : Access) (he : e ∈ (run program (5*n+4) s).reads) :
    e ∈ s.reads ∨ Permitted s a n e := by
  have hr := (sum_bytes_correct s a n h).2.2.2
  rw [hr] at he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with (he|he)|he
  · exact Or.inl he
  · exact Or.inr (Or.inl (buffer_read_member a n e he))
  · subst e; exact Or.inr (Or.inr ⟨rfl,rfl⟩)

theorem run_add (p : Program) (n m : Nat) (s : State) :
    run p (n+m) s = run p m (run p n s) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => simpa [Nat.succ_add, run] using ih (step p s)

theorem run_stopped (p : Program) (n : Nat) (s : State) (h : s.status ≠ .running) :
    run p n s = s := by
  have hs : step p s = s := by unfold step; split <;> simp_all
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, hs] using ih

theorem never_faults (s : State) (a n k : Nat) (h : Preconditions s a n) :
    (run program k s).status ≠ .fault := by
  have hr := (sum_bytes_correct s a n h).1
  intro hf
  by_cases hk : k ≤ 5*n+4
  · have he : 5*n+4 = k+(5*n+4-k) := by omega
    rw [he, run_add, run_stopped] at hr
    · rw [hf] at hr; contradiction
    · rw [hf]; decide
  · have he : k = (5*n+4)+(k-(5*n+4)) := by omega
    rw [he, run_add, run_stopped] at hf
    · rw [hr] at hf; contradiction
    · rw [hr]; simp

theorem stays_returned (s : State) (a n extra : Nat) (h : Preconditions s a n) :
    run program (5*n+4+extra) s = run program (5*n+4) s := by
  rw [run_add, run_stopped]
  rw [(sum_bytes_correct s a n h).1]
  simp


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

theorem all_accesses_safe (s : State) (a n k : Nat) (h : Preconditions s a n)
    (e : Access) (he : e ∈ (run program k s).reads) :
    e ∈ s.reads ∨ Permitted s a n e := by
  apply access_safety s a n h e
  by_cases hk : k ≤ 5*n+4
  · have heq : 5*n+4 = k+(5*n+4-k) := by omega
    rw [heq, run_add]
    exact run_reads_monotone program _ _ e he
  · have heq : k = 5*n+4+(k-(5*n+4)) := by omega
    rw [heq, stays_returned s a n _ h] at he
    exact he

theorem empty_reads_only_stack (s : State) (a : Nat) (h : Preconditions s a 0) :
    (run program 4 s).reads = s.reads ++ [⟨s.regs .rsp,8⟩] := by
  simpa [bufferReads] using (sum_bytes_correct s a 0 h).2.2.2

#print axioms all_accesses_safe
#print axioms empty_reads_only_stack

#print axioms access_safety
#print axioms callee_saved
#print axioms run_memory
#print axioms never_faults
#print axioms stays_returned
end Verification
