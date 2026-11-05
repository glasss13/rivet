import Verification.Imported
namespace Verification
open Imported
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

def byteSum (m : Nat → Fin 256) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (m a).val + byteSum m (a+1) n

def bufferReads (a : Nat) : Nat → List Access
  | 0 => []
  | n+1 => ⟨a,1⟩ :: bufferReads (a+1) n

theorem sum_bound (m : Nat → Fin 256) (a n : Nat) : byteSum m a n ≤ n*255 := by
  induction n generalizing a with
  | zero => simp [byteSum]
  | succ n ih =>
    have := ih (a+1)
    have := (m a).isLt
    simp only [byteSum]
    omega

def Good (s : State) (a n : Nat) : Prop :=
  a+n < word ∧ ∀ i, i < n → s.readable (a+i) = true

def Stack (s : State) : Prop :=
  s.regs .rsp + 8 ≤ word ∧ (List.range 8).all (fun i => s.readable (s.regs .rsp+i)) = true

def Result (s t : State) (a n acc : Nat) : Prop :=
  t.status = .returned (read64 s.mem (s.regs .rsp)) ∧
  t.regs .rax = acc + byteSum s.mem a n ∧
  t.regs .rsp = (s.regs .rsp + 8) % word ∧
  t.reads = s.reads ++ bufferReads a n ++ [⟨s.regs .rsp,8⟩]

 theorem loop_correct (n : Nat) (s : State) (a acc : Nat)
    (hrun : s.status = .running)
    (hpc : s.pc = if n = 0 then 8 else 3)
    (hc : s.regs .rsi = n) (hp : s.regs .rdi = a) (ha : s.regs .rax = acc)
    (hg : Good s a n) (hs : Stack s) (hb : acc + n*255 < word) :
    Result s (run program (5*n+1) s) a n acc := by
  induction n generalizing s a acc with
  | zero =>
    obtain ⟨hstack, hread⟩ := hs
    simp only [Result, byteSum, bufferReads, Nat.add_zero, List.append_nil]
    have hsp : s.regs .rsp + 8 ≤ word := by omega
    simp [run, step, program, hrun, hpc, stepOp, hsp, hread, put,
      ha]
  | succ n ih =>
    have hpc' : s.pc = 3 := by simpa using hpc
    have hmem : s.readable a = true := by simpa using hg.2 0 (by omega)
    have hab : a < word := by have := hg.1; omega
    have hbyte := (s.mem a).isLt
    have hsum : acc + (s.mem a).val < word := by omega
    have hptr : a+1 < word := by have := hg.1; omega
    have hn : n < word := by omega
    have hdec : (n+1+word-1)%word = n := by
      have he : n+1+word-1 = n+word := by omega
      rw [he, Nat.add_mod]; simp [Nat.mod_eq_of_lt hn]
    let t := step program (step program (step program (step program (step program s))))
    have ht : t = { s with
        regs := fun r => if r = .rsi then n else if r = .rdi then a+1 else
          if r = .rax then acc+(s.mem a).val else if r = .rdx then (s.mem a).val else s.regs r
        zf := n == 0
        pc := if n = 0 then 8 else 3
        reads := s.reads ++ [⟨a,1⟩] } := by
      have hv : (s.mem a).val < word := by unfold word; omega
      simp [t, step, program, hrun, hpc', stepOp, next, put, hp, hc, ha,
        hab, hmem, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hsum,
        Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hn]
    have trun : t.status = .running := by simp [ht, hrun]
    have tpc : t.pc = if n = 0 then 8 else 3 := by simp [ht]
    have tc : t.regs .rsi = n := by simp [ht]
    have tp : t.regs .rdi = a+1 := by simp [ht]
    have ta : t.regs .rax = acc+(s.mem a).val := by simp [ht]
    have tg : Good t (a+1) n := by
      constructor
      · have := hg.1; omega
      · intro i hi
        simpa [ht, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg.2 (i+1) (by omega)
    have ts : Stack t := by simpa [Stack, ht] using hs
    have tb : acc+(s.mem a).val+n*255 < word := by omega
    have hi := ih t (a+1) (acc+(s.mem a).val) trun tpc tc tp ta tg ts tb
    have hf : 5*(n+1)+1 = (5*n+1)+5 := by omega
    rw [hf]
    change Result s (run program (5*n+1) t) a (n+1) acc
    simpa [Result, ht, byteSum, bufferReads, Nat.add_assoc, List.append_assoc] using hi

-- Preconditions are stated on the actual entry state, with arbitrary other registers/flags.
def Preconditions (s : State) (a n : Nat) : Prop :=
  s.status = .running ∧ s.pc = 0 ∧ s.regs .rdi = a ∧ s.regs .rsi = n ∧
  n ≤ 4096 ∧ Good s a n ∧ Stack s ∧
  (∀ r, s.regs r < word) ∧
  (∀ i j, i < n → j < 8 → a+i ≠ s.regs .rsp+j)

theorem sum_bytes_correct (s : State) (a n : Nat) (h : Preconditions s a n) :
    Result s (run program (5*n+4) s) a n 0 := by
  obtain ⟨hrun,hpc,hp,hc,hn,hg,hs,hw,hd⟩ := h
  let t := step program (step program (step program s))
  have ht : t = { s with regs := fun r => if r = .rax then 0 else s.regs r, zf := n == 0, pc := if n = 0 then 8 else 3 } := by
    simp [t, step, program, hrun, hpc, stepOp, next, put, hc]
  have hb : 0+n*255 < word := by unfold word; omega
  have hi := loop_correct n t a 0 (by simp [ht, hrun]) (by simp [ht])
    (by simp [ht, hc]) (by simp [ht, hp]) (by simp [ht])
    (by simpa [Good, ht] using hg) (by simpa [Stack, ht] using hs) hb
  change Result s (run program (5*n+1+3) s) a n 0
  change Result s (run program (5*n+1) t) a n 0
  simpa [Result, ht] using hi

#print axioms Imported.certificate
#print axioms loop_correct
#print axioms sum_bytes_correct
end Verification
