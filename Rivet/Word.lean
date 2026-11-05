module
public import Rivet.Safety
@[expose] public section
namespace Rivet
set_option maxRecDepth 4000
-- Registers use the canonical natural-number encoding of a 64-bit word.
-- The invariant is explicit, and every supported transition preserves it.
def Registers64 (s : State) : Prop := ∀ r, s.regs r < 2^64

theorem put_registers64 (s : State) (r : Reg) (v : Nat) (h : Registers64 s) :
    Registers64 (put s r v) := by
  intro q
  simp only [put]
  split
  · exact Nat.mod_lt _ (by decide)
  · exact h q

theorem stepOp_registers64 (op : Op) (s : State) (h : Registers64 s) :
    Registers64 (stepOp op s) := by
  have hm : ∀ v : Nat, v % word < 2^64 := fun v => Nat.mod_lt v (by decide)
  cases op <;> simp_all [Registers64, stepOp, next, put, -Reg32.parent] <;>
    intros <;> split <;> simp_all [-Reg32.parent] <;> split <;> simp_all [-Reg32.parent]

theorem step_registers64 (p : Program) (s : State) (h : Registers64 s) :
    Registers64 (step p s) := by
  unfold step
  split
  · split
    · exact stepOp_registers64 _ s h
    · exact h
  · exact h

theorem run_registers64 (p : Program) (n : Nat) (s : State) (h : Registers64 s) :
    Registers64 (run p n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (step_registers64 p s h)

end Rivet
