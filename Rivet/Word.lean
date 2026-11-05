module
public import Rivet.Safety
@[expose] public section
namespace Rivet
set_option maxRecDepth 4000
-- Registers use the canonical natural-number encoding of a 64-bit word.
-- The invariant is explicit, and every supported transition preserves it.
def Registers64 (state : MachineState) : Prop := ∀ register, state.registers register < 2^64

theorem put_registers64 (state : MachineState) (register : Reg) (value : Nat) (registersFit : Registers64 state) :
    Registers64 (put state register value) := by
  intro otherRegister
  simp only [put]
  split
  · exact Nat.mod_lt _ (by decide)
  · exact registersFit otherRegister

theorem stepOp_registers64 (operation : Op) (state : MachineState) (registersFit : Registers64 state) :
    Registers64 (stepOp operation state) := by
  have wrappedValueFits : ∀ value : Nat, value % word < 2^64 := fun value => Nat.mod_lt value (by decide)
  cases operation <;> simp_all [Registers64, stepOp, next, put, -Reg32.parent] <;>
    intros <;> split <;> simp_all [-Reg32.parent] <;> split <;> simp_all [-Reg32.parent]

theorem step_registers64 (program : Program) (state : MachineState) (registersFit : Registers64 state) :
    Registers64 (step program state) := by
  unfold step
  split
  · split
    · exact stepOp_registers64 _ state registersFit
    · exact registersFit
  · exact registersFit

theorem run_registers64 (program : Program) (steps : Nat) (state : MachineState) (registersFit : Registers64 state) :
    Registers64 (run program steps state) := by
  induction steps generalizing state with
  | zero => exact registersFit
  | succ steps inductionHypothesis => exact inductionHypothesis _ (step_registers64 program state registersFit)

end Rivet
