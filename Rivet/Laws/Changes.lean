module
public import Rivet.Interpreter.Machine
-- What a block may change, and what it means for one state to be another except for that.
@[expose] public section
namespace Rivet

-- Registers, and intervals `[low, high)` of address values.
structure Changes where
  registers : List Reg := []
  memory : List (Nat × Nat) := []

-- What writing an operand changes: its whole 64-bit register, or the bytes it stores.
def Operand.changes (operand : Operand) (state : MachineState) : Changes :=
  match operand with
  | .reg8 register | .reg16 register | .reg32 register => { registers := [register.parent] }
  | .reg64 register => { registers := [register] }
  | .memory width address =>
    let base := (address.evaluate state.registers).toNat
    { memory := [(base, base + width.bytes)] }
  | .immediate _ => {}

def Changes.Misses (c : Changes) (low high : Nat) : Prop :=
  ∀ range ∈ c.memory, high ≤ range.1 ∨ range.2 ≤ low

-- Closes a goal that, with every value read back to the block's start, is a hypothesis or has two
-- equal sides. Rivet's own: `Block.done` and `rivet_call` use it, and it starts no arithmetic.
syntax (name := rivetKnown) "rivet_known" : tactic

-- `rivet_known`, then `rivet_arith` on each part left: your arithmetic, on your goal.
syntax (name := rivetClose) "rivet_close" : tactic

-- `t` is `s` except for `c`. Flags, vector registers and the status are not compared.
structure MachineState.Except (t s : MachineState) (c : Changes) : Prop where
  sameRegisters : ∀ register, register ∉ c.registers → t.registers register = s.registers register
  sameMemory : ∀ (address : BitVec 64) (size : Nat), c.Misses address.toNat (address.toNat + size) →
    address.toNat + size ≤ 2^64 → readBytes t.memory address size = readBytes s.memory address size

namespace MachineState.Except

theorem refl {s : MachineState} {c : Changes} : s.Except s c := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

end MachineState.Except

end Rivet
