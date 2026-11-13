module
public import Rivet.Interpreter.Machine
public import Rivet.Laws.Memory
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

-- Proves a goal about a change: `t.Except s c` from what the steps and nested blocks since `s`
-- recorded, a register outside a change, and a range that misses one.
syntax (name := rivetChanges) "rivet_changes" : tactic

-- `t` is `s` except for `c`. Flags, vector registers and the status are not compared.
structure MachineState.Except (t s : MachineState) (c : Changes) : Prop where
  sameRegisters : ∀ register, register ∉ c.registers → t.registers register = s.registers register
  sameMemory : ∀ address : BitVec 64, c.Misses address.toNat (address.toNat + 1) →
    t.memory address = s.memory address

namespace MachineState.Except

theorem refl {s : MachineState} {c : Changes} : s.Except s c := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem registers {t s : MachineState} {c : Changes} (same : t.Except s c) (register : Reg)
    (out : register ∉ c.registers := by rivet_changes) : t.registers register = s.registers register :=
  same.sameRegisters register out

theorem readBytes {t s : MachineState} {c : Changes} (same : t.Except s c) (address : BitVec 64) (size : Nat)
    (away : c.Misses address.toNat (address.toNat + size) := by rivet_changes)
    (fits : address.toNat + size ≤ 2^64 := by rivet_arith) :
    Rivet.readBytes t.memory address size = Rivet.readBytes s.memory address size :=
  readBytes_congr (fits := fits) fun other _ _ => same.sameMemory other fun range inside => by
    have := away range inside
    omega

end MachineState.Except

end Rivet
