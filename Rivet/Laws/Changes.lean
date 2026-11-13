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

def Changes.Within (smaller larger : Changes) : Prop :=
  (∀ register ∈ smaller.registers, register ∈ larger.registers) ∧
  ∀ range ∈ smaller.memory, ∃ cover ∈ larger.memory, cover.1 ≤ range.1 ∧ range.2 ≤ cover.2

-- Proves a goal about a change: `t.Except s c` from what the steps since `s` recorded, a register
-- outside a change, a range that misses one, and one change within another.
syntax (name := rivetChanges) "rivet_changes" : tactic

-- `t` is `s` except for `c`. Flags, vector registers and the status are not compared.
structure MachineState.Except (t s : MachineState) (c : Changes) : Prop where
  sameRegisters : ∀ register, register ∉ c.registers → t.registers register = s.registers register
  sameMemory : ∀ address : BitVec 64, c.Misses address.toNat (address.toNat + 1) →
    t.memory address = s.memory address

namespace MachineState.Except

theorem refl {s : MachineState} {c : Changes} : s.Except s c := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans {u t s : MachineState} {c : Changes} (later : u.Except t c) (earlier : t.Except s c) :
    u.Except s c :=
  ⟨fun register out => (later.sameRegisters register out).trans (earlier.sameRegisters register out),
    fun address away => (later.sameMemory address away).trans (earlier.sameMemory address away)⟩

theorem mono {t s : MachineState} {c larger : Changes} (same : t.Except s c)
    (within : c.Within larger := by rivet_changes) : t.Except s larger := by
  refine ⟨fun register out => same.sameRegisters register fun inside => out (within.1 register inside),
    fun address away => same.sameMemory address fun range inside => ?_⟩
  obtain ⟨cover, member, low, high⟩ := within.2 range inside
  have := away cover member
  omega

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
