module
public import Rivet.Interpreter.Machine
-- What a block may change, and what it means for one state to be another except for that.
@[expose] public section
namespace Rivet

-- Registers, vector registers, intervals `[low, high)` of address values, and whether what the kernel
-- keeps changes.
structure Changes where
  registers : List Reg := []
  xmm : List Xmm := []
  memory : List (Nat × Nat) := []
  kernel : Bool := false
  unrestricted : Bool := false

abbrev Changes.all : Changes := { unrestricted := true }

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
syntax (name := Internal.rivetKnown) "rivet_known" : tactic

-- `t` is `s` except for `c`. Flags and the status are not compared.
structure MachineState.Except (t s : MachineState) (c : Changes) : Prop where
  sameRegisters : c.unrestricted = false → ∀ register, register ∉ c.registers → t.registers register = s.registers register
  sameXmm : c.unrestricted = false → ∀ register, register ∉ c.xmm → t.xmmRegisters register = s.xmmRegisters register
  sameMemory : c.unrestricted = false → ∀ (address : BitVec 64) (size : Nat), c.Misses address.toNat (address.toNat + size) →
    address.toNat + size ≤ 2^64 → readBytes t.memory address size = readBytes s.memory address size
  sameKernel : c.unrestricted = false → c.kernel = false → t.kernel = s.kernel

-- Laws Rivet's tactics build proofs with. Proofs never name them.
namespace Internal

theorem MachineState.Except.refl {s : MachineState} {c : Changes} : s.Except s c :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem MachineState.Except.all {t s : MachineState} {c : Changes}
    (all : c.unrestricted = true := by rfl) : t.Except s c := by
  constructor <;> intro limited <;> simp [all] at limited

-- The vector registers outside `c`, kept from `s` to `t`: by a step that wrote none, and by a nested
-- block whose change lists only vector registers `c` lists.
def Changes.SameXmm (c : Changes) (t s : MachineState) : Prop :=
  ∀ register, register ∉ c.xmm → t.xmmRegisters register = s.xmmRegisters register

namespace Changes.SameXmm

theorem refl {c : Changes} {s : MachineState} : Changes.SameXmm c s s := fun _ _ => rfl

theorem of_eq {c : Changes} {t u s : MachineState} (same : t.xmmRegisters = u.xmmRegisters)
    (rest : Changes.SameXmm c u s) : Changes.SameXmm c t s :=
  fun register out => same ▸ rest register out

theorem nested {c inner : Changes} {t u s : MachineState} (kept : t.Except u inner)
    (limited : inner.unrestricted = false) (within : ∀ register ∈ inner.xmm, register ∈ c.xmm) (rest : Changes.SameXmm c u s) : Changes.SameXmm c t s :=
  fun register out => (kept.sameXmm limited register fun listed => out (within register listed)).trans (rest register out)

end Changes.SameXmm

end Internal

end Rivet
