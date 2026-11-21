module
public import Rivet.Interpreter.Syntax
-- Memory, byte encodings, permission checks, and what the kernel keeps for the process.
@[expose] public section
namespace Rivet

abbrev Memory := BitVec 64 → Fin 256

def Memory.storeBytes (memory : Memory) (base : BitVec 64) (length : Nat) (bytes : Memory) : Memory :=
  fun address =>
    if base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + length then bytes address else memory address

@[no_expose, irreducible] def littleEndianAt (value : BitVec n) (address : BitVec 64) : Memory :=
  fun other => ⟨(value.toNat / 256^(other - address).toNat) % 256, Nat.mod_lt _ (by decide)⟩

@[no_expose, irreducible] def readBytes (memory : Memory) (address : BitVec 64) (size : Nat) : BitVec (8 * size) :=
  BitVec.ofNat (8 * size) ((List.range size).foldr
    (fun offset value => (memory (address + BitVec.ofNat 64 offset)).val + 256 * value) 0)

-- An access that would wrap past 2^64 is never permitted.
@[no_expose, irreducible] def permits (permission : BitVec 64 → Bool) (base : BitVec 64) (length : Nat) : Bool :=
  base.toNat + length ≤ 2^64 &&
    (List.range length).all (fun offset => permission (base + BitVec.ofNat 64 offset))

-- A region does not wrap: a mapping that crossed 2^64 would be two regions. Made only by
-- `Region.root` and `Region.part`.
structure Region where
  private mk ::
  base : Nat
  length : Nat
  readable : Bool
  writable : Bool
  fits : base + length ≤ 2^64 := by decide

def Region.Contains (region : Region) (address : BitVec 64) : Prop :=
  region.base ≤ address.toNat ∧ address.toNat < region.base + region.length

instance (region : Region) (address : BitVec 64) : Decidable (region.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- `length` bytes from `start`, with their permissions. Closed, as `Region.part` is: what it is, is
-- only its laws (`Region.root_base` and the others), so nothing computes a region's base.
@[no_expose] def Region.root (start : BitVec 64) (length : Nat) (readable writable : Bool)
    (fits : start.toNat + length ≤ 2^64 := by decide) : Region :=
  { base := start.toNat, length, readable, writable, fits }

-- `length` bytes of the region from `offset`, with its permissions.
@[no_expose] def Region.part (r : Region) (offset length : Nat)
    (inside : offset + length ≤ r.length := by simp only [rivet]) : Region :=
  { base := r.base + offset, length, readable := r.readable, writable := r.writable,
    fits := by have := r.fits; omega }

-- What the kernel keeps for the process: the addresses it has mapped, and which of them the process
-- may read and write.
structure Kernel where
  mapped : BitVec 64 → Bool
  readable : BitVec 64 → Bool
  writable : BitVec 64 → Bool

-- The kernel that has mapped exactly these regions, each with its permissions.
def Kernel.ofRegions (regions : List Region) : Kernel where
  mapped address := regions.any fun region => decide (region.Contains address)
  readable address := regions.any fun region => region.readable && decide (region.Contains address)
  writable address := regions.any fun region => region.writable && decide (region.Contains address)

end Rivet
