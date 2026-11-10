module
public import Rivet.Interpreter.Syntax
-- Memory, byte encodings, permission checks, and the image a run executes.
@[expose] public section
namespace Rivet

abbrev Memory := BitVec 64 → Fin 256

def Memory.storeBytes (memory : Memory) (base length : BitVec 64) (bytes : Memory) : Memory :=
  fun address => if address - base < length then bytes address else memory address

@[no_expose, irreducible] def littleEndianAt (value : BitVec n) (address : BitVec 64) : Memory :=
  fun other => ⟨(value.toNat / 256^(other - address).toNat) % 256, Nat.mod_lt _ (by decide)⟩

@[no_expose, irreducible] def readBytes (memory : Memory) (address : BitVec 64) (size : Nat) : BitVec (8 * size) :=
  BitVec.ofNat (8 * size) ((List.range size).foldr
    (fun offset value => (memory (address + BitVec.ofNat 64 offset)).val + 256 * value) 0)

@[no_expose, irreducible] def permits (permission : BitVec 64 → Bool) (base length : BitVec 64) : Bool :=
  base ≤ base + length &&
    (List.range length.toNat).all (fun offset => permission (base + BitVec.ofNat 64 offset))

structure Region where
  base : BitVec 64
  length : BitVec 64
  readable : Bool
  writable : Bool

structure Image where
  program : Program
  regions : List Region

def Image.readable (image : Image) (address : BitVec 64) : Bool :=
  image.regions.any fun region => region.readable && address - region.base < region.length

def Image.writable (image : Image) (address : BitVec 64) : Bool :=
  image.regions.any fun region => region.writable && address - region.base < region.length

end Rivet
