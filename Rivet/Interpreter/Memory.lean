module
public import Rivet.Interpreter.Syntax
-- Memory, byte encodings, permission checks, and the image a run executes.
@[expose] public section
namespace Rivet

/-- The bytes of the 64-bit address space. Permissions are not part of memory:
they never change during execution, so they belong to the `Image`. -/
abbrev Memory := BitVec 64 → Fin 256

/-! A range of memory is a pair of addresses `[start, stop)`: the addresses `x`
with `start ≤ x ∧ x < stop`, compared unsigned. A range with `start ≤ stop` does
not wrap. Side conditions in these terms close by `bv_omega`. -/

/-- Every address in `[start, stop)` takes its byte from `bytes`; the rest keep
theirs. Instructions check permissions before storing. -/
def Memory.storeBytes (memory : Memory) (start stop : BitVec 64) (bytes : Memory) : Memory :=
  fun address => if start ≤ address ∧ address < stop then bytes address else memory address

/-- The little-endian bytes of a value of any width, laid out from `address`:
byte `i` of the value is at `address + i`. Scalar and vector stores write these. -/
def littleEndianAt (value : BitVec n) (address : BitVec 64) : Memory :=
  fun other => ⟨(value.toNat / 256^(other - address).toNat) % 256, Nat.mod_lt _ (by decide)⟩

/-- Read `size` little-endian bytes starting at `address`, for scalar, vector, and
return-address reads. This raw read does not check permissions. -/
def readBytes (memory : Memory) (address : BitVec 64) (size : Nat) : BitVec (8 * size) :=
  BitVec.ofNat (8 * size) ((List.range size).foldr
    (fun offset value => (memory (address + BitVec.ofNat 64 offset)).val + 256 * value) 0)

/-- An access to `[start, stop)` must not wrap, and needs permission at every address.
Closed: reason about it through `permits_iff`, never by computation. -/
@[no_expose, irreducible] def permits (permission : BitVec 64 → Bool) (start stop : BitVec 64) : Bool :=
  start ≤ stop && (List.range (stop - start).toNat).all (fun offset => permission (start + BitVec.ofNat 64 offset))

/-! ## The image -/

/-- Addresses `[start, stop)` and what the program may do with them. A region
carries no bytes: what memory holds there is a fact about memory. -/
structure Region where
  start : BitVec 64
  stop : BitVec 64
  readable : Bool
  writable : Bool

/-- What the loader fixes for a run: the code, and the regions of the address space
with their permissions. Neither changes during execution; only memory's bytes do. -/
structure Image where
  program : Program
  regions : List Region

/-! A permission is a fact about regions. For an image whose regions are listed,
`simp [Image.writable]` (with the image's definition) turns `image.writable a`
into "`a` lies in one of the writable regions", a disjunction of bounds that
`bv_omega` decides from facts in context; `permits_iff` does the same for a range. -/

/-- An address is readable when some region containing it is readable. -/
def Image.readable (image : Image) (address : BitVec 64) : Bool :=
  image.regions.any fun region => region.readable && region.start ≤ address && address < region.stop

/-- An address is writable when some region containing it is writable. -/
def Image.writable (image : Image) (address : BitVec 64) : Bool :=
  image.regions.any fun region => region.writable && region.start ≤ address && address < region.stop

end Rivet
