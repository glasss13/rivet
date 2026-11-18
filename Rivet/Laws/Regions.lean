module
public import Rivet.Laws.Memory
public import Rivet.Laws.Changes
public import Rivet.Laws.SimpSet
import all Rivet.Interpreter.Memory
-- Memory as named regions. A region names a range of addresses. A pointer is placed in a region by
-- `Has`, two regions are `Apart`, and two memories are the `Same` on a region.
@[expose] public section
namespace Rivet

-- `size` bytes at `pointer` lie in the region.
structure Region.Has (r : Region) (pointer : BitVec 64) (size : Nat) : Prop where
  start : r.base ≤ pointer.toNat
  finish : pointer.toNat + size ≤ r.base + r.length

def Region.Apart (first second : Region) : Prop :=
  first.base + first.length ≤ second.base ∨ second.base + second.length ≤ first.base

-- The address `offset` bytes into the region. Closed, so that nothing computes a part's base: it is a
-- sum only by `Region.part_base`.
@[no_expose, irreducible] def Internal.Region.address (r : Region) (offset : Nat) : Nat := r.base + offset

theorem Internal.Region.address_eq (r : Region) (offset : Nat) : Region.address r offset = r.base + offset := by
  unfold Region.address; rfl

-- `length` bytes of the region from `offset`, with its permissions. A `def`: a part is a name.
def Region.part (r : Region) (offset length : Nat) (inside : offset + length ≤ r.length := by exact Nat.le_of_ble_eq_true rfl) :
    Region :=
  { base := Internal.Region.address r offset, length, readable := r.readable, writable := r.writable,
    fits := by have := r.fits; have := Internal.Region.address_eq r offset; omega }

-- A part's base as a sum, when a proof needs the number.
theorem Region.part_base (r : Region) (offset length : Nat) (inside : offset + length ≤ r.length) :
    (r.part offset length inside).base = r.base + offset := Internal.Region.address_eq r offset

@[rivet] theorem Region.part_length (r : Region) (offset length : Nat) (inside : offset + length ≤ r.length) :
    (r.part offset length inside).length = length := rfl

-- A change lists a region as its range.
abbrev Region.range (r : Region) : Nat × Nat := (r.base, r.base + r.length)

instance : Coe Region (Nat × Nat) := ⟨Region.range⟩

-- The two memories agree on every byte of the region.
def Region.Same (r : Region) (earlier later : Memory) : Prop :=
  ∀ address, r.Contains address → earlier address = later address

def Image.Reads (image : Image) (r : Region) : Prop := ∀ address, r.Contains address → image.readable address = true

def Image.Writes (image : Image) (r : Region) : Prop := ∀ address, r.Contains address → image.writable address = true

theorem Region.Has.part {r : Region} {pointer : BitVec 64} {size : Nat} (placed : r.Has pointer size)
    {inner : BitVec 64} {less : Nat} (start : pointer.toNat ≤ inner.toNat)
    (finish : inner.toNat + less ≤ pointer.toNat + size) : r.Has inner less :=
  ⟨by have := placed.start; omega, by have := placed.finish; omega⟩

-- A place that fills its region places each part of it: the part's bytes are at its offset from that
-- pointer.
theorem Region.Has.part_at {r : Region} {pointer : BitVec 64} {size : Nat} (placed : r.Has pointer size)
    (fills : r.length ≤ size) (offset length : Nat) (inside : offset + length ≤ r.length) (positive : 0 < length) :
    (r.part offset length inside).Has (pointer + BitVec.ofNat 64 offset) length := by
  have := r.fits
  have := placed.start
  have := placed.finish
  constructor <;> simp only [Region.part_base, Region.part_length] <;> bv_omega

-- A permission, from the image's own list.
theorem Image.reads_of_mem {image : Image} {r : Region} (member : r ∈ image.regions) (readable : r.readable = true) :
    image.Reads r := by
  intro address inside
  simp only [Image.readable, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨r, member, readable, inside⟩

theorem Image.writes_of_mem {image : Image} {r : Region} (member : r ∈ image.regions) (writable : r.writable = true) :
    image.Writes r := by
  intro address inside
  simp only [Image.writable, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨r, member, writable, inside⟩

-- Two parts of one region are apart when their offsets say so.
theorem Region.part_apart (r : Region) {offset length offset' length' : Nat} (inside : offset + length ≤ r.length)
    (inside' : offset' + length' ≤ r.length) (apart : offset + length ≤ offset' ∨ offset' + length' ≤ offset) :
    (r.part offset length inside).Apart (r.part offset' length' inside') := by
  simp only [Region.Apart, Region.part_base, Region.part_length]; omega

-- A read placed in the region is the same in both.
theorem Region.Same.read {r : Region} {earlier later : Memory} (same : r.Same earlier later) {pointer : BitVec 64} {size : Nat}
    (placed : r.Has pointer size) : readBytes earlier pointer size = readBytes later pointer size := by
  have := r.fits
  have := placed.start
  have := placed.finish
  exact Internal.readBytes_congr (fun other low high => same other ⟨by omega, by omega⟩) (by omega)

-- A read inside a store reads those bytes of the value stored.
theorem Region.Has.readBytes_stored {r : Region} {pointer stored : BitVec 64} {size length : Nat}
    (placed : r.Has stored length) (offset : Nat) (start : pointer.toNat = stored.toNat + offset)
    (inside : offset + size ≤ length) (memory : Memory) (value : BitVec n) :
    readBytes (memory.storeBytes stored length (littleEndianAt value stored)) pointer size =
      value.extractLsb' (8 * offset) (8 * size) := by
  have := r.fits
  have := placed.finish
  rw [Internal.Memory.readBytes_storeBytes_inside _ _ (by omega) (by omega) (by omega),
    Internal.readBytes_littleEndianAt value offset start (by omega)]

-- Laws Rivet's tactics build proofs with. Proofs never name them.
namespace Internal

theorem Region.Apart.symm {first second : Region} (apart : first.Apart second) : second.Apart first :=
  Or.symm apart

theorem Region.Has.fits {r : Region} {pointer : BitVec 64} {size : Nat} (placed : r.Has pointer size) :
    pointer.toNat + size ≤ 2^64 := by
  have := r.fits
  have := placed.finish
  omega

-- A permission for a part of a region that has it.
theorem Image.Reads.part {image : Image} {r : Region} (reads : image.Reads r) (offset length : Nat)
    (inside : offset + length ≤ r.length) : image.Reads (r.part offset length inside) := by
  intro address within
  apply reads
  simp only [Region.Contains, Region.part_base, Region.part_length] at within ⊢
  omega

theorem Image.Writes.part {image : Image} {r : Region} (writes : image.Writes r) (offset length : Nat)
    (inside : offset + length ≤ r.length) : image.Writes (r.part offset length inside) := by
  intro address within
  apply writes
  simp only [Region.Contains, Region.part_base, Region.part_length] at within ⊢
  omega

-- A part lies inside its region: it is apart from what the region is apart from.
theorem Region.Apart.part_left {r other : Region} (apart : r.Apart other) (offset length : Nat)
    (inside : offset + length ≤ r.length) : (r.part offset length inside).Apart other := by
  simp only [Region.Apart, Region.part_base, Region.part_length] at apart ⊢; omega

theorem Region.Apart.part_right {r other : Region} (apart : r.Apart other) (offset length : Nat)
    (inside : offset + length ≤ other.length) : r.Apart (other.part offset length inside) := by
  simp only [Region.Apart, Region.part_base, Region.part_length] at apart ⊢; omega

theorem Image.Reads.permits {image : Image} {r : Region} {pointer : BitVec 64} {size : Nat}
    (reads : image.Reads r) (placed : r.Has pointer size) : permits image.readable pointer size = true := by
  rw [permits_iff]
  have := r.fits
  have := placed.start
  have := placed.finish
  exact ⟨by omega, fun address low high => reads address ⟨by omega, by omega⟩⟩

theorem Image.Writes.permits {image : Image} {r : Region} {pointer : BitVec 64} {size : Nat}
    (writes : image.Writes r) (placed : r.Has pointer size) : permits image.writable pointer size = true := by
  rw [permits_iff]
  have := r.fits
  have := placed.start
  have := placed.finish
  exact ⟨by omega, fun address low high => writes address ⟨by omega, by omega⟩⟩

namespace Region.Same

theorem refl {r : Region} {memory : Memory} : r.Same memory memory := fun _ _ => rfl

theorem trans {r : Region} {first second third : Memory} (one : r.Same first second) (two : r.Same second third) :
    r.Same first third := fun address inside => (one address inside).trans (two address inside)

theorem of_eq {r : Region} {earlier middle later : Memory} (same : later = middle)
    (rest : r.Same earlier middle) : r.Same earlier later := same ▸ rest

-- A store placed in a region apart from this one.
theorem store {r other : Region} {earlier memory : Memory} {pointer : BitVec 64} {size : Nat}
    (placed : other.Has pointer size) (apart : r.Apart other) (bytes : Memory) (rest : r.Same earlier memory) :
    r.Same earlier (memory.storeBytes pointer size bytes) := by
  intro address inside
  have := placed.start
  have := placed.finish
  simp only [Region.Apart] at apart
  simp only [Region.Contains] at inside
  have away : ¬ (pointer.toNat ≤ address.toNat ∧ address.toNat < pointer.toNat + size) := by omega
  simp only [Memory.storeBytes, away, ↓reduceIte]
  exact rest address inside

end Region.Same

-- A block leaves alone every byte of a region its change misses.
theorem MachineState.Except.same {t s : MachineState} {c : Changes} (kept : t.Except s c) {r : Region}
    (misses : c.Misses r.base (r.base + r.length)) : r.Same s.memory t.memory := by
  intro address inside
  have bound := address.isLt
  have same := kept.sameMemory address 1
    (fun range member => by have := misses range member; simp only [Region.Contains] at inside; omega) (by omega)
  rw [readBytes_one, readBytes_one] at same
  have := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat] at this
  exact Fin.ext (by omega)

-- Two memories that read the same outside a change. `Except.sameMemory` is this of the two states'.
def Changes.Same (c : Changes) (later earlier : Memory) : Prop :=
  ∀ (address : BitVec 64) (size : Nat), c.Misses address.toNat (address.toNat + size) →
    address.toNat + size ≤ 2^64 → readBytes later address size = readBytes earlier address size

-- A range lies inside one the change lists.
def Changes.Covers (c : Changes) (range : Nat × Nat) : Prop :=
  ∃ listed ∈ c.memory, listed.1 ≤ range.1 ∧ range.2 ≤ listed.2

theorem Changes.Covers.listed {c : Changes} {range : Nat × Nat} (member : range ∈ c.memory) : Changes.Covers c range :=
  ⟨range, member, Nat.le_refl _, Nat.le_refl _⟩

-- A change that covers a region covers its parts.
theorem Changes.Covers.part {c : Changes} {r : Region} (covers : Changes.Covers c r.range) (offset length : Nat)
    (inside : offset + length ≤ r.length) : Changes.Covers c (r.part offset length inside).range := by
  obtain ⟨listed, member, low, high⟩ := covers
  exact ⟨listed, member, by simp only [Region.part_base] at low ⊢; omega,
    by simp only [Region.part_base, Region.part_length] at high ⊢; omega⟩

namespace Changes.Same

theorem refl {c : Changes} {memory : Memory} : Changes.Same c memory memory := fun _ _ _ _ => rfl

theorem of_eq {c : Changes} {later middle earlier : Memory} (same : later = middle) (rest : Changes.Same c middle earlier) :
    Changes.Same c later earlier := same ▸ rest

-- A store placed in a region the change covers.
theorem store {c : Changes} {memory earlier bytes : Memory} {r : Region} {pointer : BitVec 64} {size : Nat}
    (placed : r.Has pointer size) (covers : Changes.Covers c r.range) (rest : Changes.Same c memory earlier) :
    Changes.Same c (memory.storeBytes pointer size bytes) earlier := by
  intro address length misses fits
  obtain ⟨listed, member, low, high⟩ := covers
  have away : address.toNat + length ≤ r.base ∨ r.base + r.length ≤ address.toNat := by
    have := misses _ member; simp only at low high; omega
  have := placed.start
  have := placed.finish
  rw [Memory.readBytes_storeBytes_outside _ _ (by omega) fits]
  exact rest address length misses fits

-- A nested block whose change this one covers.
theorem nested {c inner : Changes} {t u : MachineState} {earlier : Memory} (kept : t.Except u inner)
    (within : ∀ range ∈ inner.memory, Changes.Covers c range) (rest : Changes.Same c u.memory earlier) :
    Changes.Same c t.memory earlier := by
  intro address size misses fits
  rw [kept.sameMemory address size (fun range member => by
    obtain ⟨listed, listedIn, low, high⟩ := within range member
    have := misses listed listedIn; omega) fits]
  exact rest address size misses fits

end Changes.Same

-- A pointer as an expression plus a literal number of bytes, as words: `rsp - 8#64` is `rsp` plus
-- `2^64 - 8`. Two pointers off one expression are then a literal number of bytes apart.
namespace Offset

theorem refl (pointer : BitVec 64) : pointer = pointer + BitVec.ofNat 64 0 := by simp

theorem literal (pointer : BitVec 64) : pointer = 0#64 + BitVec.ofNat 64 pointer.toNat := by simp

theorem add {pointer base : BitVec 64} {offset : Nat} (placed : pointer = base + BitVec.ofNat 64 offset)
    (literal : BitVec 64) (sum : Nat) (same : (offset + literal.toNat) % 2^64 = sum) :
    pointer + literal = base + BitVec.ofNat 64 sum := by
  subst placed same
  bv_omega

theorem sub {pointer base : BitVec 64} {offset : Nat} (placed : pointer = base + BitVec.ofNat 64 offset)
    (literal : BitVec 64) (sum : Nat) (same : (offset + (2^64 - literal.toNat)) % 2^64 = sum) :
    pointer - literal = base + BitVec.ofNat 64 sum := by
  subst placed same
  bv_omega

theorem between {pointer other base : BitVec 64} {offset otherOffset : Nat}
    (placed : pointer = base + BitVec.ofNat 64 offset) (otherPlaced : other = base + BitVec.ofNat 64 otherOffset)
    (distance : Nat) (same : (otherOffset + distance) % 2^64 = offset % 2^64) :
    pointer = other + BitVec.ofNat 64 distance := by
  subst placed otherPlaced
  bv_omega

end Offset

-- A place covers the pointers a literal number of bytes past it that stay inside it: `placed.part`,
-- with its two bounds proved by evaluation.
theorem Region.Has.cover {r : Region} {pointer inner : BitVec 64} {size less distance : Nat}
    (placed : r.Has pointer size) (place : inner = pointer + BitVec.ofNat 64 distance)
    (inside : distance + less ≤ size) (positive : 0 < less) : r.Has inner less := by
  subst place
  have := r.fits
  have := placed.start
  have := placed.finish
  constructor <;> bv_omega

theorem Region.Has.toNat_past {r : Region} {pointer inner : BitVec 64} {size distance : Nat}
    (placed : r.Has pointer size) (place : inner = pointer + BitVec.ofNat 64 distance)
    (inside : distance < size) : inner.toNat = pointer.toNat + distance := by
  subst place
  have := r.fits
  have := placed.finish
  bv_omega

-- Two places a literal number of bytes apart, as words, with room for both: their bytes do not meet.
-- It is what `Memory.readBytes_storeBytes_outside` asks, proved by evaluation.
theorem Region.Has.apart {r other : Region} {pointer stored : BitVec 64} {size length distance : Nat}
    (read : r.Has pointer size) (store : other.Has stored length)
    (place : pointer = stored + BitVec.ofNat 64 distance) (after : length ≤ distance) (before : distance + size ≤ 2^64) :
    pointer.toNat + size ≤ stored.toNat ∨ stored.toNat + length ≤ pointer.toNat := by
  subst place
  have := Region.Has.fits read
  have := Region.Has.fits store
  bv_omega

end Internal

end Rivet
