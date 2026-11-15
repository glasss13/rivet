module
public import Rivet.Laws.Memory
public import Rivet.Laws.Changes
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

-- `length` bytes of the region from `offset`, with its permissions.
abbrev Region.part (r : Region) (offset length : Nat) (inside : offset + length ≤ r.length := by exact Nat.le_of_ble_eq_true rfl) :
    Region :=
  { base := r.base + offset, length, readable := r.readable, writable := r.writable,
    fits := by have := r.fits; omega }

-- A change lists a region as its range.
abbrev Region.range (r : Region) : Nat × Nat := (r.base, r.base + r.length)

instance : Coe Region (Nat × Nat) := ⟨Region.range⟩

-- The two memories agree on every byte of the region.
def Region.Same (r : Region) (earlier later : Memory) : Prop :=
  ∀ address, r.Contains address → earlier address = later address

def Image.Reads (image : Image) (r : Region) : Prop := ∀ address, r.Contains address → image.readable address = true

def Image.Writes (image : Image) (r : Region) : Prop := ∀ address, r.Contains address → image.writable address = true

-- The image grants the region the permissions the region states.
def Image.Grants (image : Image) (r : Region) : Prop :=
  (r.readable = true → image.Reads r) ∧ (r.writable = true → image.Writes r)

-- The regions a proof names: each granted by the image, and pairwise apart.
structure Image.Layout (image : Image) (regions : List Region) : Prop where
  granted : ∀ r ∈ regions, image.Grants r
  apart : regions.Pairwise Region.Apart

theorem Image.Layout.apart_at {image : Image} {regions : List Region} (layout : image.Layout regions) (i j : Nat)
    (first : i < regions.length) (second : j < regions.length) (differ : i ≠ j) : regions[i].Apart regions[j] := by
  rcases Nat.lt_or_gt_of_ne differ with lt | gt
  · exact List.pairwise_iff_getElem.mp layout.apart i j first second lt
  · exact Or.symm (List.pairwise_iff_getElem.mp layout.apart j i second first gt)

theorem Image.Layout.reads_at {image : Image} {regions : List Region} (layout : image.Layout regions) (i : Nat)
    (bound : i < regions.length) (readable : regions[i].readable = true) : image.Reads regions[i] :=
  (layout.granted _ (List.getElem_mem bound)).1 readable

theorem Image.Layout.writes_at {image : Image} {regions : List Region} (layout : image.Layout regions) (i : Nat)
    (bound : i < regions.length) (writable : regions[i].writable = true) : image.Writes regions[i] :=
  (layout.granted _ (List.getElem_mem bound)).2 writable

theorem Region.Apart.symm {first second : Region} (apart : first.Apart second) : second.Apart first :=
  Or.symm apart

theorem Region.Has.first {r : Region} {pointer : BitVec 64} {size : Nat} (placed : r.Has pointer size)
    {less : Nat} (le : less ≤ size) : r.Has pointer less :=
  ⟨placed.start, by have := placed.finish; omega⟩

theorem Region.Has.part {r : Region} {pointer : BitVec 64} {size : Nat} (placed : r.Has pointer size)
    {inner : BitVec 64} {less : Nat} (start : pointer.toNat ≤ inner.toNat)
    (finish : inner.toNat + less ≤ pointer.toNat + size) : r.Has inner less :=
  ⟨by have := placed.start; omega, by have := placed.finish; omega⟩

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

theorem Region.Has.fits {r : Region} {pointer : BitVec 64} {size : Nat} (placed : r.Has pointer size) :
    pointer.toNat + size ≤ 2^64 := by
  have := r.fits
  have := placed.finish
  omega

-- Two places a literal number of bytes apart, as words, with room for both: their bytes do not meet.
-- It is what `Memory.readBytes_storeBytes_outside` asks, proved by evaluation.
theorem Region.Has.apart {r other : Region} {pointer stored : BitVec 64} {size length distance : Nat}
    (read : r.Has pointer size) (store : other.Has stored length)
    (place : pointer = stored + BitVec.ofNat 64 distance) (after : length ≤ distance) (before : distance + size ≤ 2^64) :
    pointer.toNat + size ≤ stored.toNat ∨ stored.toNat + length ≤ pointer.toNat := by
  subst place
  have := read.fits
  have := store.fits
  bv_omega

theorem Image.grants_of_mem {image : Image} {r : Region} (member : r ∈ image.regions) : image.Grants r := by
  constructor <;> intro permission address inside
  · simp only [Image.readable, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨r, member, permission, inside⟩
  · simp only [Image.writable, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨r, member, permission, inside⟩

theorem Image.Grants.part {image : Image} {r : Region} (granted : image.Grants r) (offset length : Nat)
    (inside : offset + length ≤ r.length) : image.Grants (r.part offset length inside) := by
  constructor <;> intro permission address within
  · apply granted.1 permission
    simp only [Region.Contains] at within ⊢
    omega
  · apply granted.2 permission
    simp only [Region.Contains] at within ⊢
    omega

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

theorem of_eq {r : Region} {earlier middle later : Memory} (same : later = middle) (rest : r.Same earlier middle) :
    r.Same earlier later := same ▸ rest

-- A read placed in the region is the same in both.
theorem read {r : Region} {earlier later : Memory} (same : r.Same earlier later) {pointer : BitVec 64} {size : Nat}
    (placed : r.Has pointer size) : readBytes earlier pointer size = readBytes later pointer size := by
  have := r.fits
  have := placed.start
  have := placed.finish
  exact readBytes_congr (fun other low high => same other ⟨by omega, by omega⟩) (by omega)

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

-- A read inside a store reads those bytes of the value stored.
theorem Region.Has.readBytes_stored {r : Region} {pointer stored : BitVec 64} {size length : Nat}
    (placed : r.Has stored length) (offset : Nat) (start : pointer.toNat = stored.toNat + offset)
    (inside : offset + size ≤ length) (memory : Memory) (value : BitVec n) :
    readBytes (memory.storeBytes stored length (littleEndianAt value stored)) pointer size =
      value.extractLsb' (8 * offset) (8 * size) := by
  have := r.fits
  have := placed.finish
  rw [Memory.readBytes_storeBytes_inside _ _ (by omega) (by omega) (by omega),
    readBytes_littleEndianAt value offset start (by omega)]

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

namespace Changes.Same

theorem refl {c : Changes} {memory : Memory} : c.Same memory memory := fun _ _ _ _ => rfl

theorem of_eq {c : Changes} {later middle earlier : Memory} (same : later = middle) (rest : c.Same middle earlier) :
    c.Same later earlier := same ▸ rest

-- A store placed in a region the change lists.
theorem store {c : Changes} {memory earlier bytes : Memory} {r : Region} {pointer : BitVec 64} {size : Nat}
    (placed : r.Has pointer size) (listed : r.range ∈ c.memory) (rest : c.Same memory earlier) :
    c.Same (memory.storeBytes pointer size bytes) earlier := by
  intro address length misses fits
  have away : address.toNat + length ≤ r.base ∨ r.base + r.length ≤ address.toNat := misses _ listed
  have := placed.start
  have := placed.finish
  rw [Memory.readBytes_storeBytes_outside _ _ (by omega) fits]
  exact rest address length misses fits

-- A nested block whose change is within this one.
theorem nested {c inner : Changes} {t u : MachineState} {earlier : Memory} (kept : t.Except u inner)
    (within : ∀ range ∈ inner.memory, range ∈ c.memory) (rest : c.Same u.memory earlier) :
    c.Same t.memory earlier := by
  intro address size misses fits
  rw [kept.sameMemory address size (fun range member => misses range (within range member)) fits]
  exact rest address size misses fits

end Changes.Same

end Rivet
