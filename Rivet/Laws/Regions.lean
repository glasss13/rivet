module
public import Rivet.Laws.Memory
public import Rivet.Laws.Changes
import all Rivet.Interpreter.Memory
-- Memory as named regions. A region names a range of addresses. A pointer is placed in a region by
-- `Has`, two regions are `Apart`, and two memories are the `Same` on a region.
@[expose] public section
namespace Rivet

-- The word pointing `offset` bytes into the region.
def Region.place (r : Region) (offset : Nat) : BitVec 64 := BitVec.ofNat 64 (r.base + offset)

-- `pointer` points `offset` bytes into the region: where a register that holds a frame is. A
-- statement of its own, so that nothing rewrites with it.
def Region.At (r : Region) (offset : Nat) (pointer : BitVec 64) : Prop := pointer = r.place offset

-- `size` bytes at `pointer` lie in the region.
structure Region.Has (r : Region) (pointer : BitVec 64) (size : Nat) : Prop where
  start : r.base ≤ pointer.toNat
  finish : pointer.toNat + size ≤ r.base + r.length

def Region.Apart (first second : Region) : Prop :=
  first.base + first.length ≤ second.base ∨ second.base + second.length ≤ first.base

-- `length` bytes of the region from `offset`, with its permissions.
def Region.part (r : Region) (offset length : Nat) (inside : offset + length ≤ r.length := by exact Nat.le_of_ble_eq_true rfl) :
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

theorem Region.place_add {r : Region} {pointer : BitVec 64} {offset : Nat} (placed : pointer = r.place offset)
    (literal : BitVec 64) (sum : Nat) (same : offset + literal.toNat = sum) : pointer + literal = r.place sum := by
  subst placed same
  apply BitVec.eq_of_toNat_eq
  simp [Region.place, Nat.add_assoc]

theorem Region.place_sub {r : Region} {pointer : BitVec 64} {offset : Nat} (placed : pointer = r.place offset)
    (literal : BitVec 64) (difference : Nat) (same : difference + literal.toNat = offset) :
    pointer - literal = r.place difference := by
  subst placed same
  apply BitVec.eq_of_toNat_eq
  have := literal.isLt
  simp only [Region.place, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem Region.Has.of_place {r : Region} {pointer : BitVec 64} {offset size : Nat}
    (placed : pointer = r.place offset) (inside : offset + size ≤ r.length) (positive : 0 < size) : r.Has pointer size := by
  subst placed
  have := r.fits
  constructor <;> simp only [Region.place, BitVec.toNat_ofNat] <;> omega

theorem Region.Has.of_place_part {r : Region} {pointer : BitVec 64} {offset size start length : Nat}
    {inside : start + length ≤ r.length} (placed : pointer = r.place offset)
    (low : start ≤ offset) (high : offset + size ≤ start + length) (positive : 0 < size) :
    (r.part start length inside).Has pointer size := by
  subst placed
  have := r.fits
  constructor <;> simp only [Region.place, Region.part, BitVec.toNat_ofNat] <;> omega

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
    simp only [Region.Contains, Region.part] at within ⊢
    omega
  · apply granted.2 permission
    simp only [Region.Contains, Region.part] at within ⊢
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

-- A read at the place of a store reads the value stored, or its low bytes.
theorem Region.Has.readBytes_stored {r : Region} {pointer stored : BitVec 64} {size length : Nat}
    (placed : r.Has stored length) (same : pointer = stored) (le : size ≤ length) (memory : Memory) (value : BitVec n) :
    readBytes (memory.storeBytes stored length (littleEndianAt value stored)) pointer size =
      value.extractLsb' 0 (8 * size) := by
  subst same
  have := r.fits
  have := placed.finish
  rw [Memory.readBytes_storeBytes_inside _ _ (by omega) (by omega) (by omega),
    readBytes_littleEndianAt value 0 (by omega) (by omega)]

-- Two places off one base at literal offsets: a read that misses a store.
theorem Region.readBytes_store_apart {base : Region} {pointer stored : BitVec 64} {offset storedOffset size length : Nat}
    (read : pointer = base.place offset) (store : stored = base.place storedOffset)
    (readInside : offset + size ≤ base.length) (storeInside : storedOffset + length ≤ base.length)
    (positive : 0 < size ∧ 0 < length)
    (apart : offset + size ≤ storedOffset ∨ storedOffset + length ≤ offset) (memory bytes : Memory) :
    readBytes (memory.storeBytes stored length bytes) pointer size = readBytes memory pointer size := by
  subst read store
  have := base.fits
  have first : (base.place offset).toNat = base.base + offset := by
    simp only [Region.place, BitVec.toNat_ofNat]; omega
  have second : (base.place storedOffset).toNat = base.base + storedOffset := by
    simp only [Region.place, BitVec.toNat_ofNat]; omega
  exact Memory.readBytes_storeBytes_outside _ _ (by omega) (by omega)

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
