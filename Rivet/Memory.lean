module
public import Rivet.Syntax
@[expose] public section
namespace Rivet

/-- A memory range with offset-indexed contents, concrete or symbolic. -/
structure MemoryRegion where
  address : Nat
  size : Nat
  contents : Nat → Fin 256 := fun _ => 0
  readable : Bool
  writable : Bool

def MemoryRegion.contains (region : MemoryRegion) (address : Nat) : Bool :=
  region.address ≤ address && address < region.address + region.size

/-- Regions must be disjoint and contained in the 64-bit address space. -/
def MemoryRegion.validLayout : List MemoryRegion → Bool
  | [] => true
  | region :: rest =>
    region.address + region.size ≤ word &&
    rest.all (fun other => region.size == 0 || other.size == 0 ||
      region.address + region.size ≤ other.address || other.address + other.size ≤ region.address) &&
    validLayout rest

/-- A complete memory layout. Its validity proof is preserved by stores. -/
structure Memory where
  regions : List MemoryRegion
  valid : MemoryRegion.validLayout regions = true := by decide +kernel

/-- Checked construction for runtime layouts. Symbolic layouts can supply `valid` directly. -/
def Memory.ofRegions (regions : List MemoryRegion) : Except String Memory :=
  if valid : MemoryRegion.validLayout regions = true then .ok ⟨regions, valid⟩
  else .error "memory regions overlap or exceed the 64-bit address space"

/-- Inspect a byte; instruction semantics check read permission before loading it. -/
def Memory.read (memory : Memory) (address : Nat) : Fin 256 :=
  match memory.regions.find? (·.contains address) with
  | some region => region.contents (address - region.address)
  | none => 0

instance : CoeFun Memory (fun _ => Nat → Fin 256) := ⟨Memory.read⟩

def Memory.readable (memory : Memory) (address : Nat) : Bool :=
  memory.regions.any fun region => region.contains address && region.readable

def Memory.writable (memory : Memory) (address : Nat) : Bool :=
  memory.regions.any fun region => region.contains address && region.writable

private theorem valid_contents (regions : List MemoryRegion) (contents : MemoryRegion → Nat → Fin 256) :
    MemoryRegion.validLayout (regions.map (fun region => { region with contents := contents region })) =
      MemoryRegion.validLayout regions := by
  induction regions with
  | nil => rfl
  | cons region rest inductionHypothesis =>
    simp only [List.map_cons, MemoryRegion.validLayout, inductionHypothesis]
    simp [List.all_map, Function.comp_def]

/-- Store offset-indexed bytes without changing the layout or permissions. -/
def Memory.storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) : Memory :=
  { regions := memory.regions.map (fun region =>
      { region with
        contents := fun offset =>
          if address ≤ region.address + offset && region.address + offset < address + size then
            bytes (region.address + offset - address)
          else region.contents offset })
    valid := by rw [valid_contents]; exact memory.valid }

@[simp] theorem Memory.readable_storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) :
    (memory.storeBytes address size bytes).readable = memory.readable := by
  funext other
  simp [Memory.readable, Memory.storeBytes, List.any_map, MemoryRegion.contains, Function.comp_def]

@[simp] theorem Memory.writable_storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) :
    (memory.storeBytes address size bytes).writable = memory.writable := by
  funext other
  simp [Memory.writable, Memory.storeBytes, List.any_map, MemoryRegion.contains, Function.comp_def]

/-- Inside a store, mapping suffices to recover the written byte. Outside it,
no mapping or permission assumption is needed. -/
theorem Memory.read_storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256)
    (other : Nat) (mapped : address ≤ other ∧ other < address + size →
      ∃ region ∈ memory.regions, region.contains other = true) :
    (memory.storeBytes address size bytes) other =
      if address ≤ other ∧ other < address + size then bytes (other - address) else memory other := by
  simp only [Memory.storeBytes, Memory.read, List.find?_map, Function.comp_def, MemoryRegion.contains]
  cases found : memory.regions.find?
      (fun region => region.address ≤ other && other < region.address + region.size) with
  | none =>
    have outside : ¬ (address ≤ other ∧ other < address + size) := by
      intro inside
      obtain ⟨region, member, contains⟩ := mapped inside
      exact (List.find?_eq_none.mp found region member) contains
    simp [outside]
  | some region =>
    have bounds : region.address ≤ other ∧ other < region.address + region.size := by
      simpa using List.find?_some found
    simp [Nat.add_sub_of_le bounds.1]

/-- Bytes outside a store are unchanged, even when unmapped. -/
theorem Memory.read_storeBytes_outside (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256)
    (other : Nat) (outside : other < address ∨ address + size ≤ other) :
    (memory.storeBytes address size bytes) other = memory other := by
  have excluded : ¬ (address ≤ other ∧ other < address + size) := by omega
  rw [memory.read_storeBytes address size bytes other (by intro inside; exact False.elim (excluded inside))]
  exact ite_eq_right excluded

/-- Little-endian bytes, independent of scalar or vector instruction widths.
This raw read does not check permissions. -/
def readBytes (memory : Nat → Fin 256) (address size : Nat) : BitVec (8 * size) :=
  BitVec.ofNat (8 * size) ((List.range size).foldr
    (fun offset value => (memory (address + offset)).val + 256 * value) 0)

/-- A byte-range equality is sufficient to replace a multi-byte read. -/
theorem readBytes_congr (first second : Nat → Fin 256) (address size : Nat)
    (equal : ∀ offset < size, first (address + offset) = second (address + offset)) :
    readBytes first address size = readBytes second address size := by
  have same : (List.range size).map (fun offset => first (address + offset)) =
      (List.range size).map (fun offset => second (address + offset)) :=
    List.map_congr_left (by intro offset member; exact equal offset (List.mem_range.mp member))
  simpa only [readBytes, List.foldr_map] using congrArg
    (fun bytes : List (Fin 256) => BitVec.ofNat (8 * size)
      (bytes.foldr (fun byte value => byte.val + 256 * value) 0)) same

/-- A multi-byte instruction access must fit the word address space and have
permission for every byte. -/
def permits (permission : Nat → Bool) (address size : Nat) : Bool :=
  address + size ≤ word && (List.range size).all (fun offset => permission (address + offset))

theorem permits_iff (permission : Nat → Bool) (address size : Nat) :
    permits permission address size = true ↔
      address + size ≤ word ∧ ∀ offset < size, permission (address + offset) = true := by
  simp [permits, List.all_eq_true, List.mem_range]

end Rivet
