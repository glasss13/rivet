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

/-- Update contents only; instruction semantics check permission before storing. -/
def Memory.storeByte (memory : Memory) (address : Nat) (value : Fin 256) : Memory :=
  { regions := memory.regions.map (fun region => { region with contents := fun offset =>
      if region.address + offset = address then value else region.contents offset })
    valid := by rw [valid_contents]; exact memory.valid }

/-- Store offset-indexed bytes without changing the layout or permissions. -/
def Memory.storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) : Memory :=
  { regions := memory.regions.map (fun region =>
      { region with
        contents := fun offset =>
          if address ≤ region.address + offset && region.address + offset < address + size then
            bytes (region.address + offset - address)
          else region.contents offset })
    valid := by rw [valid_contents]; exact memory.valid }

@[simp] theorem Memory.readable_storeByte (memory : Memory) (address : Nat) (value : Fin 256) :
    (memory.storeByte address value).readable = memory.readable := by
  funext other
  simp [Memory.readable, Memory.storeByte, List.any_map, MemoryRegion.contains, Function.comp_def]

@[simp] theorem Memory.writable_storeByte (memory : Memory) (address : Nat) (value : Fin 256) :
    (memory.storeByte address value).writable = memory.writable := by
  funext other
  simp [Memory.writable, Memory.storeByte, List.any_map, MemoryRegion.contains, Function.comp_def]

/-- A permitted byte store changes exactly the addressed byte. -/
theorem Memory.read_storeByte (memory : Memory) (address : Nat) (value : Fin 256)
    (allowed : memory.writable address = true) :
    (memory.storeByte address value).read = fun other => if other = address then value else memory other := by
  funext other
  simp only [Memory.storeByte, Memory.read, List.find?_map, Function.comp_def, MemoryRegion.contains]
  cases found : memory.regions.find?
      (fun region => region.address ≤ other && other < region.address + region.size) with
  | none =>
    by_cases equal : other = address
    · subst other
      obtain ⟨region, member, permission⟩ := List.any_eq_true.mp allowed
      have contains : region.contains address = true :=
        (show region.contains address = true ∧ region.writable = true from by simpa using permission).1
      exact False.elim ((List.find?_eq_none.mp found region member) contains)
    · simp [equal]
  | some region =>
    have bounds : region.address ≤ other ∧ other < region.address + region.size := by
      simpa using List.find?_some found
    have lower := bounds.1
    simp [Nat.add_sub_of_le lower]

end Rivet
