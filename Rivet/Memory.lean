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

/-- Little-endian bytes of a value of any width: byte `offset` is what scalar
and vector stores write, and what `readBytes` decodes. -/
def littleEndianBytes (value : BitVec n) : Nat → Fin 256 :=
  fun offset => ⟨(value.toNat / 256^offset) % 256, Nat.mod_lt _ (by decide)⟩

/-- Little-endian bytes, independent of scalar or vector instruction widths.
This raw read does not check permissions. -/
def readBytes (memory : Nat → Fin 256) (address size : Nat) : BitVec (8 * size) :=
  BitVec.ofNat (8 * size) ((List.range size).foldr
    (fun offset value => (memory (address + offset)).val + 256 * value) 0)

/-- A multi-byte instruction access must fit the word address space and have
permission for every byte. -/
def permits (permission : Nat → Bool) (address size : Nat) : Bool :=
  address + size ≤ word && (List.range size).all (fun offset => permission (address + offset))

theorem permits_iff (permission : Nat → Bool) (address size : Nat) :
    permits permission address size = true ↔
      address + size ≤ word ∧ ∀ offset < size, permission (address + offset) = true := by
  simp [permits, List.all_eq_true, List.mem_range]

/-! ## Reasoning about memory

Addresses and sizes in these lemmas are plain `Nat`s, so their side conditions
close by `omega`. A footprint is a set of addresses, `Nat → Prop`, such as
`fun address => output ≤ address ∧ address < output + count`. -/

private theorem foldr_bytes {first second : Nat → Nat} {size : Nat}
    (same : ∀ offset < size, first offset = second offset) :
    (List.range size).foldr (fun offset value => first offset + 256 * value) 0 =
      (List.range size).foldr (fun offset value => second offset + 256 * value) 0 := by
  have each : ∀ offsets : List Nat, (∀ offset ∈ offsets, offset < size) →
      offsets.foldr (fun offset value => first offset + 256 * value) 0 =
        offsets.foldr (fun offset value => second offset + 256 * value) 0 := by
    intro offsets bounded
    induction offsets with
    | nil => rfl
    | cons offset rest inductionHypothesis =>
      simp only [List.foldr_cons]
      rw [same offset (bounded offset List.mem_cons_self),
        inductionHypothesis (fun other member => bounded other (List.mem_cons_of_mem _ member))]
  exact each _ (fun offset member => List.mem_range.mp member)

/-- A read depends only on the bytes it covers. -/
theorem readBytes_congr {first second : Nat → Fin 256} {address other size : Nat}
    (same : ∀ offset < size, first (address + offset) = second (other + offset)) :
    readBytes first address size = readBytes second other size := by
  unfold readBytes
  rw [foldr_bytes (fun offset bound => congrArg Fin.val (same offset bound))]

private theorem foldr_littleEndian (value offset size : Nat) :
    (List.range size).foldr (fun index rest => value / 256^(offset + index) % 256 + 256 * rest) 0 =
      value / 256^offset % 256^size := by
  induction size generalizing offset with
  | zero => simp [Nat.mod_one]
  | succ size inductionHypothesis =>
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    have shifted : (fun index rest => value / 256^(offset + (index + 1)) % 256 + 256 * rest) =
        (fun index rest => value / 256^((offset + 1) + index) % 256 + 256 * rest) := by
      funext index rest
      rw [show offset + (index + 1) = (offset + 1) + index by omega]
    simp only [Nat.succ_eq_add_one, Nat.add_zero]
    rw [shifted, inductionHypothesis (offset + 1), Nat.pow_succ 256 size, Nat.mul_comm _ 256,
      Nat.mod_mul, Nat.pow_succ 256 offset, ← Nat.div_div_eq_div_mul]

/-- Reading back stored little-endian bytes selects the corresponding bits. -/
theorem readBytes_littleEndianBytes (value : BitVec n) (offset size : Nat) :
    readBytes (littleEndianBytes value) offset size = value.extractLsb' (8 * offset) (8 * size) := by
  apply BitVec.eq_of_toNat_eq
  simp only [readBytes, littleEndianBytes, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  rw [foldr_littleEndian, Nat.pow_mul, Nat.pow_mul]
  simp only [Nat.reducePow, Nat.mod_mod]

/-- Bytes a store does not cover are unchanged, even when unmapped. -/
theorem Memory.readBytes_storeBytes_disjoint (memory : Memory) (bytes : Nat → Fin 256)
    {address size other count : Nat} (away : other + count ≤ address ∨ address + size ≤ other) :
    readBytes (memory.storeBytes address size bytes) other count = readBytes memory other count :=
  readBytes_congr fun _ _ => memory.read_storeBytes_outside address size bytes _ (by omega)

/-- Reading inside a store returns the stored bytes. The store's write permission
ensures every byte is mapped (stores to unmapped bytes are dropped). -/
theorem Memory.readBytes_storeBytes_within (memory : Memory) (bytes : Nat → Fin 256)
    {address size other count : Nat} (writable : permits memory.writable address size = true)
    (lower : address ≤ other) (upper : other + count ≤ address + size) :
    readBytes (memory.storeBytes address size bytes) other count =
      readBytes bytes (other - address) count := by
  apply readBytes_congr
  intro offset bound
  rw [memory.read_storeBytes address size bytes _ (fun inside => by
    have allowed := ((permits_iff _ _ _).mp writable).2 (other + offset - address) (by omega)
    rw [show address + (other + offset - address) = other + offset by omega] at allowed
    simp only [Memory.writable, List.any_eq_true, Bool.and_eq_true] at allowed
    obtain ⟨region, member, contains, _⟩ := allowed
    exact ⟨region, member, contains⟩)]
  have inside : address ≤ other + offset ∧ other + offset < address + size := ⟨by omega, by omega⟩
  simp only [inside, and_self, ↓reduceIte]
  rw [show other + offset - address = other - address + offset by omega]

/-- A permission over a range holds over every subrange. -/
theorem permits_within {permission : Nat → Bool} {address size other count : Nat}
    (whole : permits permission address size = true)
    (lower : address ≤ other) (upper : other + count ≤ address + size) :
    permits permission other count = true := by
  rw [permits_iff] at whole ⊢
  refine ⟨by omega, fun offset bound => ?_⟩
  have allowed := whole.2 (other + offset - address) (by omega)
  rwa [show address + (other + offset - address) = other + offset by omega] at allowed

/-- `after` holds the same bytes as `before` at every address outside `footprint`. -/
def Memory.SameOutside (before after : Memory) (footprint : Nat → Prop) : Prop :=
  ∀ address, ¬ footprint address → after address = before address

theorem Memory.SameOutside.refl (memory : Memory) (footprint : Nat → Prop) :
    memory.SameOutside memory footprint :=
  fun _ _ => rfl

theorem Memory.SameOutside.trans {first second third : Memory} {footprint : Nat → Prop}
    (earlier : first.SameOutside second footprint) (later : second.SameOutside third footprint) :
    first.SameOutside third footprint :=
  fun address outside => (later address outside).trans (earlier address outside)

/-- A footprint can always be enlarged. -/
theorem Memory.SameOutside.mono {before after : Memory} {footprint larger : Nat → Prop}
    (agree : before.SameOutside after footprint) (covered : ∀ address, footprint address → larger address) :
    before.SameOutside after larger :=
  fun address outside => agree address (fun inside => outside (covered address inside))

/-- A store inside the footprint keeps the agreement. -/
theorem Memory.SameOutside.storeBytes {before after : Memory} {footprint : Nat → Prop}
    (agree : before.SameOutside after footprint) {address size : Nat} (bytes : Nat → Fin 256)
    (inside : ∀ other, address ≤ other → other < address + size → footprint other) :
    before.SameOutside (after.storeBytes address size bytes) footprint := by
  intro other outside
  rw [after.read_storeBytes_outside address size bytes other
    ((Nat.lt_or_ge other address).elim Or.inl fun lower =>
      Or.inr (Nat.le_of_not_lt fun upper => outside (inside other lower upper)))]
  exact agree other outside

/-- The frame law: a read outside the footprint sees the original bytes. -/
theorem Memory.SameOutside.readBytes {before after : Memory} {footprint : Nat → Prop}
    (agree : before.SameOutside after footprint) {address size : Nat}
    (away : ∀ other, address ≤ other → other < address + size → ¬ footprint other) :
    Rivet.readBytes after address size = Rivet.readBytes before address size :=
  readBytes_congr fun offset bound => agree _ (away _ (by omega) (by omega))

/-! ## Facts from the layout

Each lemma takes `member : region ∈ memory.regions`. For a layout given as
`layout : memory.regions = [...]`, state the region and prove membership by
`rw [layout]; simp`; ascribing the clean statement then unfolds the region:

    have member : ({ address := input, size := count, contents := bytes,
                     readable := true, writable := false } : MemoryRegion) ∈ memory.regions := by
      rw [layout]; simp
    have readable : permits memory.readable input count = true :=
      memory.permits_readable_of_mem member rfl -/

private theorem validLayout_iff (regions : List MemoryRegion) :
    MemoryRegion.validLayout regions = true ↔
      (∀ region ∈ regions, region.address + region.size ≤ word) ∧
      regions.Pairwise fun first second => first.size = 0 ∨ second.size = 0 ∨
        first.address + first.size ≤ second.address ∨ second.address + second.size ≤ first.address := by
  induction regions with
  | nil => simp [MemoryRegion.validLayout]
  | cons region rest inductionHypothesis =>
    simp only [MemoryRegion.validLayout, Bool.and_eq_true, inductionHypothesis, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.pairwise_cons, List.mem_cons,
      forall_eq_or_imp]
    constructor
    · intro ⟨⟨fits, apart⟩, restFits, restApart⟩
      exact ⟨⟨fits, restFits⟩, fun other member => by have := apart other member; omega, restApart⟩
    · intro ⟨⟨fits, restFits⟩, apart, restApart⟩
      exact ⟨⟨fits, fun other member => by have := apart other member; omega⟩, restFits, restApart⟩

/-- Distinct regions share no address. -/
theorem Memory.regions_disjoint (memory : Memory) :
    memory.regions.Pairwise fun first second => first.size = 0 ∨ second.size = 0 ∨
      first.address + first.size ≤ second.address ∨ second.address + second.size ≤ first.address :=
  ((validLayout_iff _).mp memory.valid).2

/-- Every region fits in the 64-bit address space. -/
theorem Memory.fits_of_mem (memory : Memory) {region : MemoryRegion} (member : region ∈ memory.regions) :
    region.address + region.size ≤ word :=
  ((validLayout_iff _).mp memory.valid).1 region member

private theorem permits_of_mem (memory : Memory) (field : MemoryRegion → Bool) {region : MemoryRegion}
    (member : region ∈ memory.regions) (allowed : field region = true) {address size : Nat}
    (lower : region.address ≤ address) (upper : address + size ≤ region.address + region.size) :
    permits (fun other => memory.regions.any fun region => region.contains other && field region)
      address size = true := by
  have fits := memory.fits_of_mem member
  rw [permits_iff]
  refine ⟨by omega, fun offset bound => List.any_eq_true.mpr ⟨region, member, ?_⟩⟩
  simp only [MemoryRegion.contains, allowed, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A readable region is readable throughout; use `permits_within` for parts of it. -/
theorem Memory.permits_readable_of_mem (memory : Memory) {region : MemoryRegion}
    (member : region ∈ memory.regions) (readable : region.readable = true) :
    permits memory.readable region.address region.size = true :=
  permits_of_mem memory MemoryRegion.readable member readable (Nat.le_refl _) (Nat.le_refl _)

/-- A writable region is writable throughout; use `permits_within` for parts of it. -/
theorem Memory.permits_writable_of_mem (memory : Memory) {region : MemoryRegion}
    (member : region ∈ memory.regions) (writable : region.writable = true) :
    permits memory.writable region.address region.size = true :=
  permits_of_mem memory MemoryRegion.writable member writable (Nat.le_refl _) (Nat.le_refl _)

private theorem find_region {regions : List MemoryRegion}
    (disjoint : regions.Pairwise fun first second => first.size = 0 ∨ second.size = 0 ∨
      first.address + first.size ≤ second.address ∨ second.address + second.size ≤ first.address)
    {region : MemoryRegion} (member : region ∈ regions) {address : Nat}
    (contains : region.contains address = true) :
    regions.find? (·.contains address) = some region := by
  induction regions with
  | nil => cases member
  | cons head rest inductionHypothesis =>
    rw [List.pairwise_cons] at disjoint
    by_cases here : head.contains address = true
    · simp only [List.find?_cons, here]
      rcases List.mem_cons.mp member with equal | later
      · rw [equal]
      · have apart := disjoint.1 region later
        simp only [MemoryRegion.contains, Bool.and_eq_true, decide_eq_true_eq] at here contains
        omega
    · simp only [List.find?_cons, Bool.not_eq_true] at here ⊢
      rw [here]
      rcases List.mem_cons.mp member with equal | later
      · rw [equal] at contains; simp [contains] at here
      · exact inductionHypothesis disjoint.2 later

/-- Inside a region, memory reads the region's contents. -/
theorem Memory.readBytes_of_mem (memory : Memory) {region : MemoryRegion}
    (member : region ∈ memory.regions) {address size : Nat}
    (lower : region.address ≤ address) (upper : address + size ≤ region.address + region.size) :
    readBytes memory address size = readBytes region.contents (address - region.address) size := by
  apply readBytes_congr
  intro offset bound
  have found := find_region memory.regions_disjoint member (address := address + offset) (by
    simp only [MemoryRegion.contains, Bool.and_eq_true, decide_eq_true_eq]; omega)
  simp only [Memory.read, found]
  rw [show address + offset - region.address = address - region.address + offset by omega]

end Rivet
