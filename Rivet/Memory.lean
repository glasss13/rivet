module
public import Rivet.Syntax
@[expose] public section
namespace Rivet

/-- The flat 64-bit address space: a byte and read and write permissions at every
address. Unmapped addresses have neither permission. Build one from a layout with
`Memory.ofRegions`. -/
structure Memory where
  bytes : Nat → Fin 256 := fun _ => 0
  readable : Nat → Bool := fun _ => false
  writable : Nat → Bool := fun _ => false

instance : CoeFun Memory (fun _ => Nat → Fin 256) := ⟨Memory.bytes⟩

/-- Store `bytes 0, bytes 1, …` at `address, address + 1, …`. Permissions are
unchanged; instructions check them before storing. -/
def Memory.storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) : Memory :=
  { memory with bytes := fun other =>
      if address ≤ other ∧ other < address + size then bytes (other - address) else memory other }

@[simp] theorem Memory.readable_storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) :
    (memory.storeBytes address size bytes).readable = memory.readable := rfl

@[simp] theorem Memory.writable_storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) :
    (memory.storeBytes address size bytes).writable = memory.writable := rfl

theorem Memory.read_storeBytes (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256) (other : Nat) :
    (memory.storeBytes address size bytes) other =
      if address ≤ other ∧ other < address + size then bytes (other - address) else memory other := rfl

theorem Memory.read_storeBytes_outside (memory : Memory) (address size : Nat) (bytes : Nat → Fin 256)
    (other : Nat) (outside : other < address ∨ address + size ≤ other) :
    (memory.storeBytes address size bytes) other = memory other := by
  have away : ¬ (address ≤ other ∧ other < address + size) := by omega
  simp only [Memory.read_storeBytes, away, ↓reduceIte]

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

/-- A read outside a store sees the bytes from before it. -/
theorem Memory.readBytes_storeBytes_disjoint (memory : Memory) (bytes : Nat → Fin 256)
    {address size other count : Nat} (away : other + count ≤ address ∨ address + size ≤ other) :
    readBytes (memory.storeBytes address size bytes) other count = readBytes memory other count := by
  apply readBytes_congr
  intro offset bound
  have outside : ¬ (address ≤ other + offset ∧ other + offset < address + size) := by omega
  simp only [Memory.read_storeBytes, outside, ↓reduceIte]

/-- A read inside a store sees the stored bytes. -/
theorem Memory.readBytes_storeBytes_within (memory : Memory) (bytes : Nat → Fin 256)
    {address size other count : Nat} (lower : address ≤ other) (upper : other + count ≤ address + size) :
    readBytes (memory.storeBytes address size bytes) other count =
      readBytes bytes (other - address) count := by
  apply readBytes_congr
  intro offset bound
  have inside : address ≤ other + offset ∧ other + offset < address + size := ⟨by omega, by omega⟩
  simp only [Memory.read_storeBytes, inside, and_self, ↓reduceIte]
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
  have away : ¬ (address ≤ other ∧ other < address + size) :=
    fun ⟨lower, upper⟩ => outside (inside other lower upper)
  simp only [Memory.read_storeBytes, away, ↓reduceIte]
  exact agree other outside

/-- The frame law: a read outside the footprint sees the original bytes. -/
theorem Memory.SameOutside.readBytes {before after : Memory} {footprint : Nat → Prop}
    (agree : before.SameOutside after footprint) {address size : Nat}
    (away : ∀ other, address ≤ other → other < address + size → ¬ footprint other) :
    Rivet.readBytes after address size = Rivet.readBytes before address size :=
  readBytes_congr fun offset bound => agree _ (away _ (by omega) (by omega))

/-! ## Building memory from regions -/

/-- A block of memory with offset-indexed contents, concrete or symbolic. The
importer emits each loadable segment of a binary as a region. -/
structure MemoryRegion where
  address : Nat
  size : Nat
  contents : Nat → Fin 256 := fun _ => 0
  readable : Bool
  writable : Bool

def MemoryRegion.contains (region : MemoryRegion) (address : Nat) : Bool :=
  region.address ≤ address && address < region.address + region.size

/-- Two regions share no address. -/
def MemoryRegion.Disjoint (first second : MemoryRegion) : Prop :=
  first.size = 0 ∨ second.size = 0 ∨
    first.address + first.size ≤ second.address ∨ second.address + second.size ≤ first.address

/-- Memory laid out as regions. An address has a permission if a region containing
it grants one, and its byte comes from the first region containing it. Addresses
outside every region read zero and have no permissions. -/
def Memory.ofRegions (regions : List MemoryRegion) : Memory where
  bytes address := match regions.find? (·.contains address) with
    | some region => region.contents (address - region.address)
    | none => 0
  readable address := regions.any fun region => region.contains address && region.readable
  writable address := regions.any fun region => region.contains address && region.writable

/-! The lemmas below take `member : region ∈ regions` and read the region's fields
from it, so their side conditions close by `omega`. State the region when proving
membership:

    have input : ({ address := base, size := count, contents := bytes,
                    readable := true, writable := false } : MemoryRegion) ∈ regions := by
      simp [regions]
    have readable : permits (Memory.ofRegions regions).readable base count = true :=
      Memory.permits_readable_ofRegions input (by omega) -/

private theorem permits_ofRegions (regions : List MemoryRegion) (field : MemoryRegion → Bool)
    {region : MemoryRegion} (member : region ∈ regions) (allowed : field region = true)
    (fits : region.address + region.size ≤ word) :
    permits (fun other => regions.any fun region => region.contains other && field region)
      region.address region.size = true := by
  rw [permits_iff]
  refine ⟨fits, fun offset bound => List.any_eq_true.mpr ⟨region, member, ?_⟩⟩
  simp only [MemoryRegion.contains, allowed, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A readable region is readable throughout; use `permits_within` for parts of it. -/
theorem Memory.permits_readable_ofRegions {regions : List MemoryRegion} {address size : Nat}
    {contents : Nat → Fin 256} {writable : Bool}
    (member : ⟨address, size, contents, true, writable⟩ ∈ regions) (fits : address + size ≤ word) :
    permits (Memory.ofRegions regions).readable address size = true :=
  permits_ofRegions regions MemoryRegion.readable member rfl fits

/-- A writable region is writable throughout; use `permits_within` for parts of it. -/
theorem Memory.permits_writable_ofRegions {regions : List MemoryRegion} {address size : Nat}
    {contents : Nat → Fin 256} {readable : Bool}
    (member : ⟨address, size, contents, readable, true⟩ ∈ regions) (fits : address + size ≤ word) :
    permits (Memory.ofRegions regions).writable address size = true :=
  permits_ofRegions regions MemoryRegion.writable member rfl fits

private theorem find_region {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
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
        simp only [MemoryRegion.Disjoint] at apart
        simp only [MemoryRegion.contains, Bool.and_eq_true, decide_eq_true_eq] at here contains
        omega
    · simp only [List.find?_cons, Bool.not_eq_true] at here ⊢
      rw [here]
      rcases List.mem_cons.mp member with equal | later
      · rw [equal] at contains; simp [contains] at here
      · exact inductionHypothesis disjoint.2 later

private theorem contains_inside {base count address : Nat} {contents : Nat → Fin 256} {readable writable : Bool}
    (lower : base ≤ address) (upper : address < base + count) :
    (⟨base, count, contents, readable, writable⟩ : MemoryRegion).contains address = true := by
  simp only [MemoryRegion.contains, Bool.and_eq_true, decide_eq_true_eq]; omega

private theorem any_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    (field : MemoryRegion → Bool) {region : MemoryRegion} (member : region ∈ regions) {address : Nat}
    (contains : region.contains address = true) :
    (regions.any fun other => other.contains address && field other) = field region := by
  have unique : ∀ other ∈ regions, other.contains address = true → other = region := fun other inside hit =>
    Option.some.inj ((find_region disjoint inside hit).symm.trans (find_region disjoint member contains))
  cases granted : field region
  · apply List.any_eq_false.mpr
    intro other inside both
    simp only [Bool.and_eq_true] at both
    rw [unique other inside both.1, granted] at both
    simp at both
  · exact List.any_eq_true.mpr ⟨region, member, by simp [contains, granted]⟩

/-- At an address inside a region of a disjoint layout, memory holds the region's byte. -/
theorem Memory.read_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {base count : Nat} {contents : Nat → Fin 256} {readable writable : Bool}
    (member : ⟨base, count, contents, readable, writable⟩ ∈ regions) {address : Nat}
    (lower : base ≤ address) (upper : address < base + count) :
    (Memory.ofRegions regions) address = contents (address - base) := by
  have found := find_region disjoint member (contains_inside (address := address) lower upper)
  simp only [Memory.ofRegions, found]

/-- Inside a region of a disjoint layout, an address is readable exactly when the region is. -/
theorem Memory.readable_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {base count : Nat} {contents : Nat → Fin 256} {readable writable : Bool}
    (member : ⟨base, count, contents, readable, writable⟩ ∈ regions) {address : Nat}
    (lower : base ≤ address) (upper : address < base + count) :
    (Memory.ofRegions regions).readable address = readable :=
  any_ofRegions disjoint MemoryRegion.readable member (contains_inside lower upper)

/-- Inside a region of a disjoint layout, an address is writable exactly when the region is;
so read-only data is unwritable. -/
theorem Memory.writable_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {base count : Nat} {contents : Nat → Fin 256} {readable writable : Bool}
    (member : ⟨base, count, contents, readable, writable⟩ ∈ regions) {address : Nat}
    (lower : base ≤ address) (upper : address < base + count) :
    (Memory.ofRegions regions).writable address = writable :=
  any_ofRegions disjoint MemoryRegion.writable member (contains_inside lower upper)

/-- Inside a region of a disjoint layout, memory holds the region's contents. -/
theorem Memory.readBytes_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {base count : Nat} {contents : Nat → Fin 256} {readable writable : Bool}
    (member : ⟨base, count, contents, readable, writable⟩ ∈ regions) {address size : Nat}
    (lower : base ≤ address) (upper : address + size ≤ base + count) :
    readBytes (Memory.ofRegions regions) address size = readBytes contents (address - base) size := by
  apply readBytes_congr
  intro offset bound
  rw [Memory.read_ofRegions disjoint member (by omega) (by omega),
    show address + offset - base = address - base + offset by omega]

end Rivet
