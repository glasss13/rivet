module
public import Rivet.Syntax
@[expose] public section
namespace Rivet

/-- The 64-bit address space: a byte and read and write permissions at every
address. Unmapped addresses have neither permission. Build one from a layout with
`Memory.ofRegions`. -/
structure Memory where
  bytes : BitVec 64 → Fin 256 := fun _ => 0
  readable : BitVec 64 → Bool := fun _ => false
  writable : BitVec 64 → Bool := fun _ => false

instance : CoeFun Memory (fun _ => BitVec 64 → Fin 256) := ⟨Memory.bytes⟩

/-! A range of memory is a pair of addresses `[start, stop)`: the addresses `x`
with `start ≤ x ∧ x < stop`, compared unsigned. A range with `start ≤ stop` does
not wrap. Side conditions in these terms close by `bv_omega`. -/

/-- Every address in `[start, stop)` takes its byte from `bytes`; the rest keep
theirs. Permissions are unchanged; instructions check them before storing. -/
def Memory.storeBytes (memory : Memory) (start stop : BitVec 64) (bytes : BitVec 64 → Fin 256) : Memory :=
  { memory with bytes := fun address => if start ≤ address ∧ address < stop then bytes address else memory address }

@[simp] theorem Memory.readable_storeBytes (memory : Memory) (start stop : BitVec 64)
    (bytes : BitVec 64 → Fin 256) : (memory.storeBytes start stop bytes).readable = memory.readable := rfl

@[simp] theorem Memory.writable_storeBytes (memory : Memory) (start stop : BitVec 64)
    (bytes : BitVec 64 → Fin 256) : (memory.storeBytes start stop bytes).writable = memory.writable := rfl

theorem Memory.read_storeBytes (memory : Memory) (start stop : BitVec 64) (bytes : BitVec 64 → Fin 256)
    (address : BitVec 64) :
    (memory.storeBytes start stop bytes) address =
      if start ≤ address ∧ address < stop then bytes address else memory address := rfl

theorem Memory.read_storeBytes_outside (memory : Memory) (start stop : BitVec 64) (bytes : BitVec 64 → Fin 256)
    (address : BitVec 64) (outside : address < start ∨ stop ≤ address) :
    (memory.storeBytes start stop bytes) address = memory address := by
  have away : ¬ (start ≤ address ∧ address < stop) := by bv_omega
  simp only [Memory.read_storeBytes, away, ↓reduceIte]

/-- The little-endian bytes of a value of any width, laid out from `address`:
byte `i` of the value is at `address + i`. Scalar and vector stores write these. -/
def littleEndianAt (value : BitVec n) (address : BitVec 64) : BitVec 64 → Fin 256 :=
  fun other => ⟨(value.toNat / 256^(other - address).toNat) % 256, Nat.mod_lt _ (by decide)⟩

/-- Read `size` little-endian bytes starting at `address`, for scalar, vector, and
return-address reads. This raw read does not check permissions. -/
def readBytes (memory : BitVec 64 → Fin 256) (address : BitVec 64) (size : Nat) : BitVec (8 * size) :=
  BitVec.ofNat (8 * size) ((List.range size).foldr
    (fun offset value => (memory (address + BitVec.ofNat 64 offset)).val + 256 * value) 0)

/-- An access to `[start, stop)` must not wrap, and needs permission at every address. -/
def permits (permission : BitVec 64 → Bool) (start stop : BitVec 64) : Bool :=
  start ≤ stop && (List.range (stop - start).toNat).all (fun offset => permission (start + BitVec.ofNat 64 offset))

theorem permits_iff (permission : BitVec 64 → Bool) (start stop : BitVec 64) :
    permits permission start stop = true ↔
      start ≤ stop ∧ ∀ address, start ≤ address → address < stop → permission address = true := by
  simp only [permits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · intro ⟨valid, each⟩
    refine ⟨valid, fun address lower upper => ?_⟩
    have same : start + BitVec.ofNat 64 (address - start).toNat = address := by bv_omega
    rw [← same]
    exact each _ (by bv_omega)
  · intro ⟨valid, each⟩
    exact ⟨valid, fun offset bound => each _ (by bv_omega) (by bv_omega)⟩

/-- A permitted access does not wrap. -/
theorem permits_valid {permission : BitVec 64 → Bool} {start stop : BitVec 64}
    (allowed : permits permission start stop = true) : start ≤ stop :=
  ((permits_iff _ _ _).mp allowed).1

/-- A permission over a range holds over every subrange. -/
theorem permits_within {permission : BitVec 64 → Bool} {start stop first last : BitVec 64}
    (whole : permits permission start stop = true)
    (lower : start ≤ first) (valid : first ≤ last) (upper : last ≤ stop) :
    permits permission first last = true := by
  rw [permits_iff] at whole ⊢
  exact ⟨valid, fun address below above => whole.2 address (by bv_omega) (by bv_omega)⟩

/-! ## Reasoning about memory

A footprint is a set of addresses, `BitVec 64 → Prop`, such as
`fun x => output ≤ x ∧ x < outputEnd`. A read of `size` bytes from `address`
covers `[address, address + size)`; lemmas about it ask that this not wrap,
`address ≤ address + size`, which the read's own permission provides
(`permits_valid`), and that `size < 2^64`. -/

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

private theorem readBytes_congr {first second : BitVec 64 → Fin 256} {address : BitVec 64} {size : Nat}
    (same : ∀ offset < size, first (address + BitVec.ofNat 64 offset) = second (address + BitVec.ofNat 64 offset)) :
    readBytes first address size = readBytes second address size := by
  unfold readBytes
  rw [foldr_bytes (fun offset bound => congrArg Fin.val (same offset bound))]

/-- The addresses a non-wrapping read covers. -/
private theorem covered {address : BitVec 64} {size offset : Nat}
    (fits : address ≤ address + BitVec.ofNat 64 size) (small : size < 2^64) (bound : offset < size) :
    address ≤ address + BitVec.ofNat 64 offset ∧ address + BitVec.ofNat 64 offset < address + BitVec.ofNat 64 size := by
  bv_omega

/-- A read inside a store sees the stored bytes. -/
theorem Memory.readBytes_storeBytes_within (memory : Memory) (bytes : BitVec 64 → Fin 256)
    {start stop address : BitVec 64} {size : Nat}
    (lower : start ≤ address) (upper : address + BitVec.ofNat 64 size ≤ stop)
    (fits : address ≤ address + BitVec.ofNat 64 size) (small : size < 2^64) :
    readBytes (memory.storeBytes start stop bytes) address size = readBytes bytes address size := by
  apply readBytes_congr
  intro offset bound
  have ⟨above, below⟩ := covered fits small bound
  have inside : start ≤ address + BitVec.ofNat 64 offset ∧ address + BitVec.ofNat 64 offset < stop := by
    bv_omega
  simp only [Memory.read_storeBytes, inside, and_self, ↓reduceIte]

/-- A read outside a store sees the bytes from before it. -/
theorem Memory.readBytes_storeBytes_disjoint (memory : Memory) (bytes : BitVec 64 → Fin 256)
    {start stop address : BitVec 64} {size : Nat}
    (away : address + BitVec.ofNat 64 size ≤ start ∨ stop ≤ address)
    (fits : address ≤ address + BitVec.ofNat 64 size) (small : size < 2^64) :
    readBytes (memory.storeBytes start stop bytes) address size = readBytes memory address size := by
  apply readBytes_congr
  intro offset bound
  have ⟨above, below⟩ := covered fits small bound
  exact Memory.read_storeBytes_outside _ _ _ _ _ (by bv_omega)

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

/-- Reading a stored value back from byte `offset` on selects the corresponding bits. -/
theorem readBytes_littleEndianAt_add (value : BitVec n) (address : BitVec 64) (offset size : Nat)
    (fits : offset + size ≤ 2^64) :
    readBytes (littleEndianAt value address) (address + BitVec.ofNat 64 offset) size =
      value.extractLsb' (8 * offset) (8 * size) := by
  apply BitVec.eq_of_toNat_eq
  simp only [readBytes, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [foldr_bytes (second := fun index => value.toNat / 256^(offset + index) % 256) (fun index bound => by
    simp only [littleEndianAt]
    congr 3
    bv_omega)]
  rw [foldr_littleEndian, Nat.pow_mul, Nat.pow_mul]
  simp only [Nat.reducePow, Nat.mod_mod]

/-- Reading a stored value back from where it was stored gives its low bits. -/
@[simp] theorem readBytes_littleEndianAt (value : BitVec n) (address : BitVec 64) (size : Nat)
    (fits : size ≤ 2^64) :
    readBytes (littleEndianAt value address) address size = value.extractLsb' 0 (8 * size) := by
  simpa using readBytes_littleEndianAt_add value address 0 size (by omega)

/-- `after` holds the same bytes as `before` at every address outside `footprint`. -/
def Memory.SameOutside (before after : Memory) (footprint : BitVec 64 → Prop) : Prop :=
  ∀ address, ¬ footprint address → after address = before address

theorem Memory.SameOutside.refl (memory : Memory) (footprint : BitVec 64 → Prop) :
    memory.SameOutside memory footprint :=
  fun _ _ => rfl

theorem Memory.SameOutside.trans {first second third : Memory} {footprint : BitVec 64 → Prop}
    (earlier : first.SameOutside second footprint) (later : second.SameOutside third footprint) :
    first.SameOutside third footprint :=
  fun address outside => (later address outside).trans (earlier address outside)

/-- A footprint can always be enlarged. -/
theorem Memory.SameOutside.mono {before after : Memory} {footprint larger : BitVec 64 → Prop}
    (agree : before.SameOutside after footprint) (covered : ∀ address, footprint address → larger address) :
    before.SameOutside after larger :=
  fun address outside => agree address (fun inside => outside (covered address inside))

/-- A store inside the footprint keeps the agreement. -/
theorem Memory.SameOutside.storeBytes {before after : Memory} {footprint : BitVec 64 → Prop}
    (agree : before.SameOutside after footprint) {start stop : BitVec 64} (bytes : BitVec 64 → Fin 256)
    (inside : ∀ address, start ≤ address → address < stop → footprint address) :
    before.SameOutside (after.storeBytes start stop bytes) footprint := by
  intro address outside
  have away : ¬ (start ≤ address ∧ address < stop) := fun ⟨lower, upper⟩ => outside (inside address lower upper)
  simp only [Memory.read_storeBytes, away, ↓reduceIte]
  exact agree address outside

/-- The frame law: a read outside the footprint sees the original bytes. -/
theorem Memory.SameOutside.readBytes {before after : Memory} {footprint : BitVec 64 → Prop}
    (agree : before.SameOutside after footprint) {address : BitVec 64} {size : Nat}
    (away : ∀ other, address ≤ other → other < address + BitVec.ofNat 64 size → ¬ footprint other)
    (fits : address ≤ address + BitVec.ofNat 64 size) (small : size < 2^64) :
    Rivet.readBytes after address size = Rivet.readBytes before address size := by
  apply readBytes_congr
  intro offset bound
  have ⟨above, below⟩ := covered fits small bound
  exact agree _ (away _ above below)

/-! ## Building memory from regions -/

/-- The addresses `[start, stop)` with their contents, concrete or symbolic. The
importer emits each loadable segment of a binary as a region. -/
structure MemoryRegion where
  start : BitVec 64
  stop : BitVec 64
  contents : BitVec 64 → Fin 256 := fun _ => 0
  readable : Bool
  writable : Bool

def MemoryRegion.contains (region : MemoryRegion) (address : BitVec 64) : Bool :=
  region.start ≤ address && address < region.stop

/-- Two regions share no address. -/
def MemoryRegion.Disjoint (first second : MemoryRegion) : Prop :=
  first.stop ≤ first.start ∨ second.stop ≤ second.start ∨
    first.stop ≤ second.start ∨ second.stop ≤ first.start

/-- Memory laid out as regions. An address has a permission if a region containing
it grants one, and its byte comes from the first region containing it. Addresses
outside every region read zero and have no permissions. -/
def Memory.ofRegions (regions : List MemoryRegion) : Memory where
  bytes address := match regions.find? (·.contains address) with
    | some region => region.contents address
    | none => 0
  readable address := regions.any fun region => region.contains address && region.readable
  writable address := regions.any fun region => region.contains address && region.writable

/-! The lemmas below take `member : region ∈ regions` and read the region's fields
from it. State the region when proving membership:

    have input : ({ start := base, stop := limit, contents := bytes,
                    readable := true, writable := false } : MemoryRegion) ∈ regions := by
      simp [regions]
    have readable : permits (Memory.ofRegions regions).readable base limit = true :=
      Memory.permits_readable_ofRegions input valid -/

private theorem permits_ofRegions (regions : List MemoryRegion) (field : MemoryRegion → Bool)
    {region : MemoryRegion} (member : region ∈ regions) (allowed : field region = true)
    (valid : region.start ≤ region.stop) :
    permits (fun other => regions.any fun region => region.contains other && field region)
      region.start region.stop = true := by
  rw [permits_iff]
  refine ⟨valid, fun address lower upper => List.any_eq_true.mpr ⟨region, member, ?_⟩⟩
  simp [MemoryRegion.contains, allowed, lower, upper]

/-- A readable region is readable throughout; use `permits_within` for parts of it. -/
theorem Memory.permits_readable_ofRegions {regions : List MemoryRegion} {start stop : BitVec 64}
    {contents : BitVec 64 → Fin 256} {writable : Bool}
    (member : ⟨start, stop, contents, true, writable⟩ ∈ regions) (valid : start ≤ stop) :
    permits (Memory.ofRegions regions).readable start stop = true :=
  permits_ofRegions regions MemoryRegion.readable member rfl valid

/-- A writable region is writable throughout; use `permits_within` for parts of it. -/
theorem Memory.permits_writable_ofRegions {regions : List MemoryRegion} {start stop : BitVec 64}
    {contents : BitVec 64 → Fin 256} {readable : Bool}
    (member : ⟨start, stop, contents, readable, true⟩ ∈ regions) (valid : start ≤ stop) :
    permits (Memory.ofRegions regions).writable start stop = true :=
  permits_ofRegions regions MemoryRegion.writable member rfl valid

private theorem find_region {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {region : MemoryRegion} (member : region ∈ regions) {address : BitVec 64}
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
        bv_omega
    · simp only [List.find?_cons, Bool.not_eq_true] at here ⊢
      rw [here]
      rcases List.mem_cons.mp member with equal | later
      · rw [equal] at contains; simp [contains] at here
      · exact inductionHypothesis disjoint.2 later

private theorem any_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    (field : MemoryRegion → Bool) {region : MemoryRegion} (member : region ∈ regions) {address : BitVec 64}
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

private theorem contains_inside {start stop address : BitVec 64} {contents : BitVec 64 → Fin 256}
    {readable writable : Bool} (lower : start ≤ address) (upper : address < stop) :
    (⟨start, stop, contents, readable, writable⟩ : MemoryRegion).contains address = true := by
  simp [MemoryRegion.contains, lower, upper]

/-- Inside a region of a disjoint layout, memory holds the region's contents. -/
theorem Memory.read_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {start stop : BitVec 64} {contents : BitVec 64 → Fin 256} {readable writable : Bool}
    (member : ⟨start, stop, contents, readable, writable⟩ ∈ regions) {address : BitVec 64}
    (lower : start ≤ address) (upper : address < stop) :
    (Memory.ofRegions regions) address = contents address := by
  have found := find_region disjoint member (contains_inside (contents := contents) (readable := readable)
    (writable := writable) lower upper)
  simp only [Memory.ofRegions, found]

/-- Inside a region of a disjoint layout, an address is readable exactly when the region is. -/
theorem Memory.readable_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {start stop : BitVec 64} {contents : BitVec 64 → Fin 256} {readable writable : Bool}
    (member : ⟨start, stop, contents, readable, writable⟩ ∈ regions) {address : BitVec 64}
    (lower : start ≤ address) (upper : address < stop) :
    (Memory.ofRegions regions).readable address = readable :=
  any_ofRegions disjoint MemoryRegion.readable member (contains_inside lower upper)

/-- Inside a region of a disjoint layout, an address is writable exactly when the region is;
so read-only data is unwritable. -/
theorem Memory.writable_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {start stop : BitVec 64} {contents : BitVec 64 → Fin 256} {readable writable : Bool}
    (member : ⟨start, stop, contents, readable, writable⟩ ∈ regions) {address : BitVec 64}
    (lower : start ≤ address) (upper : address < stop) :
    (Memory.ofRegions regions).writable address = writable :=
  any_ofRegions disjoint MemoryRegion.writable member (contains_inside lower upper)

/-- A read inside a region of a disjoint layout sees the region's contents. -/
theorem Memory.readBytes_ofRegions {regions : List MemoryRegion} (disjoint : regions.Pairwise MemoryRegion.Disjoint)
    {start stop : BitVec 64} {contents : BitVec 64 → Fin 256} {readable writable : Bool}
    (member : ⟨start, stop, contents, readable, writable⟩ ∈ regions) {address : BitVec 64} {size : Nat}
    (lower : start ≤ address) (upper : address + BitVec.ofNat 64 size ≤ stop)
    (fits : address ≤ address + BitVec.ofNat 64 size) (small : size < 2^64) :
    readBytes (Memory.ofRegions regions) address size = readBytes contents address size := by
  apply readBytes_congr
  intro offset bound
  have ⟨above, below⟩ := covered fits small bound
  exact Memory.read_ofRegions disjoint member (by bv_omega) (by bv_omega)

end Rivet
