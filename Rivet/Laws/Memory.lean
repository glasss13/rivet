module
public import Rivet.Interpreter.Memory
import all Rivet.Interpreter.Memory
-- Laws of memory: stores, little-endian reads, permissions, and frames.
@[expose] public section
namespace Rivet

theorem Memory.read_storeBytes_outside {memory : Memory} {base length : BitVec 64} {bytes : Memory}
    {address : BitVec 64} (outside : length ≤ address - base) :
    (memory.storeBytes base length bytes) address = memory address := by
  have away : ¬ address - base < length := by bv_omega
  simp only [Memory.storeBytes, away, ↓reduceIte]

theorem permits_iff {permission : BitVec 64 → Bool} {base length : BitVec 64} :
    permits permission base length = true ↔
      base ≤ base + length ∧ ∀ address, address - base < length → permission address = true := by
  simp only [permits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · intro ⟨valid, each⟩
    refine ⟨valid, fun address inside => ?_⟩
    have same : base + BitVec.ofNat 64 (address - base).toNat = address := by bv_omega
    rw [← same]
    exact each _ (by bv_omega)
  · intro ⟨valid, each⟩
    exact ⟨valid, fun offset bound => each _ (by bv_omega)⟩

/-- A permission over a range holds over every range inside it. -/
theorem permits_inside {permission : BitVec 64 → Bool} {base length first size : BitVec 64}
    (whole : permits permission base length = true)
    (fits : size ≤ length) (inside : first - base ≤ length - size) :
    permits permission first size = true := by
  rw [permits_iff] at whole ⊢
  exact ⟨by bv_omega, fun address within => whole.2 address (by bv_omega)⟩

/-! ## Reasoning about memory

A footprint is a set of addresses, `BitVec 64 → Prop`, such as
`fun x => x - output < length`. A read of `size` bytes from `address` covers the
addresses `x` with `x - address < BitVec.ofNat 64 size`; lemmas about it ask that
`size < 2^64`, proved by `decide` unless given. -/

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

private theorem readBytes_offsets_congr {first second : Memory} {address : BitVec 64} {size : Nat}
    (same : ∀ offset < size, first (address + BitVec.ofNat 64 offset) = second (address + BitVec.ofNat 64 offset)) :
    readBytes first address size = readBytes second address size := by
  unfold readBytes
  rw [foldr_bytes (fun offset bound => congrArg Fin.val (same offset bound))]

/-- The addresses a read covers. -/
private theorem covered {address : BitVec 64} {size offset : Nat}
    (small : size < 2^64) (bound : offset < size) :
    address + BitVec.ofNat 64 offset - address < BitVec.ofNat 64 size := by
  bv_omega

/-- Memories that agree on the addresses a read covers give the same read. -/
theorem readBytes_congr {first second : Memory} {address : BitVec 64} {size : Nat}
    (agree : ∀ other, other - address < BitVec.ofNat 64 size → first other = second other)
    (small : size < 2^64 := by decide) :
    readBytes first address size = readBytes second address size := by
  apply readBytes_offsets_congr
  intro offset bound
  exact agree _ (covered small bound)

/-- A read inside a store sees the stored bytes. -/
theorem Memory.readBytes_storeBytes_within (memory : Memory) (bytes : Memory)
    {base length address : BitVec 64} {size : Nat}
    (fits : BitVec.ofNat 64 size ≤ length) (inside : address - base ≤ length - BitVec.ofNat 64 size)
    (small : size < 2^64 := by decide) :
    readBytes (memory.storeBytes base length bytes) address size = readBytes bytes address size := by
  apply readBytes_offsets_congr
  intro offset bound
  have within := covered (address := address) small bound
  have stored : address + BitVec.ofNat 64 offset - base < length := by bv_omega
  simp only [Memory.storeBytes, stored, ↓reduceIte]

/-- Two ranges are disjoint exactly when each one's length is at most the distance
from its base to the other's base. A read disjoint from a store sees the bytes from
before it. -/
theorem Memory.readBytes_storeBytes_disjoint (memory : Memory) (bytes : Memory)
    {base length address : BitVec 64} {size : Nat}
    (before : length ≤ address - base) (after : BitVec.ofNat 64 size ≤ base - address)
    (small : size < 2^64 := by decide) :
    readBytes (memory.storeBytes base length bytes) address size = readBytes memory address size := by
  apply readBytes_offsets_congr
  intro offset bound
  have within := covered (address := address) small bound
  exact Memory.read_storeBytes_outside (by bv_omega)

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

/-- A one-byte read is the byte at that address. Not a simp lemma: it would turn a byte
read of a store into a point read before the store laws apply. -/
theorem readBytes_one (memory : Memory) (address : BitVec 64) :
    readBytes memory address 1 = BitVec.ofNat 8 (memory address).val := by
  simp [readBytes]

/-- The byte a stored value puts at `address + offset` is the value's byte `offset`. -/
theorem littleEndianAt_add (value : BitVec n) (address : BitVec 64) (offset : Nat)
    (small : offset < 2^64 := by decide) :
    (littleEndianAt value address (address + BitVec.ofNat 64 offset)).val =
      (value.extractLsb' (8 * offset) 8).toNat := by
  have distance : (address + BitVec.ofNat 64 offset - address).toNat = offset := by
    bv_omega
  simp only [littleEndianAt, distance, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- The byte a stored value puts at its own address is the value's lowest byte. -/
@[simp] theorem littleEndianAt_self (value : BitVec n) (address : BitVec 64) :
    (littleEndianAt value address address).val = (value.extractLsb' 0 8).toNat := by
  simpa using littleEndianAt_add value address 0

/-- `after` holds the same bytes as `before` at every address outside `footprint`. -/
def Memory.SameOutside (before after : Memory) (footprint : BitVec 64 → Prop) : Prop :=
  ∀ address, ¬ footprint address → after address = before address

theorem Memory.SameOutside.refl {memory : Memory} {footprint : BitVec 64 → Prop} :
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
    (agree : before.SameOutside after footprint) {base length : BitVec 64} {bytes : Memory}
    (inside : ∀ address, address - base < length → footprint address) :
    before.SameOutside (after.storeBytes base length bytes) footprint := by
  intro address outside
  have away : ¬ address - base < length := fun within => outside (inside address within)
  simp only [Memory.storeBytes, away, ↓reduceIte]
  exact agree address outside

/-- The frame law: a read outside the footprint sees the original bytes. -/
theorem Memory.SameOutside.readBytes {before after : Memory} {footprint : BitVec 64 → Prop}
    (agree : before.SameOutside after footprint) {address : BitVec 64} {size : Nat}
    (away : ∀ other, other - address < BitVec.ofNat 64 size → ¬ footprint other)
    (small : size < 2^64 := by decide) :
    Rivet.readBytes after address size = Rivet.readBytes before address size := by
  apply readBytes_offsets_congr
  intro offset bound
  exact agree _ (away _ (covered small bound))

end Rivet
