module
public import Rivet.Interpreter.Memory
import all Rivet.Interpreter.Memory
-- Laws of memory: permissions, stores, little-endian reads, and frames. A range is an interval of
-- `toNat` values. A read that ends past 2^64 wraps around, so the laws about reads ask it not to.
@[expose] public section
namespace Rivet

theorem permits_iff {permission : BitVec 64 → Bool} {base : BitVec 64} {length : Nat} :
    permits permission base length = true ↔
      base.toNat + length ≤ 2^64 ∧
        ∀ address, base.toNat ≤ address.toNat → address.toNat < base.toNat + length → permission address = true := by
  simp only [permits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · intro ⟨fits, each⟩
    refine ⟨fits, fun address start finish => ?_⟩
    have same : base + BitVec.ofNat 64 (address.toNat - base.toNat) = address := by bv_omega
    rw [← same]
    exact each _ (by omega)
  · intro ⟨fits, each⟩
    exact ⟨fits, fun offset bound => each _ (by bv_omega) (by bv_omega)⟩

theorem permits_inside {permission : BitVec 64 → Bool} {base first : BitVec 64} {length size : Nat}
    (whole : permits permission base length = true)
    (start : base.toNat ≤ first.toNat) (finish : first.toNat + size ≤ base.toNat + length) :
    permits permission first size = true := by
  rw [permits_iff] at whole ⊢
  exact ⟨by omega, fun address low high => whole.2 address (by omega) (by omega)⟩

abbrev Region.Covers (region : Region) (address : BitVec 64) (size : Nat) : Prop :=
  region.base ≤ address.toNat ∧ address.toNat + size ≤ region.base + region.length

theorem Region.Covers.toNat_add {region : Region} {address : BitVec 64} {size offset : Nat}
    (covers : region.Covers address size) (inside : offset < size) :
    (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
  have := region.fits
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

theorem Image.permits_readable {image : Image} {region : Region} {address : BitVec 64} {size : Nat}
    (member : region ∈ image.regions) (readable : region.readable = true) (covers : region.Covers address size) :
    permits image.readable address size = true := by
  rw [permits_iff]
  refine ⟨by have := region.fits; omega, fun other start finish => ?_⟩
  simp only [Image.readable, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨region, member, readable, by simp only [Region.Contains]; omega⟩

theorem Image.permits_writable {image : Image} {region : Region} {address : BitVec 64} {size : Nat}
    (member : region ∈ image.regions) (writable : region.writable = true) (covers : region.Covers address size) :
    permits image.writable address size = true := by
  rw [permits_iff]
  refine ⟨by have := region.fits; omega, fun other start finish => ?_⟩
  simp only [Image.writable, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨region, member, writable, by simp only [Region.Contains]; omega⟩

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

theorem readBytes_congr {first second : Memory} {address : BitVec 64} {size : Nat}
    (agree : ∀ other, address.toNat ≤ other.toNat → other.toNat < address.toNat + size → first other = second other)
    (fits : address.toNat + size ≤ 2^64) :
    readBytes first address size = readBytes second address size := by
  apply readBytes_offsets_congr
  intro offset bound
  exact agree _ (by bv_omega) (by bv_omega)

theorem Memory.read_storeBytes_outside {memory : Memory} {base : BitVec 64} {length : Nat} {bytes : Memory}
    {address : BitVec 64} (outside : address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat) :
    (memory.storeBytes base length bytes) address = memory address := by
  have away : ¬ (base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + length) := by omega
  simp only [Memory.storeBytes, away, ↓reduceIte]

theorem Memory.readBytes_storeBytes_inside (memory : Memory) (bytes : Memory)
    {base address : BitVec 64} {length size : Nat}
    (start : base.toNat ≤ address.toNat) (finish : address.toNat + size ≤ base.toNat + length)
    (fits : address.toNat + size ≤ 2^64) :
    readBytes (memory.storeBytes base length bytes) address size = readBytes bytes address size := by
  apply readBytes_offsets_congr
  intro offset bound
  have stored : base.toNat ≤ (address + BitVec.ofNat 64 offset).toNat ∧
      (address + BitVec.ofNat 64 offset).toNat < base.toNat + length := by bv_omega
  simp only [Memory.storeBytes, stored, and_self, ↓reduceIte]

theorem Memory.readBytes_storeBytes_outside (memory : Memory) (bytes : Memory)
    {base address : BitVec 64} {length size : Nat}
    (outside : address.toNat + size ≤ base.toNat ∨ base.toNat + length ≤ address.toNat)
    (fits : address.toNat + size ≤ 2^64) :
    readBytes (memory.storeBytes base length bytes) address size = readBytes memory address size := by
  apply readBytes_offsets_congr
  intro offset bound
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

@[simp] theorem readBytes_littleEndianAt (value : BitVec n) (address : BitVec 64) (size : Nat)
    (fits : size ≤ 2^64) :
    readBytes (littleEndianAt value address) address size = value.extractLsb' 0 (8 * size) := by
  simpa using readBytes_littleEndianAt_add value address 0 size (by omega)

theorem readBytes_one (memory : Memory) (address : BitVec 64) :
    readBytes memory address 1 = BitVec.ofNat 8 (memory address).val := by
  simp [readBytes]

private theorem foldr_bytes_lt {byte : Nat → Nat} (offsets : List Nat) (small : ∀ offset, byte offset < 256) :
    offsets.foldr (fun offset value => byte offset + 256 * value) 0 < 256 ^ offsets.length := by
  induction offsets with
  | nil => simp
  | cons offset rest inductionHypothesis =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    have := small offset
    omega

private theorem readBytes_succ_toNat (memory : Memory) (address : BitVec 64) (size : Nat) :
    (readBytes memory address (size + 1)).toNat =
      (memory address).val + 256 * (readBytes memory (address + 1#64) size).toNat := by
  have small : ∀ (start : BitVec 64) (offset : Nat), (memory (start + BitVec.ofNat 64 offset)).val < 256 :=
    fun _ _ => (memory _).isLt
  simp only [readBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by simpa [Nat.pow_mul] using foldr_bytes_lt (List.range (size + 1)) (small address)),
    Nat.mod_eq_of_lt (by simpa [Nat.pow_mul] using foldr_bytes_lt (List.range size) (small (address + 1#64))),
    List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
  simp only [BitVec.add_zero]
  congr 2
  apply foldr_bytes
  intro offset _
  congr 2
  bv_omega

theorem readBytes_succ (memory : Memory) (address : BitVec 64) (size : Nat) :
    readBytes memory address (size + 1) =
      readBytes memory (address + 1#64) size ++ BitVec.ofNat 8 (memory address).val := by
  apply BitVec.eq_of_toNat_eq
  have byte := (memory address).isLt
  rw [readBytes_succ_toNat, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

theorem littleEndianAt_add (value : BitVec n) (address : BitVec 64) (offset : Nat)
    (small : offset < 2^64 := by decide) :
    (littleEndianAt value address (address + BitVec.ofNat 64 offset)).val =
      (value.extractLsb' (8 * offset) 8).toNat := by
  have distance : (address + BitVec.ofNat 64 offset - address).toNat = offset := by
    bv_omega
  simp only [littleEndianAt, distance, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

@[simp] theorem littleEndianAt_self (value : BitVec n) (address : BitVec 64) :
    (littleEndianAt value address address).val = (value.extractLsb' 0 8).toNat := by
  simpa using littleEndianAt_add value address 0

def Memory.SameOutside (before after : Memory) (footprint : BitVec 64 → Prop) : Prop :=
  ∀ address, ¬ footprint address → after address = before address

theorem Memory.SameOutside.refl {memory : Memory} {footprint : BitVec 64 → Prop} :
    memory.SameOutside memory footprint :=
  fun _ _ => rfl

theorem Memory.SameOutside.trans {first second third : Memory} {footprint : BitVec 64 → Prop}
    (earlier : first.SameOutside second footprint) (later : second.SameOutside third footprint) :
    first.SameOutside third footprint :=
  fun address outside => (later address outside).trans (earlier address outside)

theorem Memory.SameOutside.mono {before after : Memory} {footprint larger : BitVec 64 → Prop}
    (agree : before.SameOutside after footprint) (covered : ∀ address, footprint address → larger address) :
    before.SameOutside after larger :=
  fun address outside => agree address (fun inside => outside (covered address inside))

theorem Memory.SameOutside.storeBytes {before after : Memory} {footprint : BitVec 64 → Prop}
    (agree : before.SameOutside after footprint) {base : BitVec 64} {length : Nat} {bytes : Memory}
    (inside : ∀ address, base.toNat ≤ address.toNat → address.toNat < base.toNat + length → footprint address) :
    before.SameOutside (after.storeBytes base length bytes) footprint := by
  intro address outside
  have away : ¬ (base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + length) :=
    fun ⟨start, finish⟩ => outside (inside address start finish)
  simp only [Memory.storeBytes, away, ↓reduceIte]
  exact agree address outside

theorem Memory.SameOutside.readBytes {before after : Memory} {footprint : BitVec 64 → Prop}
    (agree : before.SameOutside after footprint) {address : BitVec 64} {size : Nat}
    (away : ∀ other, address.toNat ≤ other.toNat → other.toNat < address.toNat + size → ¬ footprint other)
    (fits : address.toNat + size ≤ 2^64) :
    Rivet.readBytes after address size = Rivet.readBytes before address size := by
  apply readBytes_offsets_congr
  intro offset bound
  exact agree _ (away _ (by bv_omega) (by bv_omega))

end Rivet
