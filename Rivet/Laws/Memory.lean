module
public import Rivet.Interpreter.Memory
public import Rivet.Tactics.Arith
import all Rivet.Interpreter.Memory
-- Laws of flat memory: stores and little-endian reads. A range is an interval of `toNat` values. A
-- read that ends past 2^64 wraps around, so the laws about reads ask it not to. Every bound is an
-- argument you give.
@[expose] public section
namespace Rivet

-- An offset is a plain number; inside an address it is `BitVec.ofNat 64 offset`, which `lia` reads
-- through this theorem.
@[lia =] theorem toNat_ofNat_of_lt {w n : Nat} (small : n < 2^w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

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

private theorem Memory.read_storeBytes_outside {memory : Memory} {base : BitVec 64} {length : Nat} {bytes : Memory}
    {address : BitVec 64}
    (outside : address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat) :
    (memory.storeBytes base length bytes) address = memory address := by
  have away : ¬ (base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + length) := by omega
  simp only [Memory.storeBytes, away, ↓reduceIte]

theorem Memory.readBytes_storeBytes_inside (memory : Memory) (bytes : Memory)
    {base address : BitVec 64} {length size : Nat}
    (start : base.toNat ≤ address.toNat)
    (finish : address.toNat + size ≤ base.toNat + length)
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

private theorem readBytes_littleEndianAt_add (value : BitVec n) (address : BitVec 64) (offset size : Nat)
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

theorem readBytes_littleEndianAt (value : BitVec n) {base address : BitVec 64} {size : Nat} (offset : Nat)
    (start : address.toNat = base.toNat + offset)
    (fits : address.toNat + size ≤ 2^64) :
    readBytes (littleEndianAt value base) address size = value.extractLsb' (8 * offset) (8 * size) := by
  rw [show address = base + BitVec.ofNat 64 offset by bv_omega]
  exact readBytes_littleEndianAt_add value base offset size (by omega)

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

end Rivet
