module
public import Rivet.Laws.SimpSet
-- One spelling for what `rivet_step` states: conditions as comparisons, literal offsets
-- folded, and register parts read back as the value written.
@[expose] public section
namespace Rivet

attribute [rivet] BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq
  BitVec.xor_self BitVec.and_self BitVec.setWidth_zero BitVec.sub_zero
  BitVec.shiftLeft_zero BitVec.ushiftRight_zero
  eq_self_iff_true and_self Bool.false_eq_true Bool.true_eq_false
  decide_eq_true_eq decide_eq_false_iff_not beq_iff_eq beq_eq_false_iff_ne ne_eq Classical.not_not
  Bool.not_eq_true' Bool.and_eq_true Bool.or_eq_true BitVec.not_lt BitVec.not_le

-- Literal displacements: `BitVec.ofInt 64 (-8)` becomes a subtraction of `8#64`, and a zero
-- displacement is dropped.
attribute [rivet] BitVec.ofInt_ofNat BitVec.ofInt_neg BitVec.ofInt_natCast BitVec.add_neg_eq_sub
  BitVec.add_zero

@[rivet] theorem le_and_ne_iff_lt {a b : BitVec w} : (b ≤ a ∧ ¬a = b) ↔ b < a := by
  bv_omega
@[rivet] theorem lt_or_eq_iff_le {a b : BitVec w} : (a < b ∨ a = b) ↔ a ≤ b := by
  bv_omega

@[rivet] theorem sub_ofNat_sub_ofNat (x : BitVec w) (a b : Nat) :
    x - BitVec.ofNat w a - BitVec.ofNat w b = x - BitVec.ofNat w (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]
@[rivet] theorem add_ofNat_add_ofNat (x : BitVec w) (a b : Nat) :
    x + BitVec.ofNat w a + BitVec.ofNat w b = x + BitVec.ofNat w (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
@[rivet] theorem add_ofNat_sub_ofNat_of_le (x : BitVec w) {a b : Nat} (le : b ≤ a) :
    x + BitVec.ofNat w a - BitVec.ofNat w b = x + BitVec.ofNat w (a - b) := by
  rw [← Nat.sub_add_cancel le, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel,
    Nat.add_sub_cancel]
@[rivet] theorem add_ofNat_sub_ofNat_of_ge (x : BitVec w) {a b : Nat} (ge : a ≤ b) :
    x + BitVec.ofNat w a - BitVec.ofNat w b = x - BitVec.ofNat w (b - a) := by
  rw [← Nat.sub_add_cancel ge, ← BitVec.ofNat_add_ofNat, Nat.add_sub_cancel]
  grind
@[rivet] theorem sub_ofNat_add_ofNat_of_le (x : BitVec w) {a b : Nat} (le : b ≤ a) :
    x - BitVec.ofNat w a + BitVec.ofNat w b = x - BitVec.ofNat w (a - b) := by
  rw [← Nat.sub_add_cancel le, ← BitVec.ofNat_add_ofNat, Nat.add_sub_cancel]
  grind
@[rivet] theorem sub_ofNat_add_ofNat_of_ge (x : BitVec w) {a b : Nat} (ge : a ≤ b) :
    x - BitVec.ofNat w a + BitVec.ofNat w b = x + BitVec.ofNat w (b - a) := by
  rw [← Nat.sub_add_cancel ge, ← BitVec.ofNat_add_ofNat, Nat.add_sub_cancel]
  grind

@[rivet] theorem read_low_byte (register : BitVec 64) (value : BitVec 8) :
    (register &&& ~~~255#64 ||| value.setWidth 64).setWidth 8 = value := by
  ext i; simp
@[rivet] theorem write_low_byte_twice (register : BitVec 64) (first second : BitVec 8) :
    (register &&& ~~~255#64 ||| first.setWidth 64) &&& ~~~255#64 ||| second.setWidth 64 =
      register &&& ~~~255#64 ||| second.setWidth 64 := by
  ext i size
  have mask : (~~~255#64 : BitVec 64)[i] = decide (8 ≤ i) := by
    have : ∀ i (size : i < 64), (~~~255#64 : BitVec 64)[i] = decide (8 ≤ i) := by decide
    exact this i size
  simp only [BitVec.getElem_or, BitVec.getElem_and, mask, BitVec.getElem_setWidth]
  by_cases high : 8 ≤ i <;> simp [high, BitVec.getLsbD_of_ge]
@[rivet] theorem read_low_word (register : BitVec 64) (value : BitVec 16) :
    (register &&& ~~~65535#64 ||| value.setWidth 64).setWidth 16 = value := by
  ext i; simp
@[rivet] theorem write_low_word_twice (register : BitVec 64) (first second : BitVec 16) :
    (register &&& ~~~65535#64 ||| first.setWidth 64) &&& ~~~65535#64 ||| second.setWidth 64 =
      register &&& ~~~65535#64 ||| second.setWidth 64 := by
  ext i size
  have mask : (~~~65535#64 : BitVec 64)[i] = decide (16 ≤ i) := by
    have : ∀ i (size : i < 64), (~~~65535#64 : BitVec 64)[i] = decide (16 ≤ i) := by decide
    exact this i size
  simp only [BitVec.getElem_or, BitVec.getElem_and, mask, BitVec.getElem_setWidth]
  by_cases high : 16 ≤ i <;> simp [high, BitVec.getLsbD_of_ge]

@[rivet] theorem setcc_eq_zero {condition : Prop} [Decidable condition] :
    ((if condition then 1 else 0 : BitVec 8) = 0) ↔ ¬condition := by
  split <;> simp_all

end Rivet
