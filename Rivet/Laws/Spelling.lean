module
public import Rivet.Laws.SimpSet
meta import Lean
-- One spelling for what `rivet_step` states: conditions as comparisons, literal offsets
-- folded, and register parts read back as the value written. Rivet's tactics use these through the
-- `rivet` set; proofs never name them.
@[expose] public section
namespace Rivet.Internal

attribute [rivet] BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq
  BitVec.xor_self BitVec.and_self BitVec.setWidth_zero BitVec.sub_zero
  and_self Bool.false_eq_true Bool.true_eq_false
  decide_eq_true_eq decide_eq_false_iff_not beq_iff_eq beq_eq_false_iff_ne ne_eq Classical.not_not
  Bool.not_eq_true' Bool.and_eq_true Bool.or_eq_true BitVec.not_lt BitVec.not_le

-- A read of a register the step did not write skips the `if`s for the ones it did. Lean's own
-- `reduceCtorEq` and `reduceIte` are not `meta`, so a module cannot add them to a set directly.
simproc [rivet] distinctConstructors (_ = _) := reduceCtorEq
simproc ↓ [rivet] decidedIte (ite _ _ _) := reduceIte

-- Literals are evaluated: `8 + 56`, `16 % 32`, `8 ≤ 56`, `1#64 = 0#64`, `(65546#32).toInt`.
dsimproc [rivet] natAdd ((_ + _ : Nat)) := Nat.reduceAdd
dsimproc [rivet] natSub ((_ - _ : Nat)) := Nat.reduceSub
dsimproc [rivet] natMul ((_ * _ : Nat)) := Nat.reduceMul
dsimproc [rivet] natDiv ((_ / _ : Nat)) := Nat.reduceDiv
dsimproc [rivet] natMod ((_ % _ : Nat)) := Nat.reduceMod
dsimproc [rivet] natPow ((_ ^ _ : Nat)) := Nat.reducePow
-- A comparison of two literals is decided; nothing else is rearranged, which is `lia`'s work.
simproc [rivet] natLe ((_ : Nat) ≤ _) := fun e => do
  let_expr LE.le _ _ x y := e | return .continue
  let (some x, some y) := (← Lean.Meta.getNatValue? x, ← Lean.Meta.getNatValue? y) | return .continue
  Lean.Meta.Simp.evalPropStep e (x ≤ y)
simproc [rivet] natEq ((_ : Nat) = _) := fun e => do
  let_expr Eq _ x y := e | return .continue
  let (some x, some y) := (← Lean.Meta.getNatValue? x, ← Lean.Meta.getNatValue? y) | return .continue
  Lean.Meta.Simp.evalPropStep e (x = y)
dsimproc [rivet] wordOfNat (BitVec.ofNat _ _) := BitVec.reduceOfNat
dsimproc [rivet] wordAdd ((_ + _ : BitVec _)) := BitVec.reduceAdd
dsimproc [rivet] wordSetWidth (BitVec.setWidth _ _) := BitVec.reduceSetWidth
simproc [rivet] wordEq ((_ : BitVec _) = _) := BitVec.reduceEq
dsimproc [rivet] wordToInt (BitVec.toInt _) := BitVec.reduceToInt
attribute [rivet] BitVec.extractLsb'_eq_self

-- Literal displacements: `BitVec.ofInt 64 (-8)` becomes a subtraction of `8#64`, and a zero
-- displacement is dropped.
attribute [rivet] BitVec.ofInt_ofNat BitVec.ofInt_neg BitVec.add_neg_eq_sub
  BitVec.add_zero

@[rivet] theorem le_and_ne_iff_lt {a b : BitVec w} : (b ≤ a ∧ ¬a = b) ↔ b < a := by
  bv_omega
@[rivet] theorem lt_or_eq_iff_le {a b : BitVec w} : (a < b ∨ a = b) ↔ a ≤ b := by
  bv_omega

-- Signed conditions after a subtraction or comparison: SF = OF is `y ≤ x` as signed numbers.
attribute [rivet] bne_iff_ne Int.not_lt Int.not_le

@[rivet] theorem msb_sub_eq_ssubOverflow_iff (x y : BitVec w) :
    ((x - y).msb = x.ssubOverflow y) ↔ y.toInt ≤ x.toInt := by
  rcases w with _ | w
  · simp [BitVec.of_length_zero, BitVec.ssubOverflow]
  have below := @BitVec.toInt_sub_toInt_lt_twoPow_iff (w + 1) x y
  have above := @BitVec.twoPow_le_toInt_sub_toInt_iff (w + 1) x y
  have inside (low : -(2 : Int) ^ w ≤ x.toInt - y.toInt) (high : x.toInt - y.toInt < 2 ^ w) :
      (x - y).toInt = x.toInt - y.toInt := by
    rw [BitVec.toInt_sub]
    apply Int.bmod_eq_of_le_mul_two <;> push_cast [Nat.pow_succ] <;> omega
  rw [← BitVec.toInt_sub, Nat.add_one_sub_one] at below above
  rw [BitVec.msb_eq_toInt, BitVec.ssubOverflow, Nat.add_one_sub_one]
  by_cases low : -(2 : Int) ^ w ≤ x.toInt - y.toInt <;> by_cases high : x.toInt - y.toInt < 2 ^ w
  all_goals rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.or_eq_true]
  · rw [inside low high]; omega
  all_goals omega
@[rivet] theorem msb_eq_ssubOverflow_zero_iff (x : BitVec w) :
    (x.msb = x.ssubOverflow 0#w) ↔ 0 ≤ x.toInt := by
  simpa using msb_sub_eq_ssubOverflow_iff x 0

@[rivet] theorem toInt_lt_or_eq_iff_le {x y : BitVec w} : (x.toInt < y.toInt ∨ x = y) ↔ x.toInt ≤ y.toInt := by
  rw [← BitVec.toInt_inj]; omega
@[rivet] theorem toInt_le_and_ne_iff_lt {x y : BitVec w} : (y.toInt ≤ x.toInt ∧ ¬x = y) ↔ y.toInt < x.toInt := by
  rw [← BitVec.toInt_inj]; omega
-- The same, where one side is a literal and its `toInt` is already a number.
@[rivet] theorem toInt_lt_or_eq_iff_le_right {x y : BitVec w} {c : Int} (value : y.toInt = c) :
    (x.toInt < c ∨ x = y) ↔ x.toInt ≤ c := by
  subst value; exact toInt_lt_or_eq_iff_le
@[rivet] theorem toInt_lt_or_eq_iff_le_left {x y : BitVec w} {c : Int} (value : x.toInt = c) :
    (c < y.toInt ∨ x = y) ↔ c ≤ y.toInt := by
  subst value; exact toInt_lt_or_eq_iff_le
@[rivet] theorem toInt_le_and_ne_iff_lt_right {x y : BitVec w} {c : Int} (value : y.toInt = c) :
    (c ≤ x.toInt ∧ ¬x = y) ↔ c < x.toInt := by
  subst value; exact toInt_le_and_ne_iff_lt
@[rivet] theorem toInt_le_and_ne_iff_lt_left {x y : BitVec w} {c : Int} (value : x.toInt = c) :
    (y.toInt ≤ c ∧ ¬x = y) ↔ y.toInt < c := by
  subst value; exact toInt_le_and_ne_iff_lt

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

end Rivet.Internal
