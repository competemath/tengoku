import Tengoku.Piirrationalitymeasure.Formalization.ConstructionCoefficientData
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Symbolic exponent collection in the general Mobius substitution (6.66). -/

namespace PiIrrationality

open HahnSeries PowerSeries

/--
@isnad1 id=eq.5h8v.s9.56c503b4604e from=translated src=- shape=561c6bfb vocab=1e38cfdd
-/
theorem construction_mobius_base_collect {K : Type*} [Field K] [CharZero K]
    (a b c : ℕ) (hc : Even c) (hab : c ≤ a + b) (hbc : 2 * c ≤ 4 * b)
    (U V x t : K) (hx : x ≠ 0) (ht : t ≠ 0) :
    (-5 * U / t) ^ (2 * a) * (400 * V / t ^ 4) ^ b /
      (-100 * x / t ^ 2) ^ c =
        (constructionCoefficientScale a b c : K) *
          (U ^ (2 * a) * V ^ b / t ^ (constructionDegree a b c)) / x ^ c := by
  have hdc : 2 * c ≤ 2 * a + 4 * b := by omega
  have h5 : (5 : K) ^ (2 * (a + b - c)) = 5 ^ (2 * a) * 5 ^ (2 * b) / 5 ^ (2 * c) := by
    apply (eq_div_iff (pow_ne_zero _ (by norm_num : (5 : K) ≠ 0))).mpr
    rw [← _root_.pow_add, ← _root_.pow_add]
    congr 1
    omega
  have h2 : (2 : K) ^ (4 * b - 2 * c) = 2 ^ (4 * b) / 2 ^ (2 * c) := by
    apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : K) ≠ 0))).mpr
    rw [← _root_.pow_add, Nat.sub_add_cancel hbc]
  have hd : t ^ (constructionDegree a b c) = t ^ (2 * a) * t ^ (4 * b) / t ^ (2 * c) := by
    apply (eq_div_iff (pow_ne_zero _ ht)).mpr
    rw [← _root_.pow_add, constructionDegree, Nat.sub_add_cancel hdc, _root_.pow_add]
  simp only [constructionCoefficientScale, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  rw [h5, h2, hd]
  simp only [div_pow, mul_pow]
  rw [(show Even (2 * a) from ⟨a, by omega⟩).neg_pow, hc.neg_pow,
    show (400 : K) = 2 ^ 4 * 5 ^ 2 by norm_num,
    show (100 : K) = 2 ^ 2 * 5 ^ 2 by norm_num]
  simp only [mul_pow, ← pow_mul]
  field_simp [ht, hx]

local instance : CharZero (LaurentSeries ℚ) := algebraRat.charZero _

/--
@isnad1 id=eq.0h3v.s11.0b2cca3ad8cc from=translated src=- shape=b644b50d vocab=42931201
-/
theorem constructionSeries_coe_formula (a b c : ℕ) :
    (constructionSeries a b c : LaurentSeries ℚ) =
      (1 + single 1 1) ^ (2 * a) *
        (2 + 6 * single 1 1 + 9 * single 1 1 ^ 2 +
          6 * single 1 1 ^ 3 + 2 * single 1 1 ^ 4) ^ b /
            (1 - single 1 1) ^ (constructionDegree a b c) := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
    (PositivePower.series_clearing_identity (2 * a) b (constructionDegree a b c))
  simp only [PSeries, map_mul, map_pow, map_add, map_sub, map_ofNat, map_one,
    HahnSeries.ofPowerSeries_X] at h
  exact (eq_div_iff (pow_ne_zero _ one_sub_laurentX_ne_zero)).mpr h

/--
@isnad1 id=eq.3h3v.s10.4df85ef10042 from=translated src=- shape=d34c9bfb vocab=1925b73f
-/
theorem constructionMobius_base_formula (a b c : ℕ) (hc : Even c)
    (hab : c ≤ a + b) (hbc : 2 * c ≤ 4 * b) :
    mobiusLaurent ^ (2 * a) * (mobiusLaurent ^ 4 + 6 * mobiusLaurent ^ 2 + 25) ^ b /
      (25 - mobiusLaurent ^ 2) ^ c =
        (constructionCoefficientScale a b c : LaurentSeries ℚ) *
          (constructionSeries a b c : LaurentSeries ℚ) / single 1 1 ^ c := by
  rw [constructionSeries_coe_formula, mobiusLaurent_quartic, mobiusLaurent_denominator]
  unfold mobiusLaurent
  exact construction_mobius_base_collect a b c hc hab hbc (1 + single 1 1)
    (2 + 6 * single 1 1 + 9 * single 1 1 ^ 2 + 6 * single 1 1 ^ 3 + 2 * single 1 1 ^ 4)
    (single 1 1) (1 - single 1 1) laurentX_ne_zero one_sub_laurentX_ne_zero

end PiIrrationality
