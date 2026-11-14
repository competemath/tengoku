import Tengoku.Twinprime.TwinPrime.Analytic.ComplexHyperbola
import Tengoku.Twinprime.TwinPrime.Analytic.ReciprocalPowerSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Power bounds for the zeta-convolution hyperbola remainder

These finite estimates transfer an explicit three-quarter-power summatory
bound to the short hyperbola strip and its overlap. The floor-tail estimate
uses the general `Nat.div_two_lt_floor` inequality at real endpoints.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The strip with constant outer coefficients costs a reciprocal-power sum.
@isnad1 id=le.5h4v.s8.d3de0637834d from=translated src=- shape=aa9aa18b vocab=1c202b86
-/
theorem norm_zeta_convolution_power_strip_le (f : ArithmeticFunction ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ u : ℝ, 1 ≤ u → ‖complexArithmeticSummatory f u‖ ≤ C * u ^ (3 / 4 : ℝ))
    (x z : ℝ) (hx : 1 ≤ x) (hz : 1 ≤ z) (hzx : z ≤ x) :
    ‖∑ d ∈ Ioc 0 ⌊z⌋₊, complexArithmeticSummatory f (x / d)‖ ≤
      4 * C * x ^ (3 / 4 : ℝ) * z ^ (1 / 4 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hrec := sum_Ioc_natFloor_rpow_neg_le z hz0 (3 / 4) (by norm_num) (by norm_num)
  norm_num only [show (1 - (3 / 4 : ℝ)) = 1 / 4 by norm_num] at hrec
  calc
    _ ≤ ∑ d ∈ Ioc 0 ⌊z⌋₊, ‖complexArithmeticSummatory f (x / d)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Ioc 0 ⌊z⌋₊, (C * x ^ (3 / 4 : ℝ)) * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
      have hdx : (d : ℝ) ≤ x :=
        (Nat.cast_le.mpr (mem_Ioc.mp hd).2).trans ((Nat.floor_le hz0).trans hzx)
      have hquot : 1 ≤ x / d := (le_div_iff₀ hd0).mpr (by simpa using hdx)
      apply (hA (x / d) hquot).trans_eq
      rw [Real.div_rpow hx0 hd0.le, Real.rpow_neg hd0.le]
      ring
    _ = (C * x ^ (3 / 4 : ℝ)) *
        (∑ d ∈ Ioc 0 ⌊z⌋₊, (d : ℝ) ^ (-(3 / 4 : ℝ))) := (mul_sum _ _ _).symm
    _ ≤ (C * x ^ (3 / 4 : ℝ)) * (z ^ (1 / 4 : ℝ) / (1 / 4)) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = _ := by ring

/-- The overlap keeps the natural floor coefficient and the real inner cutoff.
@isnad1 id=le.4h4v.s7.fb50abceb937 from=translated src=- shape=91742a50 vocab=b0a69499
-/
theorem natFloor_mul_norm_complexArithmeticSummatory_le (f : ArithmeticFunction ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ u : ℝ, 1 ≤ u → ‖complexArithmeticSummatory f u‖ ≤ C * u ^ (3 / 4 : ℝ))
    (y z : ℝ) (hy : 1 ≤ y) (hz : 0 ≤ z) :
    (⌊z⌋₊ : ℝ) * ‖complexArithmeticSummatory f y‖ ≤ C * z * y ^ (3 / 4 : ℝ) := by
  calc
    _ ≤ (⌊z⌋₊ : ℝ) * (C * y ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hA y hy) (Nat.cast_nonneg _)
    _ ≤ z * (C * y ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hz)
        (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
    _ = _ := by ring

/-- Flooring a positive real tail cutoff costs at most a factor two.
@isnad1 id=le.1h1v.s6.b737fd77adbf from=translated src=- shape=95adc12a vocab=ba6d5b61
-/
theorem natFloor_rpow_neg_quarter_le (y : ℝ) (hy : 1 ≤ y) :
    (⌊y⌋₊ : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 * y ^ (-(1 / 4 : ℝ)) := by
  have hy0 : 0 ≤ y := by linarith
  have hyhalf : 0 < y / 2 := by linarith
  have hfloor : y / 2 ≤ (⌊y⌋₊ : ℝ) := (Nat.div_two_lt_floor hy).le
  have htwo : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 / 4 : ℝ) ≤ 1))
  calc
    _ ≤ (y / 2) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hyhalf hfloor (by norm_num)
    _ = y ^ (-(1 / 4 : ℝ)) * (2 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.div_rpow hy0 (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul]
    _ ≤ y ^ (-(1 / 4 : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hy0 _)
    _ = _ := by ring

end TwinPrime.Analytic
