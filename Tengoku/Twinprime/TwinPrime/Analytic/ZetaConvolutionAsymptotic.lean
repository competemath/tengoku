import Tengoku.Twinprime.TwinPrime.Analytic.ZetaConvolutionHyperbola
import Tengoku.Twinprime.TwinPrime.Analytic.PowerDirichletContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaConvolutionPowerBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An explicit main term for a zeta convolution

A three-quarter-power cancellation bound gives an actual ordered reciprocal
limit. Together with an absolute coefficient-mass bound, the finite hyperbola
identity yields an explicit four-fifths-power error about that limit.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.0h2v.s5.dfeb72d4b45f from=translated src=- shape=8924a20c vocab=bcf8b4e7
-/
theorem powerDirichletPartialSum_one_eq (a : ℕ → ℂ) (N : ℕ) :
    powerDirichletPartialSum a 1 N = ∑ n ∈ Ioc 0 N, a n / (n : ℂ) := by
  simp only [powerDirichletPartialSum, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]

/--
@isnad1 id=le.1h3v.s7.12a5ef5102d1 from=translated src=- shape=4a854fa7 vocab=fc7f570f
-/
theorem norm_prefix_le_three_quarter_power_of_real_bound (f : ArithmeticFunction ℂ)
    (C : ℝ)
    (hA : ∀ x : ℝ, 1 ≤ x →
      ‖complexArithmeticSummatory f x‖ ≤ C * x ^ (3 / 4 : ℝ)) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, f n‖ ≤ C * (N : ℝ) ^ (3 / 4 : ℝ) := by
  by_cases hN : N = 0
  · simp [hN]
  · simpa only [complexArithmeticSummatory_nat] using
      hA N (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)

/--
@isnad1 id=le.3h3v.s7.6eb600d1a2e8 from=translated src=- shape=44b5c47d vocab=bfc59c82
-/
theorem norm_reciprocal_sum_sub_powerDirichletLimit_le (f : ArithmeticFunction ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x : ℝ, 1 ≤ x →
      ‖complexArithmeticSummatory f x‖ ≤ C * x ^ (3 / 4 : ℝ))
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Ioc 0 N, f n / (n : ℂ)) - powerDirichletLimit f 1‖ ≤
      10 * C * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  calc
    _ = ‖powerDirichletLimit f 1 - powerDirichletPartialSum f 1 N‖ := by
      rw [powerDirichletPartialSum_one_eq, norm_sub_rev]
    _ ≤ (2 * C) * (N : ℝ) ^ ((3 / 4 : ℝ) - (1 : ℂ).re) *
        (1 + ‖(1 : ℂ)‖ / ((1 : ℂ).re - (3 / 4 : ℝ))) :=
      norm_powerDirichletLimit_sub_partialSum_le (3 / 4) (by norm_num) f C hC
        (norm_prefix_le_three_quarter_power_of_real_bound f C hA) N hN 1 (by norm_num)
    _ = _ := by norm_num; ring

/--
@isnad1 id=le.3h3v.s7.ff20a04db82a from=translated src=- shape=c857698b vocab=afe0ea3e
-/
theorem norm_reciprocal_sum_natFloor_sub_powerDirichletLimit_le
    (f : ArithmeticFunction ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x : ℝ, 1 ≤ x →
      ‖complexArithmeticSummatory f x‖ ≤ C * x ^ (3 / 4 : ℝ))
    (y : ℝ) (hy : 1 ≤ y) :
    ‖(∑ n ∈ Ioc 0 ⌊y⌋₊, f n / (n : ℂ)) - powerDirichletLimit f 1‖ ≤
      20 * C * y ^ (-(1 / 4 : ℝ)) := by
  calc
    _ ≤ 10 * C * (⌊y⌋₊ : ℝ) ^ (-(1 / 4 : ℝ)) :=
      norm_reciprocal_sum_sub_powerDirichletLimit_le f C hC hA ⌊y⌋₊
        (Nat.floor_pos.mpr hy)
    _ ≤ 10 * C * (2 * y ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left (natFloor_rpow_neg_quarter_le y hy) (by positivity)
    _ = _ := by ring

/-- The main coefficient is the actual ordered reciprocal limit, constructed
from the cancellation hypothesis. No asymptotic formula is assumed.
@isnad1 id=le.4h3v.s8.6378d69d35c2 from=translated src=- shape=23adf583 vocab=3518019c
-/
theorem norm_zeta_convolution_sub_powerDirichletLimit_le
    (f : ArithmeticFunction ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x : ℝ, 1 ≤ x →
      ‖complexArithmeticSummatory f x‖ ≤ C * x ^ (3 / 4 : ℝ))
    (hMass : ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Ioc 0 ⌊x⌋₊, ‖f n‖) ≤ x * (1 + Real.log x) ^ 2)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory (f * ArithmeticFunction.zeta) x -
      (x : ℂ) * powerDirichletLimit f 1‖ ≤
        (1 + 25 * C) * x ^ (4 / 5 : ℝ) * (1 + Real.log x) ^ 2 := by
  let y : ℝ := x ^ (4 / 5 : ℝ)
  let z : ℝ := x ^ (1 / 5 : ℝ)
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hy : 1 ≤ y := Real.one_le_rpow hx (by norm_num)
  have hz : 1 ≤ z := Real.one_le_rpow hx (by norm_num)
  have hy0 : 0 ≤ y := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hyx : y ≤ x := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (4 / 5 : ℝ) ≤ 1))
  have hzx : z ≤ x := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 / 5 : ℝ) ≤ 1))
  have hyz : y * z = x := by
    dsimp [y, z]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hBpower : x ^ (3 / 4 : ℝ) * z ^ (1 / 4 : ℝ) = y := by
    dsimp [y, z]
    rw [← Real.rpow_mul hx0, ← Real.rpow_add hxpos]
    norm_num
  have hOpower : z * y ^ (3 / 4 : ℝ) = y := by
    dsimp [y, z]
    rw [← Real.rpow_mul hx0, ← Real.rpow_add hxpos]
    norm_num
  have hTpower : x * y ^ (-(1 / 4 : ℝ)) = y := by
    calc
      _ = x ^ (1 : ℝ) * (x ^ (4 / 5 : ℝ)) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.rpow_one]
      _ = y := by
        rw [← Real.rpow_mul hx0, ← Real.rpow_add hxpos]
        norm_num [y]
  have hhead : (∑ n ∈ Ioc 0 ⌊y⌋₊, ‖f n‖) ≤ y * (1 + Real.log x) ^ 2 := by
    apply (hMass y hy).trans
    have hlog : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hyx
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hy]) (by linarith) 2) hy0
  have hstrip : ‖∑ d ∈ Ioc 0 ⌊z⌋₊, complexArithmeticSummatory f (x / d)‖ ≤
      4 * C * y := by
    apply (norm_zeta_convolution_power_strip_le f C hC hA x z hx hz hzx).trans_eq
    rw [mul_assoc (4 * C), hBpower]
  have hoverlap : (⌊z⌋₊ : ℝ) * ‖complexArithmeticSummatory f y‖ ≤ C * y := by
    apply (natFloor_mul_norm_complexArithmeticSummatory_le f C hC hA y z hy hz0).trans_eq
    rw [mul_assoc C, hOpower]
  have htail : x * ‖(∑ n ∈ Ioc 0 ⌊y⌋₊, f n / (n : ℂ)) -
      powerDirichletLimit f 1‖ ≤ 20 * C * y := by
    calc
      _ ≤ x * (20 * C * y ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (norm_reciprocal_sum_natFloor_sub_powerDirichletLimit_le f C hC hA y hy) hx0
      _ = 20 * C * (x * y ^ (-(1 / 4 : ℝ))) := by ring
      _ = _ := by rw [hTpower]
  have hL : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith [Real.log_nonneg hx]
  have hrest : 25 * C * y ≤ 25 * C * y * (1 + Real.log x) ^ 2 :=
    le_mul_of_one_le_right (by positivity) hL
  calc
    _ ≤ (∑ n ∈ Ioc 0 ⌊y⌋₊, ‖f n‖) +
        ‖∑ d ∈ Ioc 0 ⌊z⌋₊, complexArithmeticSummatory f (x / d)‖ +
        (⌊z⌋₊ : ℝ) * ‖complexArithmeticSummatory f y‖ +
        x * ‖(∑ n ∈ Ioc 0 ⌊y⌋₊, f n / (n : ℂ)) - powerDirichletLimit f 1‖ :=
      norm_zeta_convolution_sub_main_le_hyperbola f (powerDirichletLimit f 1)
        x y z hx hy hz hyz
    _ ≤ y * (1 + Real.log x) ^ 2 + 4 * C * y + C * y + 20 * C * y :=
      add_le_add (add_le_add (add_le_add hhead hstrip) hoverlap) htail
    _ ≤ (1 + 25 * C) * y * (1 + Real.log x) ^ 2 := by nlinarith

end TwinPrime.Analytic
