import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveMass
import Tengoku.Twinprime.TwinPrime.Analytic.HarmonicConvolutionLimit
import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveError

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Asymptotic size of the middle-prime sieve denominator

Absolute convergence of the correction and the exact harmonic convolution
give `S(z) / log z → 1 / (2 C₂)`. The reciprocal form is uniform over all
sufficiently large natural thresholds, for substitution into a growing
family of finite sieves.
-/

noncomputable section

open Finset Filter Topology

namespace TwinPrime.Analytic

/--
@isnad1 id=tendsto.0h0v.s6.74095f05f0d5 from=translated src=- shape=fad2f17c vocab=24a6a388
-/
theorem tendsto_middlePrimeSelbergDenominator_div_one_add_log :
    Tendsto (fun z : ℕ => middlePrimeSelbergDenominator z / (1 + Real.log z))
      atTop (𝓝 (1 / (2 * twinPrimeConstant))) := by
  have h := tendsto_harmonic_convolution_div_log_of_zero
    middlePrimeSelbergCorrection
    (by simpa only [Real.norm_eq_abs] using summable_norm_middlePrimeSelbergCorrection)
    (ArithmeticFunction.map_zero (f := middlePrimeSelbergCorrection))
  simpa only [← middlePrimeSelbergDenominator_eq_harmonic_convolution,
    tsum_middlePrimeSelbergCorrection] using h

/--
@isnad1 id=tendsto.0h0v.s5.4158aefb5547 from=translated src=- shape=ea4f1310 vocab=28c4b88c
-/
theorem tendsto_middlePrimeSelbergDenominator_div_log :
    Tendsto (fun z : ℕ => middlePrimeSelbergDenominator z / Real.log z)
      atTop (𝓝 (1 / (2 * twinPrimeConstant))) := by
  have hlog : Tendsto (fun z : ℕ => Real.log (z : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun z : ℕ => (1 + Real.log z) / Real.log z)
      atTop (𝓝 1) := by
    have h := hlog.inv_tendsto_atTop.add_const 1
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with z hz
    have hz1 : (1 : ℝ) < z := by exact_mod_cast hz
    have hn : Real.log (z : ℝ) ≠ 0 := (Real.log_pos hz1).ne'
    change (Real.log (z : ℝ))⁻¹ + 1 = _
    simp only [add_div, one_div, div_self hn]
  have h := tendsto_middlePrimeSelbergDenominator_div_one_add_log.mul hratio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with z hz
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hn : 1 + Real.log (z : ℝ) ≠ 0 := by
    have := Real.log_nonneg hz1
    linarith
  field_simp

/--
@isnad1 id=tendsto.0h0v.s5.d6b62de149e3 from=translated src=- shape=dcfdeab9 vocab=28c4b88c
-/
theorem tendsto_log_div_middlePrimeSelbergDenominator :
    Tendsto (fun z : ℕ => Real.log z / middlePrimeSelbergDenominator z)
      atTop (𝓝 (2 * twinPrimeConstant)) := by
  have hC : 2 * twinPrimeConstant ≠ 0 :=
    (mul_pos (by norm_num) twinPrimeConstant_pos).ne'
  have h := tendsto_middlePrimeSelbergDenominator_div_log.inv₀ (one_div_ne_zero hC)
  simpa only [inv_div, inv_one, div_one] using h

/-- One threshold controls every member of a growing sieve family.
@isnad1 id=ex.1h1v.s6.9258457eb072 from=translated src=- shape=67c865b7 vocab=d7c006b4
-/
theorem middlePrimeSelbergDenominator_uniform_reciprocal_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : ℕ, ∀ z ≥ Z, 0 < Real.log (z : ℝ) ∧
      1 / middlePrimeSelbergDenominator z ≤
        (2 * twinPrimeConstant + ε) / Real.log z := by
  have h := tendsto_log_div_middlePrimeSelbergDenominator.eventually
    (gt_mem_nhds (lt_add_of_pos_right (2 * twinPrimeConstant) hε))
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp h
  refine ⟨max Z 2, fun z hz => ?_⟩
  have hz2 : 2 ≤ z := (le_max_right _ _).trans hz
  have hz1 : (1 : ℝ) < z := by exact_mod_cast hz2
  have hlog := Real.log_pos hz1
  refine ⟨hlog, ?_⟩
  have hr := (hZ z ((le_max_left _ _).trans hz)).le
  calc
    1 / middlePrimeSelbergDenominator z =
        (Real.log z / middlePrimeSelbergDenominator z) / Real.log z := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hr hlog.le

end TwinPrime.Analytic
