import Tengoku.Seed.Analysis.MellinInversion
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Mellin kernel of a continuous ramp

The transform of `max (1-u) 0` on the positive half-line is `1/(s(s+1))`.
The kernel is integrable on every vertical line with positive real part,
so actual Mellin inversion recovers the continuous ramp at every positive
argument. No convergence hypothesis is left to the caller.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

def mellinRamp (u : ℝ) : ℂ := ((max (1 - u) 0 : ℝ) : ℂ)

def mellinRampKernel (s : ℂ) : ℂ := 1 / (s * (s + 1))

/--
@isnad1 id=eq.1h1v.s5.0f782102edf2 from=translated src=- shape=1c7083cd vocab=e2ce9ea1
-/
theorem mellinRamp_eq_of_le_one (u : ℝ) (hu : u ≤ 1) :
    mellinRamp u = 1 - (u : ℂ) := by
  simp [mellinRamp, max_eq_left (sub_nonneg.mpr hu)]

/--
@isnad1 id=eq.1h1v.s4.2b2b342da33c from=translated src=- shape=aa240375 vocab=9d10f8f9
-/
theorem mellinRamp_eq_zero_of_one_le (u : ℝ) (hu : 1 ≤ u) : mellinRamp u = 0 := by
  simp [mellinRamp, max_eq_right (sub_nonpos.mpr hu)]

/--
@isnad1 id=continuo.0h0v.s4.7d9bbbd51924 from=translated src=- shape=54c8eceb vocab=98620bf9
-/
theorem continuous_mellinRamp : Continuous mellinRamp := by
  unfold mellinRamp
  fun_prop

private theorem mellinRamp_integrand_eq_indicator (s : ℂ) (t : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) • mellinRamp t =
      (Ioc (0 : ℝ) 1).indicator (fun x : ℝ => (x : ℂ) ^ (s - 1) - (x : ℂ) ^ s) t := by
  by_cases ht1 : t ≤ 1
  · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩),
      mellinRamp_eq_of_le_one t ht1, smul_eq_mul]
    have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ s := by
      simpa only [sub_add_cancel, Complex.cpow_one] using
        (Complex.cpow_add (s - 1) 1 (by exact_mod_cast ht.ne' : (t : ℂ) ≠ 0)).symm
    rw [mul_sub, mul_one, hpow]
  · rw [indicator_of_notMem (by simp only [mem_Ioc]; tauto),
      mellinRamp_eq_zero_of_one_le t (le_of_not_ge ht1), smul_zero]

private theorem intervalIntegrable_mellinRamp_difference (s : ℂ) (hs : 0 < s.re) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) - (t : ℂ) ^ s) volume 0 1 := by
  apply IntervalIntegrable.sub
  · apply intervalIntegral.intervalIntegrable_cpow'
    simp only [sub_re, one_re]
    linarith
  · exact intervalIntegral.intervalIntegrable_cpow' (by linarith)

/--
@isnad1 id=mellinco.1h1v.s4.7715ec3993bd from=translated src=- shape=c5298c69 vocab=7ac13073
-/
theorem mellinConvergent_mellinRamp (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent mellinRamp s := by
  have hi := (intervalIntegrable_mellinRamp_difference s hs).1.integrable_indicator
    measurableSet_Ioc
  exact hi.integrableOn.congr_fun (fun t ht =>
    (mellinRamp_integrand_eq_indicator s t ht).symm) measurableSet_Ioi

/--
@isnad1 id=eq.1h1v.s5.21ed2bd5ac6d from=translated src=- shape=cae4238f vocab=ccbc8645
-/
theorem mellin_mellinRamp (s : ℂ) (hs : 0 < s.re) :
    mellin mellinRamp s = mellinRampKernel s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at this
    linarith
  have hI : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := inter_eq_right.mpr Ioc_subset_Ioi_self
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => mellinRamp_integrand_eq_indicator s t ht),
    setIntegral_indicator measurableSet_Ioc, hI,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_sub]
  · rw [integral_cpow (Or.inl (by simp only [sub_re, one_re]; linarith)),
      integral_cpow (Or.inl (by linarith : -1 < s.re))]
    simp only [ofReal_one, ofReal_zero, sub_add_cancel, one_cpow,
      zero_cpow hs0, zero_cpow hs1, sub_zero]
    unfold mellinRampKernel
    field_simp
    ring
  · exact intervalIntegral.intervalIntegrable_cpow' (by simp only [sub_re, one_re]; linarith)
  · exact intervalIntegral.intervalIntegrable_cpow' (by linarith)

/--
@isnad1 id=hasmelli.1h1v.s4.95af70a093cc from=translated src=- shape=20c519ab vocab=f738bae6
-/
theorem hasMellin_mellinRamp (s : ℂ) (hs : 0 < s.re) :
    HasMellin mellinRamp s (mellinRampKernel s) :=
  ⟨mellinConvergent_mellinRamp s hs, mellin_mellinRamp s hs⟩

/--
@isnad1 id=le.1h2v.s6.577df9cd5a75 from=translated src=- shape=c8401b0b vocab=e292b0de
-/
theorem norm_mellinRampKernel_vertical_le (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ‖mellinRampKernel ((c : ℂ) + t * I)‖ ≤
      (1 + (c ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by
  let s : ℂ := (c : ℂ) + t * I
  have hnorm : ‖s‖ ^ 2 = c ^ 2 + t ^ 2 := by
    simp [s, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnorm1 : ‖s + 1‖ ^ 2 = (c + 1) ^ 2 + t ^ 2 := by
    simp [s, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hle : ‖s‖ ≤ ‖s + 1‖ := by nlinarith [norm_nonneg s, norm_nonneg (s + 1)]
  have hprod : c ^ 2 + t ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hle (norm_nonneg s)]
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hden : 0 < c ^ 2 + t ^ 2 := by positivity
  have hnum : 1 + t ^ 2 ≤ (1 + (c ^ 2)⁻¹) * (c ^ 2 + t ^ 2) := by
    have hi : (c ^ 2)⁻¹ * c ^ 2 = 1 := inv_mul_cancel₀ hc2.ne'
    have hp : 0 ≤ (c ^ 2)⁻¹ * t ^ 2 := by positivity
    nlinarith
  calc
    _ = 1 / (‖s‖ * ‖s + 1‖) := by simp only [mellinRampKernel, norm_div, norm_one, norm_mul]; rfl
    _ ≤ 1 / (c ^ 2 + t ^ 2) := one_div_le_one_div_of_le hden hprod
    _ ≤ (1 + (c ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (div_le_div_iff₀ hden (by positivity)).mpr (by simpa only [one_mul] using hnum)

/--
@isnad1 id=vertical.1h1v.s4.22257f9d88bf from=translated src=- shape=cfaaad28 vocab=123895b3
-/
theorem verticalIntegrable_mellinRampKernel (c : ℝ) (hc : 0 < c) :
    VerticalIntegrable mellinRampKernel c := by
  have hs (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_re] at this
    linarith
  have hs1 (t : ℝ) : (c : ℂ) + t * I + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, one_re, zero_re] at this
    linarith
  have hcont : Continuous (fun t : ℝ => mellinRampKernel ((c : ℂ) + t * I)) := by
    unfold mellinRampKernel
    exact continuous_const.div (by fun_prop) (fun t => mul_ne_zero (hs t) (hs1 t))
  exact (integrable_inv_one_add_sq.const_mul (1 + (c ^ 2)⁻¹)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall (norm_mellinRampKernel_vertical_le c hc))

/--
@isnad1 id=vertical.1h1v.s5.5c431663afe6 from=translated src=- shape=9edc543a vocab=ceac725b
-/
theorem verticalIntegrable_mellin_mellinRamp (c : ℝ) (hc : 0 < c) :
    VerticalIntegrable (mellin mellinRamp) c := by
  apply (verticalIntegrable_mellinRampKernel c hc).congr
  filter_upwards [] with t
  exact (mellin_mellinRamp ((c : ℂ) + t * I) (by simpa using hc)).symm

/--
@isnad1 id=eq.2h2v.s5.d94d2c7e7898 from=translated src=- shape=3dafefcd vocab=24f7ffbb
-/
theorem mellinInv_mellinRampKernel (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : 0 < u) :
    mellinInv c mellinRampKernel u = mellinRamp u := by
  have hinv := mellinInv_mellin_eq c mellinRamp hu
    (mellinConvergent_mellinRamp (c : ℂ) hc)
    (verticalIntegrable_mellin_mellinRamp c hc) continuous_mellinRamp.continuousAt
  rw [← hinv]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mellin_mellinRamp ((c : ℂ) + t * I) (by simpa using hc)]

end TwinPrime.Analytic
