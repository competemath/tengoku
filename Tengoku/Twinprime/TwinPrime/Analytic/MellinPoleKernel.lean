import Tengoku.Twinprime.TwinPrime.Analytic.MellinRampKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The principal-pole Mellin kernel

The weight `max(1-u,0)^2/(2u)` has Mellin transform
`1/((s-1)s(s+1))` on `Re(s)>1`. Actual Mellin inversion gives
the exact principal term `(x-1)^2/(2x)` at the reciprocal argument.
No residue formula or distribution hypothesis is assumed.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

def mellinPoleWeight (u : ℝ) : ℂ := mellinRamp u ^ 2 / (2 * (u : ℂ))

def mellinPoleKernel (s : ℂ) : ℂ := 1 / ((s - 1) * s * (s + 1))

theorem mellinPoleWeight_eq_of_le_one (u : ℝ) (hu : u ≤ 1) :
    mellinPoleWeight u = (1 - (u : ℂ)) ^ 2 / (2 * (u : ℂ)) := by
  rw [mellinPoleWeight, mellinRamp_eq_of_le_one u hu]

theorem mellinPoleWeight_eq_zero_of_one_le (u : ℝ) (hu : 1 ≤ u) :
    mellinPoleWeight u = 0 := by
  simp [mellinPoleWeight, mellinRamp_eq_zero_of_one_le u hu]

theorem continuousAt_mellinPoleWeight (u : ℝ) (hu : u ≠ 0) :
    ContinuousAt mellinPoleWeight u := by
  unfold mellinPoleWeight
  exact (continuous_mellinRamp.continuousAt.pow 2).div
    (by fun_prop) (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hu))

private theorem mellinPoleWeight_eq_ramp_difference (u : ℝ) (hu : 0 < u) :
    mellinPoleWeight u =
      ((u : ℂ) ^ (-1 : ℂ) * mellinRamp u - mellinRamp u) / 2 := by
  by_cases hu1 : u ≤ 1
  · rw [mellinPoleWeight_eq_of_le_one u hu1, mellinRamp_eq_of_le_one u hu1,
      Complex.cpow_neg_one]
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    field_simp
  · simp [mellinPoleWeight_eq_zero_of_one_le u (le_of_not_ge hu1),
      mellinRamp_eq_zero_of_one_le u (le_of_not_ge hu1)]

private theorem mellinPoleWeight_integrand_eq (s : ℂ) (u : ℝ) (hu : 0 < u) :
    (u : ℂ) ^ (s - 1) • mellinPoleWeight u =
      ((u : ℂ) ^ ((s - 1) - 1) • mellinRamp u -
        (u : ℂ) ^ (s - 1) • mellinRamp u) / 2 := by
  have hp : (u : ℂ) ^ (s - 1) * (u : ℂ) ^ (-1 : ℂ) =
      (u : ℂ) ^ ((s - 1) - 1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
    congr 1
  rw [mellinPoleWeight_eq_ramp_difference u hu]
  simp only [smul_eq_mul]
  rw [← mul_div_assoc, mul_sub, ← mul_assoc, hp]

theorem mellinConvergent_mellinPoleWeight (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent mellinPoleWeight s := by
  have h0 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ ((s - 1) - 1) • mellinRamp u)
      (Ioi 0) := mellinConvergent_mellinRamp (s - 1) (by simp only [sub_re, one_re]; linarith)
  have h1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) • mellinRamp u)
      (Ioi 0) := mellinConvergent_mellinRamp s (by linarith)
  have hi : IntegrableOn (fun u : ℝ =>
      ((u : ℂ) ^ ((s - 1) - 1) • mellinRamp u -
        (u : ℂ) ^ (s - 1) • mellinRamp u) / 2) (Ioi 0) :=
    (h0.sub h1).div_const (2 : ℂ)
  exact hi.congr_fun
    (fun u hu => (mellinPoleWeight_integrand_eq s u hu).symm) measurableSet_Ioi

theorem mellin_mellinPoleWeight (s : ℂ) (hs : 1 < s.re) :
    mellin mellinPoleWeight s = mellinPoleKernel s := by
  have hsm1 : 0 < (s - 1).re := by simp only [sub_re, one_re]; linarith
  have hs0 : 0 < s.re := by linarith
  have h0 := mellinConvergent_mellinRamp (s - 1) hsm1
  have h1 := mellinConvergent_mellinRamp s hs0
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => mellinPoleWeight_integrand_eq s u hu), integral_div, integral_sub h0 h1]
  change (mellin mellinRamp (s - 1) - mellin mellinRamp s) / 2 = mellinPoleKernel s
  rw [mellin_mellinRamp (s - 1) hsm1, mellin_mellinRamp s hs0]
  have hsne : s ≠ 0 := by intro h; simp [h] at hs0
  have hsmne : s - 1 ≠ 0 := by intro h; simp [h] at hsm1
  have hspne : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at this
    linarith
  unfold mellinRampKernel mellinPoleKernel
  simp only [sub_add_cancel]
  field_simp
  ring

theorem hasMellin_mellinPoleWeight (s : ℂ) (hs : 1 < s.re) :
    HasMellin mellinPoleWeight s (mellinPoleKernel s) :=
  ⟨mellinConvergent_mellinPoleWeight s hs, mellin_mellinPoleWeight s hs⟩

theorem mellinPoleKernel_eq_mellinRampKernel_div (s : ℂ) :
    mellinPoleKernel s = mellinRampKernel s / (s - 1) := by
  simp only [mellinPoleKernel, mellinRampKernel, div_div]
  congr 1
  ring

theorem norm_mellinPoleKernel_vertical_le (c : ℝ) (hc : 1 < c) (t : ℝ) :
    ‖mellinPoleKernel ((c : ℂ) + t * I)‖ ≤
      ‖mellinRampKernel ((c : ℂ) + t * I)‖ / (c - 1) := by
  have hr : c - 1 ≤ ‖(c : ℂ) + t * I - 1‖ := by
    simpa using Complex.re_le_norm ((c : ℂ) + t * I - 1)
  rw [mellinPoleKernel_eq_mellinRampKernel_div, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) hr

theorem verticalIntegrable_mellinPoleKernel (c : ℝ) (hc : 1 < c) :
    VerticalIntegrable mellinPoleKernel c := by
  have hs (t : ℝ) : (c : ℂ) + t * I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, one_re, zero_re] at this
    linarith
  have hs0 (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
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
  have hcont : Continuous (fun t : ℝ => mellinPoleKernel ((c : ℂ) + t * I)) := by
    unfold mellinPoleKernel
    exact continuous_const.div (by fun_prop)
      (fun t => mul_ne_zero (mul_ne_zero (hs t) (hs0 t)) (hs1 t))
  exact ((verticalIntegrable_mellinRampKernel c (by linarith)).norm.div_const (c - 1)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall (norm_mellinPoleKernel_vertical_le c hc))

theorem verticalIntegrable_mellin_mellinPoleWeight (c : ℝ) (hc : 1 < c) :
    VerticalIntegrable (mellin mellinPoleWeight) c := by
  apply (verticalIntegrable_mellinPoleKernel c hc).congr
  filter_upwards [] with t
  exact (mellin_mellinPoleWeight ((c : ℂ) + t * I) (by simpa using hc)).symm

theorem mellinInv_mellinPoleKernel (c : ℝ) (hc : 1 < c) (u : ℝ) (hu : 0 < u) :
    mellinInv c mellinPoleKernel u = mellinPoleWeight u := by
  have hinv := mellinInv_mellin_eq c mellinPoleWeight hu
    (mellinConvergent_mellinPoleWeight (c : ℂ) hc)
    (verticalIntegrable_mellin_mellinPoleWeight c hc) (continuousAt_mellinPoleWeight u hu.ne')
  rw [← hinv]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mellin_mellinPoleWeight ((c : ℂ) + t * I) (by simpa using hc)]

theorem mellinPoleWeight_one_div (x : ℝ) (hx : 1 ≤ x) :
    mellinPoleWeight (1 / x) = (((x - 1) ^ 2 / (2 * x) : ℝ) : ℂ) := by
  have hx0 : 0 < x := by linarith
  rw [mellinPoleWeight_eq_of_le_one (1 / x) ((div_le_one hx0).mpr hx)]
  push_cast
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  field_simp

theorem mellinInv_mellinPoleKernel_one_div (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 1 ≤ x) :
    mellinInv c mellinPoleKernel (1 / x) = (((x - 1) ^ 2 / (2 * x) : ℝ) : ℂ) := by
  rw [mellinInv_mellinPoleKernel c hc (1 / x) (by positivity), mellinPoleWeight_one_div x hx]

theorem norm_mellinPoleWeight_one_div_sub_half_le (x : ℝ) (hx : 1 ≤ x) :
    ‖mellinPoleWeight (1 / x) - ((x / 2 : ℝ) : ℂ)‖ ≤ 1 := by
  rw [mellinPoleWeight_one_div x hx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hx0 : 0 < x := by linarith
  have heq : (x - 1) ^ 2 / (2 * x) - x / 2 = -1 + 1 / (2 * x) := by
    field_simp
    ring
  rw [heq]
  apply abs_le.mpr
  have hi : 0 ≤ 1 / (2 * x) := by positivity
  have hi1 : 1 / (2 * x) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  constructor <;> linarith

end TwinPrime.Analytic
