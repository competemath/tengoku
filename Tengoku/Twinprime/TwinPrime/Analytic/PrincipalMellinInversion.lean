import Tengoku.Twinprime.TwinPrime.Analytic.SmoothedMangoldtContour
import Tengoku.Twinprime.TwinPrime.Analytic.MellinPoleKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Centered principal Mellin inversion

The exact pole kernel is subtracted on the line of absolute convergence.
The remaining integrand is the logarithmic derivative of regularized
zeta. Both full integrands are integrable, so subtraction commutes with
the actual inverse integral.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

def negativeRegularizedZetaLogDerivative (s : ℂ) : ℂ :=
  -deriv regularizedRiemannZeta s / regularizedRiemannZeta s

def mellinPoleContourIntegrand (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s * mellinPoleKernel s

theorem weighted_vonMangoldt_sum_eq_modOne (x : ℝ) :
    weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x =
      weightedPartialSum (fun n : ℕ =>
        (1 : DirichletCharacter ℂ 1) n * (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
  congr 1
  funext n
  rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one, one_mul]

theorem regularized_mellin_integrand_eq_difference (x : ℝ) (s : ℂ) (hs : 1 < s.re) :
    mellinContourIntegrand x negativeRegularizedZetaLogDerivative s =
      mellinContourIntegrand x (negativeLFunctionLogDerivative (1 : DirichletCharacter ℂ 1)) s -
        mellinPoleContourIntegrand x s := by
  have hs1 : s ≠ 1 := by intro he; simp [he] at hs
  have he := neg_zeta_logDerivative_eq_pole_sub_regularized s hs1
    (regularizedRiemannZeta_ne_zero_of_one_le_re s hs.le)
  unfold mellinContourIntegrand negativeLFunctionLogDerivative
    negativeRegularizedZetaLogDerivative mellinPoleContourIntegrand
  rw [DirichletCharacter.LFunction_modOne_eq, he, mellinPoleKernel_eq_mellinRampKernel_div]
  ring

theorem integrable_mellinPole_contour_integrand (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    Integrable (fun t : ℝ => mellinPoleContourIntegrand x ((c : ℂ) + t * I)) := by
  have hpow : Continuous (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I)) :=
    (show Continuous (fun t : ℝ => (c : ℂ) + t * I) by fun_prop).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hK := verticalIntegrable_mellinPoleKernel c hc
  have hm : AEStronglyMeasurable (fun t : ℝ => mellinPoleContourIntegrand x ((c : ℂ) + t * I)) :=
    hpow.aestronglyMeasurable.mul hK.aestronglyMeasurable
  apply (hK.norm.const_mul (x ^ c)).mono' hm
  filter_upwards [] with t
  rw [mellinPoleContourIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem integrable_regularizedZeta_contour_integrand (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    Integrable (fun t : ℝ => mellinContourIntegrand x negativeRegularizedZetaLogDerivative
      ((c : ℂ) + t * I)) := by
  apply ((integrable_mangoldt_contour_integrand (1 : DirichletCharacter ℂ 1) x c hx hc).sub
    (integrable_mellinPole_contour_integrand x c hx hc)).congr
  filter_upwards [] with t
  exact (regularized_mellin_integrand_eq_difference x ((c : ℂ) + t * I) (by simpa using hc)).symm

theorem mellinPoleWeight_eq_contour_integral (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    mellinPoleWeight (1 / x) = (1 / (2 * Real.pi) : ℝ) •
      ∫ t : ℝ, mellinPoleContourIntegrand x ((c : ℂ) + t * I) := by
  rw [← mellinInv_mellinPoleKernel c hc (1 / x) (by positivity), mellinInv]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul, one_div_cpow_neg_eq x hx]
  rfl

/-- The exact principal main term is retained before estimating the
holomorphic regularized part.-/
theorem weighted_vonMangoldt_sum_sub_pole_eq_contour_integral
    (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
      mellinPoleWeight (1 / x) = (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, mellinContourIntegrand x negativeRegularizedZetaLogDerivative ((c : ℂ) + t * I) := by
  rw [weighted_vonMangoldt_sum_eq_modOne,
    weighted_mangoldt_sum_eq_mellinInv (1 : DirichletCharacter ℂ 1) c hc x hx]
  change mellinInv c (fun s => negativeLFunctionLogDerivative (1 : DirichletCharacter ℂ 1) s *
    mellinRampKernel s) (1 / x) - _ = _
  rw [mellinInv_one_div_eq_contour_integral x hx c,
    mellinPoleWeight_eq_contour_integral x c hx hc, ← smul_sub,
    ← integral_sub (integrable_mangoldt_contour_integrand (1 : DirichletCharacter ℂ 1) x c hx hc)
      (integrable_mellinPole_contour_integrand x c hx hc)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact (regularized_mellin_integrand_eq_difference x ((c : ℂ) + t * I) (by simpa using hc)).symm

theorem norm_negativeRegularizedZetaLogDerivative_vertical_le
    (c t : ℝ) (hc : 1 < c) :
    ‖negativeRegularizedZetaLogDerivative ((c : ℂ) + t * I)‖ ≤
      mangoldtDirichletMass c + 1 / (c - 1) := by
  let s : ℂ := (c : ℂ) + t * I
  have hsr : s.re = c := by simp [s]
  have hs1 : s ≠ 1 := by intro he; simp [he] at hsr; linarith
  have hmass := norm_twist_vonMangoldt_LSeries_le (1 : DirichletCharacter ℂ 1)
    (s := s) (by rwa [hsr])
  rw [← neg_LFunction_logDerivative_eq_twist _ (by rwa [hsr]),
    DirichletCharacter.LFunction_modOne_eq, hsr] at hmass
  have hnorm : c - 1 ≤ ‖s - 1‖ := by simpa [hsr] using Complex.re_le_norm (s - 1)
  have hpole : ‖1 / (s - 1)‖ ≤ 1 / (c - 1) := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by linarith) hnorm
  have he := neg_zeta_logDerivative_eq_pole_sub_regularized s hs1
    (regularizedRiemannZeta_ne_zero_of_one_le_re s (by rw [hsr]; exact hc.le))
  have hsplit : negativeRegularizedZetaLogDerivative s =
      -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) := by
    rw [he]
    unfold negativeRegularizedZetaLogDerivative
    ring
  change ‖negativeRegularizedZetaLogDerivative s‖ ≤ _
  rw [hsplit]
  exact (norm_sub_le _ _).trans (_root_.add_le_add hmass hpole)

theorem norm_regularizedZeta_mellin_integrand_le_inv_sq
    (x c t : ℝ) (hx : 0 < x) (hc : 1 < c) (ht : t ≠ 0) :
    ‖mellinContourIntegrand x negativeRegularizedZetaLogDerivative ((c : ℂ) + t * I)‖ ≤
      x ^ c * (mangoldtDirichletMass c + 1 / (c - 1)) / t ^ 2 := by
  have hF := norm_negativeRegularizedZetaLogDerivative_vertical_le c t hc
  have hK := norm_mellinRampKernel_le_inv_im_sq ((c : ℂ) + t * I) (by simpa using ht)
  have hM : 0 ≤ mangoldtDirichletMass c + 1 / (c - 1) := by
    have hm := mangoldtDirichletMass_nonneg c
    positivity
  rw [mellinContourIntegrand, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hK' : ‖mellinRampKernel ((c : ℂ) + t * I)‖ ≤ 1 / t ^ 2 := by simpa using hK
  calc
    _ ≤ (x ^ c * (mangoldtDirichletMass c + 1 / (c - 1))) * (1 / t ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (Real.rpow_nonneg hx.le _)) hK'
        (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hx.le _) hM)
    _ = _ := by ring

end TwinPrime.Analytic
