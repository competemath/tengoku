import Tengoku.Twinprime.TwinPrime.Analytic.MangoldtMellinInversion
import Tengoku.Twinprime.TwinPrime.Analytic.MellinRectangle
import Tengoku.Twinprime.TwinPrime.Analytic.MellinTruncation
import Tengoku.Twinprime.TwinPrime.Analytic.LogDerivativeStrip

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual smoothed Mangoldt sums and quantitative contours

The inversion theorem and the two tails are combined with a finite
rectangle shift. For primitive nonprincipal characters the zero-free
rectangle supplies both holomorphy and the full complex norm bound.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

def negativeLFunctionLogDerivative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

/--
@isnad1 id=eq.1h2v.s5.575c2bd8f513 from=translated src=- shape=38804fce vocab=572cb429
-/
theorem one_div_cpow_neg_eq (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ((1 / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg, inv_inv]

/--
@isnad1 id=eq.1h3v.s7.17ec40e43ab9 from=translated src=- shape=d30c47cb vocab=a0381d71
-/
theorem mellinInv_one_div_eq_contour_integral (x : ℝ) (hx : 0 < x)
    (c : ℝ) (F : ℂ → ℂ) :
    mellinInv c (fun s => F s * mellinRampKernel s) (1 / x) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, mellinContourIntegrand x F ((c : ℂ) + t * I) := by
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul, one_div_cpow_neg_eq x hx]
  unfold mellinContourIntegrand
  ring

/--
@isnad1 id=integrab.2h4v.s6.36782401891f from=translated src=- shape=468840c3 vocab=87369478
-/
theorem integrable_mangoldt_contour_integrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      mellinContourIntegrand x (negativeLFunctionLogDerivative χ) ((c : ℂ) + t * I)) := by
  apply (integrable_mangoldt_mellinRamp_integrand χ c hc (1 / x) (by positivity)).congr
  filter_upwards [] with t
  rw [one_div_cpow_neg_eq x hx]
  unfold mellinContourIntegrand negativeLFunctionLogDerivative
  ring

/-- Truncation of the actual inverse Mellin integral, including both tails.
@isnad1 id=le.3h5v.s8.74e7859faf92 from=translated src=- shape=c61fd374 vocab=9a338988
-/
theorem norm_weighted_mangoldt_sum_sub_vertical_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x c H : ℝ)
    (hx : 0 < x) (hc : 1 < c) (hH : 0 < H) :
    ‖weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x -
        (1 / (2 * Real.pi) : ℝ) •
          mellinVerticalSegment x (negativeLFunctionLogDerivative χ) c H‖ ≤
      x ^ c * mangoldtDirichletMass c / (Real.pi * H) := by
  rw [weighted_mangoldt_sum_eq_mellinInv χ c hc x hx]
  change ‖mellinInv c (fun s => negativeLFunctionLogDerivative χ s * mellinRampKernel s) (1 / x) - _‖ ≤ _
  rw [mellinInv_one_div_eq_contour_integral x hx c]
  have ht := norm_integral_sub_intervalIntegral_le_of_inv_sq_bound
    (fun t : ℝ => mellinContourIntegrand x (negativeLFunctionLogDerivative χ) ((c : ℂ) + t * I))
    (integrable_mangoldt_contour_integrand χ x c hx hc) H
    (x ^ c * mangoldtDirichletMass c) hH (by
      intro t ht
      exact norm_mangoldt_mellin_integrand_le_inv_sq χ x c t hx hc
        (by intro he; simp only [he, abs_zero] at ht; linarith))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * (x ^ c * mangoldtDirichletMass c) / H) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

def smoothedMangoldtContourBudget (x a c H M : ℝ) : ℝ :=
  x ^ c * mangoldtDirichletMass c / (Real.pi * H) +
    (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2)

/--
@isnad1 id=le.8h7v.s8.52bcca272a93 from=translated src=- shape=ea283cf5 vocab=ec27c023
-/
theorem norm_weighted_mangoldt_sum_le_contour_budget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x a c H M : ℝ)
    (hx : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c) (hc : 1 < c)
    (hH : 0 < H) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ (negativeLFunctionLogDerivative χ)
      (Icc a c ×ℂ Icc (-H) H))
    (hF : ∀ s ∈ Icc a c ×ℂ Icc (-H) H, ‖negativeLFunctionLogDerivative χ s‖ ≤ M) :
    ‖weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x‖ ≤
      smoothedMangoldtContourBudget x a c H M := by
  have htail := norm_weighted_mangoldt_sum_sub_vertical_le χ x c H (by linarith) hc hH
  have hrect := norm_mellinVerticalSegment_right_le x hx (negativeLFunctionLogDerivative χ)
    a c H M ha hac hH hM hd hF
  let S := weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x
  let V := (1 / (2 * Real.pi) : ℝ) • mellinVerticalSegment x (negativeLFunctionLogDerivative χ) c H
  have hV : ‖V‖ ≤ (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2) := by
    dsimp only [V]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left hrect (by positivity)
  have hsum := norm_add_le (S - V) V
  rw [sub_add_cancel] at hsum
  change ‖S - V‖ ≤ _ at htail
  change ‖S‖ ≤ _
  unfold smoothedMangoldtContourBudget
  linarith

end TwinPrime.Analytic
