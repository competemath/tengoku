import Tengoku.Twinprime.TwinPrime.Analytic.PrincipalMellinInversion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The principal smoothed contour estimate

The exact pole inverse is separated before shifting the holomorphic
regularized-zeta integrand. Its independent zero-free rectangle supplies
all nonvanishing and norm hypotheses. The final bound centers the actual
smoothed Mangoldt sum at `x/2`, with the pole correction at most one.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

theorem norm_weighted_vonMangoldt_sub_pole_sub_vertical_le (x c H : ℝ)
    (hx : 0 < x) (hc : 1 < c) (hH : 0 < H) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
        mellinPoleWeight (1 / x) - (1 / (2 * Real.pi) : ℝ) •
          mellinVerticalSegment x negativeRegularizedZetaLogDerivative c H‖ ≤
      x ^ c * (mangoldtDirichletMass c + 1 / (c - 1)) / (Real.pi * H) := by
  rw [weighted_vonMangoldt_sum_sub_pole_eq_contour_integral x c hx hc]
  have ht := norm_integral_sub_intervalIntegral_le_of_inv_sq_bound
    (fun t : ℝ => mellinContourIntegrand x negativeRegularizedZetaLogDerivative ((c : ℂ) + t * I))
    (integrable_regularizedZeta_contour_integrand x c hx hc) H
    (x ^ c * (mangoldtDirichletMass c + 1 / (c - 1))) hH (by
      intro t ht
      exact norm_regularizedZeta_mellin_integrand_le_inv_sq x c t hx hc
        (by intro he; simp only [he, abs_zero] at ht; linarith))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (2 * (x ^ c * (mangoldtDirichletMass c + 1 / (c - 1))) / H) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

def smoothedPrincipalContourBudget (x a c H M : ℝ) : ℝ :=
  x ^ c * (mangoldtDirichletMass c + 1 / (c - 1)) / (Real.pi * H) +
    (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2)

theorem norm_weighted_vonMangoldt_sub_pole_le_contour_budget (x a c H M : ℝ)
    (hx : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c) (hc : 1 < c)
    (hH : 0 < H) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ negativeRegularizedZetaLogDerivative (Icc a c ×ℂ Icc (-H) H))
    (hF : ∀ s ∈ Icc a c ×ℂ Icc (-H) H, ‖negativeRegularizedZetaLogDerivative s‖ ≤ M) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
      mellinPoleWeight (1 / x)‖ ≤ smoothedPrincipalContourBudget x a c H M := by
  have htail := norm_weighted_vonMangoldt_sub_pole_sub_vertical_le x c H (by linarith) hc hH
  have hrect := norm_mellinVerticalSegment_right_le x hx negativeRegularizedZetaLogDerivative
    a c H M ha hac hH hM hd hF
  let S := weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
    mellinPoleWeight (1 / x)
  let V := (1 / (2 * Real.pi) : ℝ) • mellinVerticalSegment x negativeRegularizedZetaLogDerivative c H
  have hV : ‖V‖ ≤ (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2) := by
    dsimp only [V]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left hrect (by positivity)
  have hsum := norm_add_le (S - V) V
  rw [sub_add_cancel] at hsum
  change ‖S - V‖ ≤ _ at htail
  change ‖S‖ ≤ _
  unfold smoothedPrincipalContourBudget
  linarith

end TwinPrime.Analytic
