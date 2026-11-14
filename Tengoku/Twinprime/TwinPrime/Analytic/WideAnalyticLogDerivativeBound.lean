import Tengoku.Twinprime.TwinPrime.Analytic.AnalyticLogDerivativeBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A logarithmic derivative bound on the closed disk of radius 17/16

The normalized logarithm is bounded by `18 A` on radius `9/8`. Cauchy's
inequality on radius `1/16` therefore gives `288 A` throughout radius
`17/16`. The original closed-unit-disk bounds retain their constants.
-/

noncomputable section

open Metric

namespace TwinPrime.Analytic

theorem wide_norm_deriv_le_of_re_le_on_ball {h : ℂ → ℂ} {c : ℂ} {A : ℝ}
    (hA : 0 < A) (hh : DifferentiableOn ℂ h (ball c (5 / 4)))
    (hc : h c = 0) (hre : ∀ w ∈ ball c (5 / 4), (h w).re ≤ A)
    (z : ℂ) (hz : z ∈ closedBall c (17 / 16)) : ‖deriv h z‖ ≤ 288 * A := by
  have hsub : closedBall z (1 / 16) ⊆ closedBall c (9 / 8) := by
    intro w hw
    have := dist_triangle w z c
    have hwz := mem_closedBall.mp hw
    have hzc := mem_closedBall.mp hz
    rw [mem_closedBall]
    linarith
  have hlarge : closedBall z (1 / 16) ⊆ ball c (5 / 4) :=
    hsub.trans (closedBall_subset_ball (by norm_num))
  have hd : DiffContOnCl ℂ h (ball z (1 / 16)) := hh.diffContOnCl_ball hlarge
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 16) hd (fun w hw =>
      norm_analytic_le_of_re_le_on_ball hA hh hc hre w (hsub (sphere_subset_closedBall hw)))
  convert hb using 1
  ring

/-- The enlarged disk allows evaluation slightly left of one when the
center has real part two. Nonvanishing is still an explicit hypothesis.-/
theorem wide_norm_logDerivative_le_of_nonvanishing_on_ball
    {g : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hg : DifferentiableOn ℂ g (ball c (5 / 4)))
    (hgn : ∀ w ∈ ball c (5 / 4), g w ≠ 0)
    (hM : ∀ w ∈ ball c (5 / 4), ‖g w‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall c (17 / 16)) :
    ‖deriv g z / g z‖ ≤ 288 * (1 + Real.log (M / ‖g c‖)) := by
  have hc : c ∈ ball c (5 / 4) := mem_ball_self (by norm_num)
  have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr (hgn c hc)
  have hMc : ‖g c‖ ≤ M := hM c hc
  have hlog : 0 ≤ Real.log (M / ‖g c‖) :=
    Real.log_nonneg ((one_le_div hgc).mpr hMc)
  obtain ⟨h, hh, hhc, he, hd⟩ := exists_normalized_holomorphic_log_on_ball
    g c (5 / 4) (by norm_num) hg hgn
  have hre : ∀ w ∈ ball c (5 / 4), (h w).re ≤ 1 + Real.log (M / ‖g c‖) := by
    intro w hw
    have hb : (h w).re ≤ Real.log (M / ‖g c‖) := by
      rw [← Real.log_exp (h w).re]
      apply Real.log_le_log (Real.exp_pos _)
      rw [← Complex.norm_exp, he w hw, norm_div]
      exact div_le_div_of_nonneg_right (hM w hw) hgc.le
    linarith
  have hz' : z ∈ ball c (5 / 4) := closedBall_subset_ball (by norm_num) hz
  rw [← hd z hz']
  exact wide_norm_deriv_le_of_re_le_on_ball (by linarith) hh hhc hre z hz

theorem wide_zero_removal_log_budget_le_of_jensen {L : ℝ} (N : ℕ)
    (hN : (N : ℝ) ≤ L / Real.log (6 / 5)) :
    288 * (1 + L + N * Real.log 5) ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) * (1 + L) := by
  have h := zero_removal_log_budget_le_of_jensen N hN
  linarith

end TwinPrime.Analytic
