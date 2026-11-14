import Tengoku.Seed.Analysis.Complex.BorelCaratheodory
import Tengoku.Seed.Analysis.Complex.Liouville
import Tengoku.Twinprime.TwinPrime.Analytic.HolomorphicLog

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit derivative bounds from a normalized holomorphic logarithm

Borel–Carathéodory on radius `5/4`, followed by Cauchy's inequality on
radius `1/8`, gives the constant `144` on the closed unit disk.
-/

noncomputable section

open Metric

namespace TwinPrime.Analytic

theorem norm_analytic_le_of_re_le_on_ball {h : ℂ → ℂ} {c : ℂ} {A : ℝ}
    (hA : 0 < A) (hh : DifferentiableOn ℂ h (ball c (5 / 4)))
    (hc : h c = 0) (hre : ∀ w ∈ ball c (5 / 4), (h w).re ≤ A)
    (w : ℂ) (hw : w ∈ closedBall c (9 / 8)) : ‖h w‖ ≤ 18 * A := by
  have hshift : DifferentiableOn ℂ (fun z => h (z + c)) (ball 0 (5 / 4)) := by
    apply hh.comp (by fun_prop)
    intro z hz
    simpa only [mem_ball_iff_norm, add_sub_cancel_right, sub_zero] using hz
  have hmap : Set.MapsTo (fun z => h (z + c)) (ball 0 (5 / 4)) {z | z.re ≤ A} := by
    intro z hz
    apply hre
    simpa only [mem_ball_iff_norm, add_sub_cancel_right, sub_zero] using hz
  have hwle : ‖w - c‖ ≤ 9 / 8 := mem_closedBall_iff_norm.mp hw
  have hwr : w - c ∈ ball (0 : ℂ) (5 / 4) := by
    rw [mem_ball_zero_iff]
    linarith
  have hb := Complex.borelCaratheodory_zero hA hshift hmap (by norm_num) hwr
    (by simpa using hc)
  simp only [sub_add_cancel] at hb
  apply hb.trans
  apply (div_le_iff₀ (by linarith : 0 < 5 / 4 - ‖w - c‖)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hwle hA.le]

theorem norm_deriv_le_of_re_le_on_ball {h : ℂ → ℂ} {c : ℂ} {A : ℝ}
    (hA : 0 < A) (hh : DifferentiableOn ℂ h (ball c (5 / 4)))
    (hc : h c = 0) (hre : ∀ w ∈ ball c (5 / 4), (h w).re ≤ A)
    (z : ℂ) (hz : z ∈ closedBall c 1) : ‖deriv h z‖ ≤ 144 * A := by
  have hsub : closedBall z (1 / 8) ⊆ closedBall c (9 / 8) := by
    intro w hw
    have := dist_triangle w z c
    have hwz := mem_closedBall.mp hw
    have hzc := mem_closedBall.mp hz
    rw [mem_closedBall]
    linarith
  have hlarge : closedBall z (1 / 8) ⊆ ball c (5 / 4) :=
    hsub.trans (closedBall_subset_ball (by norm_num))
  have hd : DiffContOnCl ℂ h (ball z (1 / 8)) := hh.diffContOnCl_ball hlarge
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 8) hd (fun w hw =>
      norm_analytic_le_of_re_le_on_ball hA hh hc hre w (hsub (sphere_subset_closedBall hw)))
  convert hb using 1
  ring

/-- A logarithmic derivative bound for a holomorphic function without zeros.
The factorization removing zeros must be established before applying this
bound to an L-function.-/
theorem norm_logDerivative_le_of_nonvanishing_on_ball {g : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hg : DifferentiableOn ℂ g (ball c (5 / 4)))
    (hgn : ∀ w ∈ ball c (5 / 4), g w ≠ 0)
    (hM : ∀ w ∈ ball c (5 / 4), ‖g w‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall c 1) :
    ‖deriv g z / g z‖ ≤ 144 * (1 + Real.log (M / ‖g c‖)) := by
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
  exact norm_deriv_le_of_re_le_on_ball (by linarith) hh hhc hre z hz

theorem zero_removal_log_budget_le {a b M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hM : 0 < M) (N : ℕ) (hcenter : a ≤ (5 / 4 : ℝ) ^ N * b) :
    1 + Real.log (M * 4 ^ N / b) ≤
      1 + Real.log (M / a) + N * Real.log 5 := by
  have hlog := Real.log_le_log ha hcenter
  rw [Real.log_mul (by positivity) hb.ne', Real.log_pow] at hlog
  rw [Real.log_div hM.ne' ha.ne',
    Real.log_div (by positivity) hb.ne', Real.log_mul hM.ne' (by positivity),
    Real.log_pow]
  have h45 : Real.log (5 / 4 : ℝ) = Real.log 5 - Real.log 4 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [h45] at hlog
  nlinarith

theorem zero_removal_log_budget_le_of_jensen {L : ℝ} (N : ℕ)
    (hN : (N : ℝ) ≤ L / Real.log (6 / 5)) :
    144 * (1 + L + N * Real.log 5) ≤
      (144 * (1 + Real.log 5 / Real.log (6 / 5))) * (1 + L) := by
  have hd : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hN h5
  have he : L / Real.log (6 / 5) * Real.log 5 =
      L * (Real.log 5 / Real.log (6 / 5)) := by ring
  rw [he] at hn
  have hquot := div_nonneg h5 hd.le
  nlinarith

end TwinPrime.Analytic
