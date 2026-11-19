/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.DiskLocalization
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.BallLocalization
public import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Basic
public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Schwartz cutoffs and their averaged input norms

Smooth bump localization followed by recentering stays in the positive
Schwartz domain with fixed support. The averaged input norm is bounded
by the corresponding moving-ball norm, using that the bump lies in `[0,1]`.
-/

public section

open MeasureTheory Set Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ}

/-- A bump bounded by one gives at most the norm of restriction to its support ball.
@isnad1 id=le.0h5v.s9.67f9007e7ce3 from=translated src=- shape=f5e61749 vocab=6ce24b97
-/
theorem eLpNorm_bump_mul_le_ball (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ θ (x - y) * f x) p volume ≤
      eLpNorm ((ball y θ.rOut).indicator (fun x ↦ ‖f x‖ₑ)) p volume := by
  apply eLpNorm_mono_enorm
  intro x
  simp only [enorm_eq_self]
  by_cases hx : x ∈ ball y θ.rOut
  · rw [indicator_of_mem hx, ← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Real.norm_of_nonneg θ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) θ.le_one
  · have hθ : θ (x - y) = 0 := θ.zero_of_le_dist (by
      simpa only [mem_ball, not_lt, dist_eq_norm, sub_zero] using hx)
    rw [hθ, zero_mul, enorm_zero, indicator_of_notMem hx]

/-- Averaging smooth localizations costs at most the volume of the bump's support ball.
@isnad1 id=le.2h4v.s10.83bea55e9d10 from=translated src=- shape=f9490d7b vocab=b2ff292e
-/
theorem lintegral_eLpNorm_bump_mul_rpow_le
    (θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {p : ℝ≥0} (hp : 0 < p) :
    (∫⁻ y, eLpNorm (fun x ↦ θ (x - y) * f x) p volume ^ (p : ℝ)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) θ.rOut) * eLpNorm f p volume ^ (p : ℝ) := by
  have h := lintegral_mono (μ := volume) fun y ↦ ENNReal.rpow_le_rpow
    (eLpNorm_bump_mul_le_ball θ f y p)
    (show 0 ≤ (p : ℝ) from hp.le)
  rw [lintegral_eLpNorm_ball_rpow θ.rOut hf.enorm hp, eLpNorm_enorm] at h
  exact h

end NKBesicovitch
