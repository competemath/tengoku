/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.Seed.Analysis.Complex.Liouville

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cauchy 积分公式与导数估计

本文件在圆周上给出 Cauchy 积分公式、圆心处的高阶导数公式和 Cauchy 估计。
公开前提使用 `HolomorphicOnTextbook`，并明确要求它覆盖整个闭圆盘；这保证边界上的
连续性与圆内的可微性。
-/

namespace SandronesLibrary.ComplexAnalysis

open Metric

/-- **Cauchy 积分公式**：若 `f` 在闭圆盘每点的一个完整邻域内全纯，则对任意内点
`w` ，沿正向边界圆周的积分等于 `2πi f(w)`。

> **Entry**: complex-analysis.cauchy.formula-/
theorem cauchy_integral_formula {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hf : HolomorphicOnTextbook f (closedBall c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), f z / (z - w)) = 2 * Real.pi * Complex.I * f w := by
  have hd : DifferentiableOn ℂ f (closedBall c R) := by
    intro z hz
    exact (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z hz)).differentiableWithinAt
  simpa only [div_eq_inv_mul, smul_eq_mul] using hd.circleIntegral_sub_inv_smul hw

/-- **Cauchy 高阶导数公式**：圆心处的 `n` 阶导数由边界圆周积分给出。

> **Entry**: complex-analysis.cauchy.derivatives-/
theorem cauchy_integral_formula_iteratedDeriv {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : HolomorphicOnTextbook f (closedBall c R)) (hR : 0 < R) (n : ℕ) :
    (∮ z in C(c, R), f z / (z - c) ^ (n + 1)) =
      (2 * Real.pi * Complex.I / n.factorial) * iteratedDeriv n f c := by
  have hd : DifferentiableOn ℂ f (closedBall c R) := by
    intro z hz
    exact (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z hz)).differentiableWithinAt
  simpa only [one_div, smul_eq_mul, inv_pow, inv_mul_eq_div] using
    hd.circleIntegral_one_div_sub_center_pow_smul hR n

/-- **Cauchy 估计**：若边界圆周上 `‖f z‖ ≤ C`，则圆心处 `n` 阶导数的范数不超过
`n! C / Rⁿ`。

> **Entry**: complex-analysis.cauchy.derivatives-/
theorem cauchy_estimate {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (hf : HolomorphicOnTextbook f (closedBall c R)) (hR : 0 < R)
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) (n : ℕ) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n := by
  have hd : DifferentiableOn ℂ f (closedBall c R) := by
    intro z hz
    exact (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z hz)).differentiableWithinAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    ((hd.mono closure_ball_subset_closedBall).diffContOnCl) hC

end SandronesLibrary.ComplexAnalysis
