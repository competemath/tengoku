/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology

/-!
# Analysis / ClassicalLimits —— 经典重要极限

本模块收录数学分析 I 中最常用的四个重要极限。证明从导数在一点的差商极限出发，
并将余弦极限拆成正弦极限、半角恒等式和连续运算，保留教材中的推导结构。
-/

namespace SandronesLibrary
namespace Analysis.ClassicalLimits

/-- 正弦函数的基本重要极限。-/
theorem tendsto_sin_div_id :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa [one_div, div_eq_mul_inv, mul_comm, Real.cos_zero] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

/-- 由正弦基本极限推出的余弦二阶重要极限。
> **Entry**: analysis.limits.classical-/
theorem tendsto_one_sub_cos_div_sq :
    Tendsto (fun x : ℝ => (1 - Real.cos x) / x ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun x : ℝ => x / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff (a := (0 : ℝ)) (s := {0}ᶜ)]
    constructor
    · simpa [div_eq_mul_inv, mul_comm] using
        (tendsto_id'.2 (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).const_mul
          (1 / 2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_compl_singleton_iff.mpr (by
        intro h
        apply (Set.mem_compl_singleton_iff.mp hx)
        linarith)
  have hs : Tendsto (fun x : ℝ => Real.sin (x / 2) / (x / 2))
      (𝓝[≠] 0) (𝓝 1) := tendsto_sin_div_id.comp hhalf
  have hs_sq : Tendsto (fun x : ℝ => (Real.sin (x / 2) / (x / 2)) ^ 2)
      (𝓝[≠] 0) (𝓝 1) := by simpa using hs.pow 2
  have hlim := hs_sq.const_mul (1 / 2 : ℝ)
  have hfun : (fun x : ℝ => (1 - Real.cos x) / x ^ 2) =
      (fun x : ℝ => (1 / 2 : ℝ) * (Real.sin (x / 2) / (x / 2)) ^ 2) := by
    funext x
    have htrig : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
      have h := Real.cos_two_mul_eq_one_sub (x / 2)
      rw [show 2 * (x / 2) = x by ring] at h
      nlinarith
    rw [htrig]
    field_simp
  rw [hfun]
  simpa using hlim

/-- 指数函数在零点的基本重要极限。-/
theorem tendsto_exp_sub_one_div :
    Tendsto (fun x : ℝ => (Real.exp x - 1) / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa [one_div, div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_exp 0).tendsto_slope_zero

/-- 对数函数在一附近的基本重要极限。-/
theorem tendsto_log_one_add_div :
    Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa [one_div, div_eq_mul_inv, mul_comm, Real.log_one, add_comm] using
    (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto_slope_zero

end Analysis.ClassicalLimits
end SandronesLibrary
