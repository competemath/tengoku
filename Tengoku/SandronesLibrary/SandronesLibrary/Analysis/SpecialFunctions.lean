/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analysis / SpecialFunctions —— 初等特殊函数第一批

本模块把指数函数与三角函数的基础性质整理成教材层接口。证明直接复用
Mathlib 对实函数的标准构造，但定理陈述保持数学分析教材中的记号：正值、加法公式、
连续性和一阶导数。后续重要极限、反函数和 Riemann 积分例子以这些结果为前置。
-/

namespace SandronesLibrary
namespace Analysis.SpecialFunctions

/-- 指数函数在实轴上处处为正。-/
theorem exp_pos (x : ℝ) : 0 < Real.exp x := by
  exact Real.exp_pos x

/-- 指数函数把加法变成乘法，是后续极限与微分计算的基本恒等式。-/
theorem exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by
  exact Real.exp_add x y

/-- 实指数函数在整个实轴上连续。-/
theorem continuous_exp : Continuous (Real.exp : ℝ → ℝ) := by
  exact Real.continuous_exp

/-- 指数函数的导数仍为指数函数本身。-/
theorem deriv_exp (x : ℝ) : deriv Real.exp x = Real.exp x := by
  exact (Real.hasDerivAt_exp x).deriv

/-- 正弦函数在整个实轴上连续。-/
theorem continuous_sin : Continuous (Real.sin : ℝ → ℝ) := by
  exact Real.continuous_sin

/-- 余弦函数在整个实轴上连续。-/
theorem continuous_cos : Continuous (Real.cos : ℝ → ℝ) := by
  exact Real.continuous_cos

/-- 正弦函数的导数是余弦函数。-/
theorem deriv_sin (x : ℝ) : deriv Real.sin x = Real.cos x := by
  exact (Real.hasDerivAt_sin x).deriv

/-- 余弦函数的导数是负的正弦函数。
> **Entry**: analysis.special-functions.basic-/
theorem deriv_cos (x : ℝ) : deriv Real.cos x = -Real.sin x := by
  exact (Real.hasDerivAt_cos x).deriv

/-! ### 对数、正切与自然幂函数 -/

/-- 非零实数乘法下，对数满足加法公式。-/
theorem log_mul (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) = Real.log x + Real.log y := by
  exact Real.log_mul hx hy

/-- 对数函数在正半轴上连续。-/
theorem continuousOn_log : ContinuousOn Real.log (Set.Ioi 0) := by
  exact Real.continuousOn_log.mono (by
    intro x hx
    exact ne_of_gt hx)

/-- 对数函数在非零点的导数为 `1 / x`。-/
theorem deriv_log (x : ℝ) (hx : x ≠ 0) : deriv Real.log x = 1 / x := by
  simpa [one_div] using (Real.hasDerivAt_log hx).deriv

/-! ### 对数函数的教材层基本性质 -/

/-- 对数函数在正半轴上严格递增。-/
theorem strictMonoOn_log_pos : StrictMonoOn Real.log (Set.Ioi 0) := by
  exact Real.strictMonoOn_log

/-- 正数经过 `log` 后再取指数，恢复原数。-/
theorem exp_log_pos {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x) = x := by
  exact Real.exp_log hx

/-- 指数函数经过 `log` 后恢复原数，说明 `log` 是 `exp` 的反函数。-/
theorem log_exp (x : ℝ) : Real.log (Real.exp x) = x := by
  exact Real.log_exp x

/-- 正数乘法下的对数加法公式。
> **Entry**: analysis.special-functions.log-/
theorem log_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x * y) = Real.log x + Real.log y := by
  exact Real.log_mul hx.ne' hy.ne'

/-- 在余弦不为零的点，正切函数的导数为 `1 / cos² x`。-/
theorem deriv_tan (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv Real.tan x = 1 / (Real.cos x) ^ 2 := by
  exact (Real.hasDerivAt_tan hcos).deriv

/-- 任意自然幂函数在实轴上连续。-/
theorem continuous_pow_nat (n : ℕ) : Continuous (fun x : ℝ => x ^ n) := by
  exact continuous_id.pow n

/-- 自然幂函数的导数公式。
> **Entry**: analysis.special-functions.log-tan-pow-/
theorem deriv_pow_nat (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => y ^ n) x = (n : ℝ) * x ^ (n - 1) := by
  simpa [Function.id_def, mul_assoc] using (hasDerivAt_id x).pow n |>.deriv

/-! ### 反三角函数的教材层基本性质 -/

/-- 反正切函数在整个实轴上连续。-/
theorem continuous_arctan : Continuous (Real.arctan : ℝ → ℝ) := by
  exact Real.continuous_arctan

/-- 反正切函数的导数公式。-/
theorem deriv_arctan (x : ℝ) : deriv Real.arctan x = 1 / (1 + x ^ 2) := by
  exact (Real.hasDerivAt_arctan x).deriv

/-- `tan` 与 `arctan` 在实轴上互为右逆。-/
theorem tan_arctan (x : ℝ) : Real.tan (Real.arctan x) = x := by
  exact Real.tan_arctan x

/-- 反正弦函数在整个实轴上连续。-/
theorem continuous_arcsin : Continuous (Real.arcsin : ℝ → ℝ) := by
  exact Real.continuous_arcsin

/-- 反余弦函数在整个实轴上连续。
> **Entry**: analysis.special-functions.tan-pow-/
theorem continuous_arccos : Continuous (Real.arccos : ℝ → ℝ) := by
  exact Real.continuous_arccos

/-- 反正弦在不触及端点 `±1` 的点的导数。-/
theorem hasDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
  exact Real.hasDerivAt_arcsin h₁ h₂

/-- 反余弦在不触及端点 `±1` 的点的导数。-/
theorem hasDerivAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - x ^ 2))) x := by
  exact Real.hasDerivAt_arccos h₁ h₂

end Analysis.SpecialFunctions
end SandronesLibrary
