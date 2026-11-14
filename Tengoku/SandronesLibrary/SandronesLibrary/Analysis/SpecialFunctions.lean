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

/-- 指数函数在实轴上处处为正。
@isnad1 id=lt.0h1v.s3.54d0bda84733 from=translated src=- shape=8a62b088 vocab=6f7909c0
-/
theorem exp_pos (x : ℝ) : 0 < Real.exp x := by
  exact Real.exp_pos x

/-- 指数函数把加法变成乘法，是后续极限与微分计算的基本恒等式。
@isnad1 id=eq.0h2v.s4.629a5bfc7a53 from=translated src=- shape=a13ca989 vocab=0f7a7319
-/
theorem exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by
  exact Real.exp_add x y

/-- 实指数函数在整个实轴上连续。
@isnad1 id=continuo.0h0v.s3.a4eac3e8d78b from=translated src=- shape=e3d48bcb vocab=4fef6fe1
-/
theorem continuous_exp : Continuous (Real.exp : ℝ → ℝ) := by
  exact Real.continuous_exp

/-- 指数函数的导数仍为指数函数本身。
@isnad1 id=eq.0h1v.s5.7abf2ae62a1f from=translated src=- shape=a89f2a74 vocab=63b268e0
-/
theorem deriv_exp (x : ℝ) : deriv Real.exp x = Real.exp x := by
  exact (Real.hasDerivAt_exp x).deriv

/-- 正弦函数在整个实轴上连续。
@isnad1 id=continuo.0h0v.s3.9c7810a69e66 from=translated src=- shape=e3d48bcb vocab=253553a9
-/
theorem continuous_sin : Continuous (Real.sin : ℝ → ℝ) := by
  exact Real.continuous_sin

/-- 余弦函数在整个实轴上连续。
@isnad1 id=continuo.0h0v.s3.547b0969a375 from=translated src=- shape=e3d48bcb vocab=89443aaa
-/
theorem continuous_cos : Continuous (Real.cos : ℝ → ℝ) := by
  exact Real.continuous_cos

/-- 正弦函数的导数是余弦函数。
@isnad1 id=eq.0h1v.s5.3033b594437a from=translated src=- shape=a89f2a74 vocab=50857409
-/
theorem deriv_sin (x : ℝ) : deriv Real.sin x = Real.cos x := by
  exact (Real.hasDerivAt_sin x).deriv

/-- 余弦函数的导数是负的正弦函数。
> **Entry**: analysis.special-functions.basic
@isnad1 id=eq.0h1v.s5.07d2dc712e07 from=translated src=- shape=42da7676 vocab=0d6b1501
-/
theorem deriv_cos (x : ℝ) : deriv Real.cos x = -Real.sin x := by
  exact (Real.hasDerivAt_cos x).deriv

/-! ### 对数、正切与自然幂函数 -/

/-- 非零实数乘法下，对数满足加法公式。
@isnad1 id=eq.2h2v.s5.871a30c01d26 from=translated src=- shape=eff8b0f5 vocab=7e9fb820
-/
theorem log_mul (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) = Real.log x + Real.log y := by
  exact Real.log_mul hx hy

/-- 对数函数在正半轴上连续。
@isnad1 id=continuo.0h0v.s4.1ada115face7 from=translated src=- shape=f2a09be3 vocab=f17a4541
-/
theorem continuousOn_log : ContinuousOn Real.log (Set.Ioi 0) := by
  exact Real.continuousOn_log.mono (by
    intro x hx
    exact ne_of_gt hx)

/-- 对数函数在非零点的导数为 `1 / x`。
@isnad1 id=eq.1h1v.s5.06e025b4c2c8 from=translated src=- shape=d25061a1 vocab=35d1f222
-/
theorem deriv_log (x : ℝ) (hx : x ≠ 0) : deriv Real.log x = 1 / x := by
  simpa [one_div] using (Real.hasDerivAt_log hx).deriv

/-! ### 对数函数的教材层基本性质 -/

/-- 对数函数在正半轴上严格递增。
@isnad1 id=strictmo.0h0v.s3.0019682f67d9 from=translated src=- shape=f2a09be3 vocab=b8a20ac3
-/
theorem strictMonoOn_log_pos : StrictMonoOn Real.log (Set.Ioi 0) := by
  exact Real.strictMonoOn_log

/-- 正数经过 `log` 后再取指数，恢复原数。
@isnad1 id=eq.1h1v.s4.14c8608cc906 from=translated src=- shape=cc7bc718 vocab=6e6e066f
-/
theorem exp_log_pos {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x) = x := by
  exact Real.exp_log hx

/-- 指数函数经过 `log` 后恢复原数，说明 `log` 是 `exp` 的反函数。
@isnad1 id=eq.0h1v.s3.e0dd0589269f from=translated src=- shape=47dcad53 vocab=40c7069c
-/
theorem log_exp (x : ℝ) : Real.log (Real.exp x) = x := by
  exact Real.log_exp x

/-- 正数乘法下的对数加法公式。
> **Entry**: analysis.special-functions.log
@isnad1 id=eq.2h2v.s5.640e2140d53f from=translated src=- shape=019488d2 vocab=c51a7605
-/
theorem log_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x * y) = Real.log x + Real.log y := by
  exact Real.log_mul hx.ne' hy.ne'

/-- 在余弦不为零的点，正切函数的导数为 `1 / cos² x`。
@isnad1 id=eq.1h1v.s6.b66b5925e0b8 from=translated src=- shape=eebe44a5 vocab=29e99c9d
-/
theorem deriv_tan (x : ℝ) (hcos : Real.cos x ≠ 0) :
    deriv Real.tan x = 1 / (Real.cos x) ^ 2 := by
  exact (Real.hasDerivAt_tan hcos).deriv

/-- 任意自然幂函数在实轴上连续。
@isnad1 id=continuo.0h1v.s4.ad5cd898e876 from=translated src=- shape=786514b0 vocab=a53b02ca
-/
theorem continuous_pow_nat (n : ℕ) : Continuous (fun x : ℝ => x ^ n) := by
  exact continuous_id.pow n

/-- 自然幂函数的导数公式。
> **Entry**: analysis.special-functions.log-tan-pow
@isnad1 id=eq.0h2v.s6.b97efcb89562 from=translated src=- shape=b0d39898 vocab=a5f06a90
-/
theorem deriv_pow_nat (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => y ^ n) x = (n : ℝ) * x ^ (n - 1) := by
  simpa [Function.id_def, mul_assoc] using (hasDerivAt_id x).pow n |>.deriv

/-! ### 反三角函数的教材层基本性质 -/

/-- 反正切函数在整个实轴上连续。
@isnad1 id=continuo.0h0v.s3.105d89432641 from=translated src=- shape=e3d48bcb vocab=4e84f1a0
-/
theorem continuous_arctan : Continuous (Real.arctan : ℝ → ℝ) := by
  exact Real.continuous_arctan

/-- 反正切函数的导数公式。
@isnad1 id=eq.0h1v.s6.6606dcfa2a63 from=translated src=- shape=45584fc7 vocab=8b31eb82
-/
theorem deriv_arctan (x : ℝ) : deriv Real.arctan x = 1 / (1 + x ^ 2) := by
  exact (Real.hasDerivAt_arctan x).deriv

/-- `tan` 与 `arctan` 在实轴上互为右逆。
@isnad1 id=eq.0h1v.s3.25dd4558c28b from=translated src=- shape=47dcad53 vocab=2cf98e61
-/
theorem tan_arctan (x : ℝ) : Real.tan (Real.arctan x) = x := by
  exact Real.tan_arctan x

/-- 反正弦函数在整个实轴上连续。
@isnad1 id=continuo.0h0v.s3.658e0d3f1b6d from=translated src=- shape=e3d48bcb vocab=5527be24
-/
theorem continuous_arcsin : Continuous (Real.arcsin : ℝ → ℝ) := by
  exact Real.continuous_arcsin

/-- 反余弦函数在整个实轴上连续。
> **Entry**: analysis.special-functions.tan-pow
@isnad1 id=continuo.0h0v.s3.42211ffe7878 from=translated src=- shape=e3d48bcb vocab=673532c3
-/
theorem continuous_arccos : Continuous (Real.arccos : ℝ → ℝ) := by
  exact Real.continuous_arccos

/-- 反正弦在不触及端点 `±1` 的点的导数。
@isnad1 id=hasderiv.2h1v.s6.724d753d5f7e from=translated src=- shape=95bb91cd vocab=553b966f
-/
theorem hasDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
  exact Real.hasDerivAt_arcsin h₁ h₂

/-- 反余弦在不触及端点 `±1` 的点的导数。
@isnad1 id=hasderiv.2h1v.s6.7fc32853ab4c from=translated src=- shape=60ecba4e vocab=11a75915
-/
theorem hasDerivAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - x ^ 2))) x := by
  exact Real.hasDerivAt_arccos h₁ h₂

end Analysis.SpecialFunctions
end SandronesLibrary
