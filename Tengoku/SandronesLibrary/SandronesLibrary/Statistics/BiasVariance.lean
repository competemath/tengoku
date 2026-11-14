/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Estimator
import Tengoku.Seed.Probability.Moments.Variance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 平方损失的偏差—方差分解

设实值估计量的输出为 `Y`，要估计的真实值为 `a`。均方误差满足

`E[(Y-a)²] = Var(Y) + (E[Y]-a)²`。

右端第二项是偏差的平方。这个等式把误差分成随机波动和系统偏移两部分，是比较实值估计量的基本
工具。

本文件先在任意概率测度上证明纯积分恒等式，再把它应用到统计模型 `P : Kernel Θ 𝓧` 和随机化
估计量 `κ : Kernel 𝓧 ℝ`。固定参数 `θ` 时，输出分布是 `(κ ∘ₖ P) θ`。平方损失使用与既有风险
接口一致的 `ℝ≥0∞` 值函数 `ENNReal.ofReal ((y - τ θ)²)`，最终消费者把原生 `lintegral` 风险精确
改写为方差与偏差平方之和的 `ENNReal.ofReal`。

本文件不另建 `Bias`、`Loss` 或逐参数 `Risk` 定义。偏差保留为“输出均值减真实目标”的表达式；
二阶矩条件 `MemLp id 2 ((κ ∘ₖ P) θ)` 逐参数显式保留，不能由 Markov 性推出。

> **Entry**: statistics.estimator.bias-variance
-/

namespace SandronesLibrary.Statistics

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- 若实值目标 `τ` 可测，则平方损失 `(θ,y) ↦ (y-τ θ)²` 作为 `ℝ≥0∞` 值函数联合可测。
@isnad1 id=measurab.1h2v.s6.e36dac63cf6d from=translated src=- shape=635be326 vocab=cfc94f1b
-/
theorem squaredLoss_jointlyMeasurable
    {Θ : Type*} [MeasurableSpace Θ] (τ : Θ → ℝ) (hτ : Measurable τ) :
    Measurable
      (Function.uncurry fun (θ : Θ) (y : ℝ) ↦ ENNReal.ofReal ((y - τ θ) ^ 2)) := by
  fun_prop

/-- 概率测度上的均方误差等于方差加偏差平方。

这里 `a` 是要估计的真实值，`∫ Y - a` 是偏差。二次可积性同时保证展开中所有一阶和二阶积分
合法。
@isnad1 id=eq.1h4v.s7.e179a0293179 from=translated src=- shape=9d1ff7c1 vocab=7d923ff7
-/
theorem squaredError_integral_eq_variance_add_bias_sq
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Ω → ℝ) (hY : MemLp Y 2 ν) (a : ℝ) :
    ∫ ω, (Y ω - a) ^ 2 ∂ν = Var[Y; ν] + (∫ ω, Y ω ∂ν - a) ^ 2 := by
  have hYint : Integrable Y ν := hY.integrable (by norm_num)
  have hYsq : Integrable (fun ω ↦ (Y ω) ^ 2) ν :=
    (memLp_two_iff_integrable_sq hY.1).mp hY
  calc
    ∫ ω, (Y ω - a) ^ 2 ∂ν =
        ∫ ω, (Y ω) ^ 2 - (2 * a) * Y ω + a ^ 2 ∂ν := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, (Y ω) ^ 2 - (2 * a) * Y ω ∂ν) + ∫ _ : Ω, a ^ 2 ∂ν := by
      exact integral_add (hYsq.sub (hYint.const_mul _)) (integrable_const _)
    _ = (∫ ω, (Y ω) ^ 2 ∂ν) - (2 * a) * (∫ ω, Y ω ∂ν) + a ^ 2 := by
      rw [integral_sub hYsq (hYint.const_mul _), integral_const_mul, integral_const]
      simp
    _ = Var[Y; ν] + (∫ ω, Y ω ∂ν - a) ^ 2 := by
      rw [variance_eq_sub hY]
      simp only [Pi.pow_apply]
      ring

/-- 实值随机化估计量在固定参数下的平方损失风险分解。

`(κ ∘ₖ P) θ` 是估计输出的概率分布。左端保持 estimator 定义条目采用的原生 `lintegral` 风险；
右端第一项是输出方差，第二项是输出均值相对目标 `τ θ` 的偏差平方。
@isnad1 id=eq.1h6v.s8.de35d501d1e8 from=translated src=- shape=c4d7b692 vocab=53db2714
-/
theorem estimator_squaredLossRisk_eq_variance_add_bias_sq
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (κ : Kernel 𝓧 ℝ) [IsMarkovKernel κ]
    (τ : Θ → ℝ) (θ : Θ)
    (hκ : MemLp id 2 ((κ ∘ₖ P) θ)) :
    ∫⁻ y, ENNReal.ofReal ((y - τ θ) ^ 2) ∂((κ ∘ₖ P) θ) =
      ENNReal.ofReal
        (Var[id; (κ ∘ₖ P) θ] + (∫ y, y ∂((κ ∘ₖ P) θ) - τ θ) ^ 2) := by
  let ν : Measure ℝ := (κ ∘ₖ P) θ
  have hshift : MemLp (fun y : ℝ ↦ y - τ θ) 2 ν := by
    convert hκ.sub (memLp_const (τ θ)) using 1
    ext y
    rfl
  have hsq : Integrable (fun y : ℝ ↦ (y - τ θ) ^ 2) ν :=
    (memLp_two_iff_integrable_sq hshift.1).mp hshift
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (.of_forall fun y ↦ sq_nonneg _)]
  exact congrArg ENNReal.ofReal
    (squaredError_integral_eq_variance_add_bias_sq ν id hκ (τ θ))

end SandronesLibrary.Statistics
