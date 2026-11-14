/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.CharacteristicFunction
import Tengoku.Seed.MeasureTheory.Measure.LevyConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lévy 连续性定理的概率测度接口

对实直线上的概率测度序列，Lévy 连续性定理把弱收敛准确刻画为特征函数的逐点收敛。本文件直接
复用 `ProbabilityMeasure ℝ` 上的弱收敛拓扑与 Mathlib 的有限维 Lévy 定理，不另造一个同义的
“依分布收敛”结构。

已知目标概率测度 `μ₀` 时，目标函数就是 `charFun μ₀`，它自动在零点连续，因此
`probabilityMeasure_tendsto_iff_charFun` 的签名无需额外连续性前提。若只知道特征函数趋于任意函数
`f`，连续性不能省略；`tight_of_charFun_tendsto_continuousAt_zero` 在 `ContinuousAt f 0` 下只先推出
测度族紧，不把尚未识别的 `f` 冒充某个概率测度的特征函数。

> **Entry**: probability.characteristic-function.levy-continuity
-/

namespace SandronesLibrary.Probability

open MeasureTheory Filter
open scoped Topology

/-- 实直线上的概率测度弱收敛，当且仅当其特征函数对每个实参数逐点收敛到目标测度的特征函数。
@isnad1 id=iff.0h2v.s6.97a5f3d1b28b from=translated src=- shape=be557cc7 vocab=2bc7f759
-/
theorem probabilityMeasure_tendsto_iff_charFun
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ} :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t)) := by
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun

/-- 若概率测度序列的特征函数逐点趋于一个在零点连续的函数，则该测度序列构成紧测度族。

结论只是 tightness；它没有单独断言任意点态极限 `f` 已经是某个概率测度的特征函数。
@isnad1 id=istightm.2h2v.s6.bb5a825e4d42 from=translated src=- shape=e0925912 vocab=3ef15a0f
-/
theorem tight_of_charFun_tendsto_continuousAt_zero
    {μ : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (μ n)]
    {f : ℝ → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range μ) := by
  exact isTightMeasureSet_of_tendsto_charFun hf h

end SandronesLibrary.Probability
