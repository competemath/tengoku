/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.BiasVariance
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Convergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 估计量的逐参数相合性

本文件考虑共同观测空间 `𝓧` 上的一列确定性实值估计量 `T n : 𝓧 → ℝ`。统计模型
`P : Kernel Θ 𝓧` 在参数 `θ` 下给出概率测度 `P θ`，目标值是 `τ θ`。逐参数相合是指，对每个固定
参数，`T n` 在 `P θ` 下依概率收敛到常数 `τ θ`。

共同观测空间可理解为无限样本轨道空间，每个 `T n` 使用前 `n` 份信息。本条目不额外编码“只依赖
前 n 个坐标”的 filtration 条件。采用共同空间使所有估计量位于同一个概率空间上，因而能够准确
复用 `TendstoInMeasure`；一般变化样本空间或未给共同 coupling 的随机化 kernel 序列不能静默套用
这个接口。

本文件给出逐参数相合的偏差概率展开，以及 `L²` 误差趋零蕴含概率相合。后者是均方相合的稳定
Lean carrier，并为偏差—方差分解的后续消费者提供出口。本条目不从逐参数相合推出一致相合。

> **Entry**: statistics.estimator.consistency
-/

namespace SandronesLibrary.Statistics

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

/-- 固定参数 `θ` 时，依概率相合等价于每个正误差阈值的偏差概率趋于零。-/
theorem pointwiseConsistency_iff
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (T : ℕ → 𝓧 → ℝ) (τ : Θ → ℝ) (θ : Θ) :
    TendstoInMeasure (P θ) T atTop (fun _ ↦ τ θ) ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n ↦ (P θ).real {x | ε ≤ |T n x - τ θ|}) atTop (𝓝 0) := by
  simpa [Real.dist_eq] using
    SandronesLibrary.Probability.convergesInProbability_iff_measureReal_dist
      (P θ) T (fun _ ↦ τ θ)

/-- 固定参数下，`L²` 误差趋零蕴含估计量依概率相合。

条件使用扩展 `L²` 半范数，避免在定义阶段把函数打包成 `Lp` 商空间。每个 `T n` 的 a.e. 强可测性
是 `TendstoInMeasure` 与 `eLpNorm` 桥所需的真实条件。-/
theorem pointwiseConsistent_of_L2
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (T : ℕ → 𝓧 → ℝ) (τ : Θ → ℝ) (θ : Θ)
    (hT : ∀ n, AEStronglyMeasurable (T n) (P θ))
    (hL2 : Tendsto
      (fun n ↦ eLpNorm (T n - fun _ ↦ τ θ) 2 (P θ)) atTop (𝓝 0)) :
    TendstoInMeasure (P θ) T atTop (fun _ ↦ τ θ) := by
  exact SandronesLibrary.Probability.convergesInLp_inProbability
    (μ := P θ) (p := 2) (by norm_num) hT aestronglyMeasurable_const hL2

end SandronesLibrary.Statistics
