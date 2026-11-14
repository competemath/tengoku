/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Convergence
import Tengoku.Seed.Probability.Distributions.Gaussian.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 分布收敛的随机变量桥

本库在 `probability.convergence.modes` 中直接复用 Mathlib 的
`MeasureTheory.TendstoInDistribution` 作为随机变量层“依分布收敛”的正式承载。该结构把教材的
“随机变量序列 `Y n` 依分布收敛到 `Z`”定义为**推前概率测度**在 `ProbabilityMeasure ℝ` 上的
弱收敛。

本文件补齐缺失的一侧接口：当分析链已经在 `ProbabilityMeasure ℝ` 层建立了弱收敛，并且已经
知道极限随机变量 `Z` 的分布时，如何回到 `TendstoInDistribution`。没有这条桥，围绕特征函数
或测度紧性得到的弱收敛结论无法直接喂给只接受 `TendstoInDistribution` 的下游定理。

`lawProbabilityMeasure` 把单个随机变量的推前分布打包成 `ProbabilityMeasure ℝ`，它是这条桥
接收的正式载体；`tendstoInDistribution_of_tendsto_law_gaussian` 则把弱收敛假设直接组装为
`TendstoInDistribution` 的三个字段。

> **Entry**: probability.convergence.distribution-bridge
-/

namespace SandronesLibrary.Probability

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- 随机变量 `Y` 关于 `P` 的推前分布，打包为概率测度 `ProbabilityMeasure ℝ`。-/
noncomputable def lawProbabilityMeasure (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    ProbabilityMeasure ℝ :=
  ⟨P.map Y, Measure.isProbabilityMeasure_map hY⟩

/-- 若随机变量序列的推前概率测度在 `ProbabilityMeasure ℝ` 中弱收敛到标准正态测度，且
`Z` 的分布恰为标准正态，则 `Y` 依分布收敛到 `Z`。

这是 `TendstoInDistribution` 的构造形式：`tendsto` 字段只要求推前测度的弱收敛。把 `Z` 的
分布改写为 `gaussianReal 0 1` 后，假设 `h` 就是所需的弱收敛证明。-/
theorem tendstoInDistribution_of_tendsto_law_gaussian
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hY : ∀ n, AEMeasurable (Y n) P) (hZ : AEMeasurable Z P')
    (hZlaw : P'.map Z = gaussianReal 0 1)
    (h : Tendsto (fun n ↦ lawProbabilityMeasure (Y n) (hY n)) atTop
      (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) :
    TendstoInDistribution Y atTop Z (fun _ ↦ P) P' where
  forall_aemeasurable := hY
  aemeasurable_limit := hZ
  tendsto := by
    simpa [hZlaw, lawProbabilityMeasure] using h

end

end SandronesLibrary.Probability
