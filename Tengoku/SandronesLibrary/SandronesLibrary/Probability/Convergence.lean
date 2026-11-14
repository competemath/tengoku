/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInDistribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 随机变量的四种收敛模式

对随机变量序列 `X n` 和候选极限 `Z`，概率论中常用四种不同的收敛概念：

* 几乎必然收敛：除去零测集后逐点收敛；
* 概率收敛：任意固定误差阈值被超过的概率趋于零；
* `Lᵖ` 收敛：差的 `Lᵖ` 范数趋于零；
* 分布收敛：随机变量的推前概率测度弱收敛。

本文件不把四种模式塞进一个新结构。几乎必然收敛直接用 a.e. 逐点 `Tendsto`；概率收敛直接用
`MeasureTheory.TendstoInMeasure`；`Lᵖ` 收敛直接用 `eLpNorm` 趋零；分布收敛直接使用
`MeasureTheory.TendstoInDistribution`。随后复用 Mathlib 建立标准单向蕴含链、概率收敛的 a.s.
子列以及连续映射定理。

这些箭头一般不可逆。特别是概率收敛只保证存在几乎必然收敛的子列，不能推出原序列几乎必然
收敛；分布收敛也不推出概率收敛。

> **Entry**: probability.convergence.modes
-/

namespace SandronesLibrary.Probability

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

/-- 几乎必然收敛的教材展开：在 `μ`-几乎每个样本点上，数列在值域拓扑中收敛。-/
theorem almostSurelyConverges_iff_ae_tendsto
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (Z : Ω → E) :
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Z ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Z ω)) :=
  Iff.rfl

/-- 概率测度下，`TendstoInMeasure` 等价于教材的概率收敛定义。-/
theorem convergesInProbability_iff_measureReal_dist
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (Z : Ω → E) :
    TendstoInMeasure μ X atTop Z ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n ↦ μ.real {ω | ε ≤ dist (X n ω) (Z ω)}) atTop (𝓝 0) :=
  tendstoInMeasure_iff_measureReal_dist

/-- 概率空间上的几乎必然收敛蕴含概率收敛。-/
theorem almostSurelyConverges_inProbability
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {Z : Ω → E}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hXZ : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Z ω))) :
    TendstoInMeasure μ X atTop Z :=
  tendstoInMeasure_of_tendsto_ae hX hXZ

/-- `Lᵖ` 收敛蕴含概率收敛。

这里直接对普通函数使用扩展 `Lᵖ` 范数 `eLpNorm`，不要求先把随机变量打包为 `Lp` 商空间元素。
条件 `p ≠ 0` 是 Markov 型估计所需的真实指数边界；定理同时覆盖 `p = ∞`。-/
theorem convergesInLp_inProbability
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) {p : ℝ≥0∞} (hp : p ≠ 0)
    {X : ℕ → Ω → E} {Z : Ω → E}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hZ : AEStronglyMeasurable Z μ)
    (hXZ : Tendsto (fun n ↦ eLpNorm (X n - Z) p μ) atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop Z :=
  tendstoInMeasure_of_tendsto_eLpNorm hp hX hZ hXZ

/-- 在 Borel 度量值域中，概率收敛蕴含分布收敛。-/
theorem convergesInProbability_inDistribution
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {Z : Ω → E}
    (hXZ : TendstoInMeasure μ X atTop Z)
    (hX : ∀ n, AEMeasurable (X n) μ) :
    TendstoInDistribution X atTop Z (fun _ ↦ μ) μ :=
  hXZ.tendstoInDistribution hX

/-- 几乎必然收敛通过“a.s. → 概率 → 分布”的正式链蕴含分布收敛。-/
theorem almostSurelyConverges_inDistribution
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {Z : Ω → E}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hXZ : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Z ω))) :
    TendstoInDistribution X atTop Z (fun _ ↦ μ) μ :=
  (almostSurelyConverges_inProbability μ hX hXZ).tendstoInDistribution
    (fun n ↦ (hX n).aemeasurable)

/-- 概率收敛序列存在一个严格递增子列，沿该子列几乎必然收敛到同一极限。

结论只涉及选出的子列 `X (ns k)`，不能误读为原序列已经几乎必然收敛。-/
theorem convergesInProbability_has_almostSurelyConvergent_subsequence
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    {μ : Measure Ω} {X : ℕ → Ω → E} {Z : Ω → E}
    (hXZ : TendstoInMeasure μ X atTop Z) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k ↦ X (ns k) ω) atTop (𝓝 (Z ω)) :=
  hXZ.exists_seq_tendsto_ae

/-- 分布收敛的连续映射定理：连续函数保持分布收敛。-/
theorem convergenceInDistribution_continuousMapping
    {Ω E F : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {Z : Ω → E} {g : E → F}
    (hg : Continuous g)
    (hXZ : TendstoInDistribution X atTop Z (fun _ ↦ μ) μ) :
    TendstoInDistribution (fun n ↦ g ∘ X n) atTop (g ∘ Z) (fun _ ↦ μ) μ :=
  hXZ.continuous_comp hg

end

end SandronesLibrary.Probability
