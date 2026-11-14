/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Moments
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Markov
import Tengoku.Seed.Analysis.Convex.Integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Markov、Chebyshev 与 Jensen 不等式

本文件把三个经典概率不等式以教材条件公开，证明直接消费 Mathlib 的正式定理。Markov 使用
`ℝ≥0∞` 值非负函数和非负积分；Chebyshev 对实值 `L²` 随机变量使用普通方差；Jensen 保留
凸函数定义域、连续性、闭性和两个可积性条件。

> **Entry**: probability.inequalities.basic
-/

namespace SandronesLibrary.Probability

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-- Markov 不等式：非负可测量的超水平集概率由其非负积分控制。
@isnad1 id=le.3h4v.s6.e35bc08474e1 from=translated src=- shape=6029d244 vocab=d8eb0b9e
-/
theorem markov_inequality
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : AEMeasurable X μ) {a : ℝ≥0∞} (ha0 : a ≠ 0) (haTop : a ≠ ⊤) :
    μ {ω | a ≤ X ω} ≤ (∫⁻ ω, X ω ∂μ) / a :=
  meas_ge_le_lintegral_div hX ha0 haTop

/-- Chebyshev 不等式：偏离期望至少 `c` 的概率由方差除以 `c²` 控制。
@isnad1 id=le.2h4v.s7.a9b62cb65ed1 from=translated src=- shape=630c91ca vocab=f2608bd6
-/
theorem chebyshev_inequality
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |X ω - ∫ x, X x ∂μ|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2) :=
  meas_ge_le_variance_div_sq hX hc

/-- 概率测度版本 Jensen 不等式。
@isnad1 id=le.6h6v.s8.04c2eff77b6f from=translated src=- shape=8c900df9 vocab=4637d58d
-/
theorem jensen_inequality
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Set E} {X : Ω → E} {g : E → ℝ}
    (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hXs : ∀ᵐ ω ∂μ, X ω ∈ s) (hX : Integrable X μ)
    (hgX : Integrable (g ∘ X) μ) :
    g (∫ ω, X ω ∂μ) ≤ ∫ ω, g (X ω) ∂μ :=
  hg.map_integral_le hgc hsc hXs hX hgX

end SandronesLibrary.Probability
