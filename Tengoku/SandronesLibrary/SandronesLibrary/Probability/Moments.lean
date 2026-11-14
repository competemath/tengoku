/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Expectation
import Tengoku.Seed.Probability.Moments.Variance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 矩、方差与协方差

本文件直接采用 Mathlib 的 `moment`、`centralMoment`、`evariance`、`variance` 和
`covariance`。普通实方差 `variance` 是扩展方差 `evariance` 的 `toReal`；若二阶矩无限，
它会退化为零。因此教材中的二阶矩公式必须显式假设 `MemLp X 2 μ`。

> **Entry**: probability.moments.variance
-/

namespace SandronesLibrary.Probability

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-- 有限二阶矩下的教材方差公式 `Var X = E[X²] - (E X)²`。
@isnad1 id=eq.1h3v.s7.354802fa507f from=translated src=- shape=58e5624f vocab=296e54a4
-/
theorem variance_eq_secondMoment_sub_expectation_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[X; μ] = (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 :=
  variance_eq_sub hX

/-- 有限二阶矩下的协方差公式。
@isnad1 id=eq.2h4v.s7.a7025fdcaf24 from=translated src=- shape=8877b92a vocab=5e431b89
-/
theorem covariance_eq_productExpectation_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] = (∫ ω, X ω * Y ω ∂μ) - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ :=
  covariance_eq_sub hX hY

/-- 方差总是非负。
@isnad1 id=le.0h3v.s4.afcc43ee2c35 from=translated src=- shape=8a5e53fd vocab=6e00d829
-/
theorem variance_nonnegative
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) :
    0 ≤ Var[X; μ] :=
  variance_nonneg X μ

/-- 对 a.e. 强可测随机变量，扩展方差有限当且仅当它属于 `L²`。
@isnad1 id=iff.1h3v.s6.5c323e081e8f from=translated src=- shape=9b42bcea vocab=c84a732a
-/
theorem evariance_lt_top_iff_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) :
    eVar[X; μ] < ⊤ ↔ MemLp X 2 μ :=
  evariance_lt_top_iff_memLp hX

/-- Mathlib 普通实方差在不属于 `L²` 时取零；课程使用时必须注意这一全定义约定。
@isnad1 id=eq.2h3v.s6.b15fe166279e from=translated src=- shape=f7ee7ccc vocab=49ddac82
-/
theorem variance_eq_zero_of_not_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) (hX2 : ¬ MemLp X 2 μ) :
    Var[X; μ] = 0 :=
  variance_of_not_memLp hX hX2

end SandronesLibrary.Probability
