/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Distribution
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Function.L1Space.Integrable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 期望与可积性

随机变量的期望就是相对于概率测度的 Bochner 积分。正式承载使用 `MeasureTheory.integral`，
有限期望使用 `Integrable`；本库不另造 `Expectation` 运算。Bochner 积分对不可积函数被约定为
零，因此教材中的线性和单调性定理显式保留可积条件。

> **Entry**: probability.expectation.definition
-/

namespace SandronesLibrary.Probability

open MeasureTheory
open scoped ProbabilityTheory ENNReal

/-- 有限期望与属于 `L¹` 是同一条件。-/
theorem integrable_iff_memLp_one
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [ContinuousENorm E]
    {μ : Measure Ω} {X : Ω → E} :
    Integrable X μ ↔ MemLp X 1 μ :=
  memLp_one_iff_integrable.symm

/-- 两个可积随机变量之和的期望等于期望之和。-/
theorem expectation_add
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {X Y : Ω → E} (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ ω, X ω + Y ω ∂μ) = (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ :=
  integral_add hX hY

/-- 实值常随机变量在概率测度下的期望就是该常数。-/
theorem expectation_const
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℝ) : (∫ _ : Ω, c ∂μ) = c := by
  simp

/-- 可积实值随机变量的 a.e. 次序被期望保持。-/
theorem expectation_mono
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) (hXY : X ≤ᵐ[μ] Y) :
    (∫ ω, X ω ∂μ) ≤ ∫ ω, Y ω ∂μ :=
  integral_mono_ae hX hY hXY

end SandronesLibrary.Probability
