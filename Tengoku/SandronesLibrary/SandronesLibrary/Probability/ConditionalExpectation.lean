/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Expectation
import Tengoku.Seed.Probability.ConditionalExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 条件期望

给定环境可测空间 `m₀`、子 σ-代数 `m ≤ m₀` 和测度 `μ`，条件期望
`μ[X | m]` 是 `X` 在 `m` 所含信息下的最佳可积代表。它对 `m` 强可测，并且在每个
`m`-可测集合上的积分都与 `X` 相同；这两个性质也在几乎处处相等的意义下刻画它。

正式承载直接使用 Mathlib 的 `MeasureTheory.condExp`，不另造条件期望结构。需要特别注意：
`condExp` 是一个全定义函数；当 `m ≰ m₀`、`μ.trim hm` 不是 σ-有限测度，或 `X` 不可积时，
它按约定退化为零。下列教材定理因此显式保留子 σ-代数、σ-有限性和可积性条件。

> **Entry**: probability.conditional-expectation.definition
-/

namespace SandronesLibrary.Probability

open MeasureTheory
open scoped ProbabilityTheory ENNReal

/-- 条件期望是关于条件 σ-代数强可测的函数。-/
theorem conditionalExpectation_stronglyMeasurable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → E} :
    StronglyMeasurable[m] (μ[X | m]) :=
  stronglyMeasurable_condExp

/-- Banach 空间值函数的条件期望可积。这个结论也覆盖 `condExp` 退化为零的分支。-/
theorem conditionalExpectation_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {m : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → E} :
    Integrable (μ[X | m]) μ :=
  integrable_condExp

/-- 条件期望在每个条件 σ-代数可测集合上的积分与原函数相同。-/
theorem conditionalExpectation_setIntegral
    {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} {X : Ω → E}
    (hm : m ≤ m₀) [SigmaFinite (@Measure.trim Ω m m₀ μ hm)] (hX : Integrable X μ)
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    (∫ ω in s, (μ[X | m]) ω ∂μ) = ∫ ω in s, X ω ∂μ :=
  setIntegral_condExp (m := m) (m₀ := m₀) (μ := μ) hm hX hs

/-- 全期望公式：可积随机变量与其条件期望有相同的期望。-/
theorem expectation_conditionalExpectation
    {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} {X : Ω → E}
    (hm : m ≤ m₀) [SigmaFinite (@Measure.trim Ω m m₀ μ hm)] (hX : Integrable X μ) :
    (∫ ω, (μ[X | m]) ω ∂μ) = ∫ ω, X ω ∂μ :=
  by
    simpa only [setIntegral_univ] using
      (@conditionalExpectation_setIntegral Ω E m₀ _ _ _ m μ X hm inferInstance hX
        Set.univ MeasurableSet.univ)

/-- 若可积函数已经关于条件 σ-代数 a.e. 强可测，则取条件期望不改变它（a.e.）。-/
theorem conditionalExpectation_ae_eq_self
    {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {m : MeasurableSpace Ω} {μ : @Measure Ω m₀} {X : Ω → E}
    (hm : m ≤ m₀) [SigmaFinite (@Measure.trim Ω m m₀ μ hm)]
    (hXm : AEStronglyMeasurable[m] X μ) (hX : Integrable X μ) :
    μ[X | m] =ᵐ[μ] X :=
  condExp_of_aestronglyMeasurable' (m := m) (m₀ := m₀) (μ := μ) hm hXm hX

/-- 概率测度下，常随机变量的条件期望仍是同一个常随机变量。-/
theorem conditionalExpectation_const
    {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : MeasurableSpace Ω} (μ : @Measure Ω m₀) [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) (c : E) :
    μ[fun _ : Ω ↦ c | m] = fun _ ↦ c :=
  condExp_const (m := m) (m₀ := m₀) (μ := μ) hm c

end SandronesLibrary.Probability
