/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.ConditionalExpectationTower
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.IndependenceVariables

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 独立性与条件期望

若随机变量 `X` 所生成的信息与条件 σ-代数独立，那么观察该 σ-代数不会改变对 `X` 的预测：
`E[X | m]` 几乎处处等于常数 `E[X]`。本文件先给出独立 σ-代数版本，再由 `IndepFun` 推出
独立随机变量版本。

> **Entry**: probability.conditional-expectation.independence
-/

namespace SandronesLibrary.Probability

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- 若 `X` 关于 `mX` 强可测，且 `mX` 与条件 σ-代数 `mC` 独立，则条件期望退化为常期望。
@isnad1 id=eventual.4h7v.s6.3e8ee5cd0ba2 from=translated src=- shape=ca4d0ea7 vocab=2113f057
-/
theorem conditionalExpectation_eq_expectation_of_indep
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {mX mC m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀} {X : Ω → E}
    (hmX : mX ≤ m₀) (hmC : mC ≤ m₀)
    [SigmaFinite (@Measure.trim Ω mC m₀ μ hmC)]
    (hX : StronglyMeasurable[mX] X) (hIndep : Indep mX mC μ) :
    μ[X | mC] =ᵐ[μ] fun _ => ∫ ω, X ω ∂μ :=
  condExp_indep_eq hmX hmC hX hIndep

/-- 独立随机变量版本：给定 `Y` 的信息后，`X` 的条件期望仍等于 `X` 的普通期望。
@isnad1 id=eventual.3h6v.s7.757df9963e11 from=translated src=- shape=d6224b5f vocab=e8842d25
-/
theorem conditionalExpectation_comap_eq_expectation_of_indepFun
    {Ω E S : Type*} [m₀ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace S] {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    {X : Ω → E} {Y : Ω → S} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) :
    μ[X | MeasurableSpace.comap Y inferInstance] =ᵐ[μ] fun _ => ∫ ω, X ω ∂μ := by
  exact conditionalExpectation_eq_expectation_of_indep hX.comap_le hY.comap_le
    (comap_measurable X).stronglyMeasurable hXY

end SandronesLibrary.Probability
