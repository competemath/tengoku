/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Expectation
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.IndependenceEvents
import Tengoku.Seed.Probability.Independence.Integration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 随机变量的独立性

随机变量 `X`、`Y` 独立，是指它们生成的 σ-代数独立。正式承载直接使用
`ProbabilityTheory.IndepFun X Y μ`，记作 `X ⟂ᵢ[μ] Y`。本文件给出可测事件原像的教材
刻画、可测变换保持独立以及独立可积变量的乘积期望公式。

> **Entry**: probability.independence.variables
-/

namespace SandronesLibrary.Probability

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- 随机变量独立的事件原像刻画。-/
theorem independentRandomVariables_iff
    {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure Ω} {X : Ω → E} {Y : Ω → F} :
    X ⟂ᵢ[μ] Y ↔ ∀ A : Set E, ∀ B : Set F,
      MeasurableSet A → MeasurableSet B →
        μ (X ⁻¹' A ∩ Y ⁻¹' B) = μ (X ⁻¹' A) * μ (Y ⁻¹' B) :=
  indepFun_iff_measure_inter_preimage_eq_mul

/-- 分别对两个独立随机变量施加可测变换后仍独立。-/
theorem independentRandomVariables_comp
    {Ω E F G H : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] [MeasurableSpace H] {μ : Measure Ω}
    {X : Ω → E} {Y : Ω → F} {g : E → G} {h : F → H}
    (hXY : X ⟂ᵢ[μ] Y) (hg : Measurable g) (hh : Measurable h) :
    (g ∘ X) ⟂ᵢ[μ] (h ∘ Y) :=
  hXY.comp hg hh

/-- 两个独立且可积的实值随机变量之积仍可积。-/
theorem independent_integrable_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (X * Y) μ :=
  hXY.integrable_mul hX hY

/-- 独立可积实值随机变量的乘积期望等于期望乘积。-/
theorem expectation_mul_eq_mul_expectation_of_independent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ ω, X ω * Y ω ∂μ) = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ :=
  hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

end SandronesLibrary.Probability
