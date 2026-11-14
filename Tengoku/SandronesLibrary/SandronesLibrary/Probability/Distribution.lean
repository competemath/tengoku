/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Variable
import Tengoku.Seed.MeasureTheory.Measure.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 随机变量的分布

随机变量 `X : Ω → E` 在概率测度 `μ` 下的分布（或律）是推前测度 `μ.map X`。本文件直接
采用 `Measure.map`，不建立同义的 distribution carrier。可测性是假设而不是装饰：Mathlib 为了
让 `Measure.map` 成为全定义函数，会在函数并非 a.e. 可测时返回零测度。

> **Entry**: probability.distribution.pushforward
-/

namespace SandronesLibrary.Probability

open MeasureTheory

/-- 可测随机变量的分布仍是概率测度。
@isnad1 id=isprobab.1h4v.s5.89068aef61a4 from=translated src=- shape=831bdb68 vocab=cd26596f
-/
theorem distribution_isProbabilityMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → E} (hX : Measurable X) :
    IsProbabilityMeasure (μ.map X) :=
  Measure.isProbabilityMeasure_map hX.aemeasurable

/-- 分布的事件公式：`P(X ∈ B)` 等于目标事件 `B` 在推前测度下的质量。
@isnad1 id=eq.2h5v.s6.9c54708df581 from=translated src=- shape=2a346a80 vocab=5e45ed3b
-/
theorem distribution_apply
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) {X : Ω → E} (hX : Measurable X)
    {B : Set E} (hB : MeasurableSet B) :
    μ.map X B = μ (X ⁻¹' B) :=
  Measure.map_apply hX hB

/-- 常随机变量的分布集中在该常值点的原像上。
@isnad1 id=eq.1h5v.s6.8acca605a067 from=translated src=- shape=51f3922f vocab=55d66237
-/
theorem distribution_const_apply
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (c : E) {B : Set E} (hB : MeasurableSet B) :
    μ.map (fun _ : Ω ↦ c) B = μ {_ω | c ∈ B} := by
  rw [Measure.map_apply measurable_const hB]
  rfl

end SandronesLibrary.Probability
