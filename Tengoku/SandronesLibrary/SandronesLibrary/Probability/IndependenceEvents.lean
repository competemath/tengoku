/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Space
import Tengoku.Seed.Probability.Independence.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 事件与 σ-代数的独立性

两个事件的独立性正式使用 Mathlib `ProbabilityTheory.IndepSet A B μ`；两个 σ-代数的独立性
使用 `ProbabilityTheory.Indep m₁ m₂ μ`。ROADMAP 中早期写的 `IndepEvents` 在 Mathlib 4.33
已不是公开名称，本条目按当前正式接口解释，不建立替代谓词。

> **Entry**: probability.independence.events
-/

namespace SandronesLibrary.Probability

open MeasureTheory ProbabilityTheory

/-- 可测事件独立，当且仅当交事件概率等于概率乘积。
@isnad1 id=iff.2h4v.s6.6a0416386afd from=translated src=- shape=63a78092 vocab=381b9afd
-/
theorem independentEvents_iff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B μ ↔ μ (A ∩ B) = μ A * μ B :=
  indepSet_iff_measure_inter_eq_mul hA hB μ

/-- 可测事件的独立性具有对称性。
@isnad1 id=indepset.3h4v.s5.655d44de7876 from=translated src=- shape=a73b3650 vocab=9b15bd19
-/
theorem independentEvents_symm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : IndepSet A B μ) : IndepSet B A μ := by
  rw [independentEvents_iff hB hA]
  rw [Set.inter_comm, mul_comm]
  exact (independentEvents_iff hA hB).1 hAB

end SandronesLibrary.Probability
