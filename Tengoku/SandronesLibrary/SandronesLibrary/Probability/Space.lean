/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.MeasureTheory.Measure.Typeclasses.Probability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 概率空间与事件

概率空间由可测空间、其上的测度 `μ` 以及归一化条件 `μ univ = 1` 组成。本文件直接采用
Mathlib 的 `IsProbabilityMeasure μ` 作为正式承载，不复制一个平行的概率空间结构。

事件就是可测集合，即 `MeasurableSet A`。因此事件的补、有限交和有限并仍为事件；概率测度
在全集上取值 `1`，每个事件的概率不超过 `1`，补事件概率为 `1 - μ A`。

> **Entry**: probability.space.definition
-/

namespace SandronesLibrary.Probability

open Set MeasureTheory
open scoped ENNReal

/-- `IsProbabilityMeasure μ` 的教材展开就是总质量等于 `1`。-/
theorem probabilityMeasure_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    IsProbabilityMeasure μ ↔ μ Set.univ = 1 :=
  isProbabilityMeasure_iff

/-- 概率测度的归一化条件：整个样本空间的概率为 `1`。-/
theorem probability_univ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : μ Set.univ = 1 :=
  measure_univ

/-- 空集是事件。-/
theorem measurableEvent_empty {Ω : Type*} [MeasurableSpace Ω] :
    MeasurableSet (∅ : Set Ω) :=
  MeasurableSet.empty

/-- 事件的补仍是事件。-/
theorem MeasurableSet.event_compl {Ω : Type*} [MeasurableSpace Ω]
    {A : Set Ω} (hA : MeasurableSet A) : MeasurableSet Aᶜ :=
  hA.compl

/-- 两个事件的交仍是事件。-/
theorem MeasurableSet.event_inter {Ω : Type*} [MeasurableSpace Ω]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (A ∩ B) :=
  hA.inter hB

/-- 概率测度下每个集合（尤其每个事件）的概率都不超过 `1`。-/
theorem probability_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Set Ω) : μ A ≤ 1 :=
  prob_le_one

/-- 补事件公式 `P(Aᶜ) = 1 - P(A)`。-/
theorem probability_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    μ Aᶜ = 1 - μ A :=
  prob_compl_eq_one_sub hA

/-- 补事件的加法形式；它避免读者把 `ℝ≥0∞` 上的减法误当成普通群减法。-/
theorem probability_add_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    μ A + μ Aᶜ = 1 :=
  prob_add_prob_compl hA

end SandronesLibrary.Probability
