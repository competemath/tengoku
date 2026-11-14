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

/-- `IsProbabilityMeasure μ` 的教材展开就是总质量等于 `1`。
@isnad1 id=iff.0h2v.s5.7b098d2570ba from=translated src=- shape=489cb65a vocab=3d33cefb
-/
theorem probabilityMeasure_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    IsProbabilityMeasure μ ↔ μ Set.univ = 1 :=
  isProbabilityMeasure_iff

/-- 概率测度的归一化条件：整个样本空间的概率为 `1`。
@isnad1 id=eq.0h2v.s5.5e6cd94a3fb9 from=translated src=- shape=c77a41f4 vocab=3d33cefb
-/
theorem probability_univ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : μ Set.univ = 1 :=
  measure_univ

/-- 空集是事件。
@isnad1 id=measurab.0h1v.s3.1202ea42beeb from=translated src=- shape=b8471119 vocab=cbdeaae0
-/
theorem measurableEvent_empty {Ω : Type*} [MeasurableSpace Ω] :
    MeasurableSet (∅ : Set Ω) :=
  MeasurableSet.empty

/-- 事件的补仍是事件。
@isnad1 id=measurab.1h2v.s4.f290f81db487 from=translated src=- shape=a3b738d9 vocab=a79caad1
-/
theorem MeasurableSet.event_compl {Ω : Type*} [MeasurableSpace Ω]
    {A : Set Ω} (hA : MeasurableSet A) : MeasurableSet Aᶜ :=
  hA.compl

/-- 两个事件的交仍是事件。
@isnad1 id=measurab.2h3v.s4.64fd4ebc8089 from=translated src=- shape=0540dca0 vocab=7435c2b8
-/
theorem MeasurableSet.event_inter {Ω : Type*} [MeasurableSpace Ω]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (A ∩ B) :=
  hA.inter hB

/-- 概率测度下每个集合（尤其每个事件）的概率都不超过 `1`。
@isnad1 id=le.0h3v.s5.601b1a4621dc from=translated src=- shape=41937d10 vocab=8ac8ec90
-/
theorem probability_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Set Ω) : μ A ≤ 1 :=
  prob_le_one

/-- 补事件公式 `P(Aᶜ) = 1 - P(A)`。
@isnad1 id=eq.1h3v.s6.ce879bb824c6 from=translated src=- shape=94cf27c1 vocab=24e705d8
-/
theorem probability_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    μ Aᶜ = 1 - μ A :=
  prob_compl_eq_one_sub hA

/-- 补事件的加法形式；它避免读者把 `ℝ≥0∞` 上的减法误当成普通群减法。
@isnad1 id=eq.1h3v.s6.4ea7bf933df3 from=translated src=- shape=ec8011fc vocab=51514cd6
-/
theorem probability_add_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    μ A + μ Aᶜ = 1 :=
  prob_add_prob_compl hA

end SandronesLibrary.Probability
