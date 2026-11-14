/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Probability.Kernel.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 统计模型

统计模型是在样本空间 `𝓧` 上、由参数 `θ : Θ` 编号的一族概率分布 `P θ`。为了能够对参数积分、
定义 Bayes 风险或选取联合可测的似然，这族测度还应随参数可测。

这两项要求正好由 Mathlib 的成熟接口共同承载：

* `P : ProbabilityTheory.Kernel Θ 𝓧` 表示可测的测度族；
* `[ProbabilityTheory.IsMarkovKernel P]` 表示每个纤维 `P θ` 都是概率测度。

因此本文件不另建 `StatisticalModel` 结构。另建平行 carrier 会迫使后续风险、估计量和似然理论
反复转换回 kernel，并可能静默丢失参数可测性。

> **Entry**: statistics.model.definition
-/

namespace SandronesLibrary.Statistics

open MeasureTheory
open ProbabilityTheory

/-- 统计模型作为 kernel 随参数可测。这里的值域是带正式可测结构的测度空间。
@isnad1 id=measurab.0h3v.s5.a15b2759a972 from=translated src=- shape=c3c12631 vocab=1e4034ac
-/
theorem statisticalModel_measurable
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (P : Kernel Θ 𝓧) :
    Measurable P :=
  P.measurable

/-- 对每个可测事件 `s`，模型赋予它的概率 `θ ↦ P θ s` 是参数的可测函数。
@isnad1 id=measurab.1h4v.s6.39516fad003f from=translated src=- shape=bd4835cb vocab=72ff7bf1
-/
theorem statisticalModel_eventProbability_measurable
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (P : Kernel Θ 𝓧) {s : Set 𝓧} (hs : MeasurableSet s) :
    Measurable (fun θ ↦ P θ s) :=
  P.measurable_coe hs

/-- Markov kernel 的每个参数纤维都是样本空间上的概率测度。
@isnad1 id=isprobab.0h4v.s5.1fa453e4204d from=translated src=- shape=9cf69e90 vocab=aad74603
-/
theorem statisticalModel_fiber_isProbabilityMeasure
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (θ : Θ) :
    IsProbabilityMeasure (P θ) :=
  inferInstance

/-- 统计模型在每个参数处都把整个样本空间赋予概率一。
@isnad1 id=eq.0h4v.s6.d53f37f91b0d from=translated src=- shape=e4a7632f vocab=f8be4ade
-/
theorem statisticalModel_measure_univ
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (θ : Θ) :
    P θ Set.univ = 1 :=
  measure_univ

/-- 固定一个概率测度、忽略参数所得的常 kernel 是统计模型。
@isnad1 id=ismarkov.0h3v.s4.a9caec391335 from=translated src=- shape=f544231d vocab=471525a6
-/
theorem constantProbabilityMeasure_isStatisticalModel
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] :
    IsMarkovKernel (Kernel.const Θ μ) :=
  inferInstance

/-- 可测的确定性观测 `f θ` 通过 Dirac 测度给出统计模型。

这说明传统的确定性参数族无需另设 carrier：它通过 `Kernel.deterministic` 进入与随机模型相同的
接口。要求 `f` 可测正是 kernel 对参数依赖施加的真实条件。
@isnad1 id=ismarkov.1h3v.s5.c03fbe687019 from=translated src=- shape=8a284326 vocab=c75b26d4
-/
theorem deterministicObservation_isStatisticalModel
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    (f : Θ → 𝓧) (hf : Measurable f) :
    IsMarkovKernel (Kernel.deterministic f hf) :=
  inferInstance

end SandronesLibrary.Statistics
