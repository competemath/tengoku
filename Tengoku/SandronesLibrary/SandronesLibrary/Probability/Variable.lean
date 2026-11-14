/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Space

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 随机变量

从样本空间 `Ω` 到状态空间 `E` 的随机变量，就是可测函数 `X : Ω → E`。正式承载直接采用
Mathlib 的 `Measurable X`：它准确表达每个可测集合的原像仍是事件。随机变量不是额外携带数据
的结构；同一个函数可以相对于不同的可测空间结构讨论可测性。

> **Entry**: probability.variable.definition
-/

namespace SandronesLibrary.Probability

open MeasureTheory

/-- 随机变量的教材展开：目标中的每个可测集合，其原像都是样本空间中的事件。
@isnad1 id=iff.0h3v.s5.4d887ea4b107 from=translated src=- shape=90a889fa vocab=2dbba744
-/
theorem randomVariable_iff_preimage
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (X : Ω → E) :
    Measurable X ↔ ∀ A : Set E, MeasurableSet A → MeasurableSet (X ⁻¹' A) :=
  Iff.rfl

/-- 常随机变量可测。
@isnad1 id=measurab.0h3v.s4.5a3c78e98f8c from=translated src=- shape=e5f2b370 vocab=a9a5f847
-/
theorem randomVariable_const
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (c : E) :
    Measurable (fun _ : Ω ↦ c) :=
  measurable_const

/-- 可测变换作用在随机变量上仍得到随机变量。
@isnad1 id=measurab.2h5v.s5.1dd081381142 from=translated src=- shape=d23617fe vocab=c36ae17f
-/
theorem randomVariable_comp
    {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    {X : Ω → E} {g : E → F} (hg : Measurable g) (hX : Measurable X) :
    Measurable (g ∘ X) :=
  hg.comp hX

end SandronesLibrary.Probability
