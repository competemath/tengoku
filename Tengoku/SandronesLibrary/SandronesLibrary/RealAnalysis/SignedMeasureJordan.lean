/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/

import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.SignedMeasureDefinition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / SignedMeasureJordan —— Jordan 分解（Folland §3.1 定理 3.1）

本文件当前条目（引理清单）：

* **real-analysis.signed-measure.jordan-decomposition**（Jordan 分解定理：任意有符号测度
  `s` 唯一地写成两个互奇异有限测度之差 `s = s.toJordanDecomposition.posPart -
  s.toJordanDecomposition.negPart`；Jordan 分解结构与有符号测度载体之间的双向伴随与唯一性；
  逐点展开；与课程正／负集 Hahn 分解的桥）✅。

### Mathlib 角色（本文件）

* `MeasureTheory.JordanDecomposition`（字段 `posPart`、`negPart`、`mutuallySingular`，
  两部分带 `IsFiniteMeasure` 实例）：**语义一致的正式承载**（教材中“一对互奇异有限测度”）。
* `MeasureTheory.SignedMeasure.toJordanDecomposition` /
  `MeasureTheory.JordanDecomposition.toSignedMeasure`：**有符号测度与 Jordan 分解之间的
  双向构造**；其互逆性即 Jordan 分解定理。
* `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` /
  `MeasureTheory.JordanDecomposition.toJordanDecomposition_toSignedMeasure` /
  `MeasureTheory.SignedMeasure.toJordanDecomposition_eq` /
  `MeasureTheory.SignedMeasure.toJordanDecompositionEquiv` /
  `MeasureTheory.JordanDecomposition.toSignedMeasure_injective` /
  `MeasureTheory.SignedMeasure.apply_eq_posPart_real_sub_negPart_real`：**唯一性与逐点展开后端**。
* 本库 `IsPositiveSet` / `IsNegativeSet` 与 `exists_hahnDecomposition`：Jordan 分解与课程
  正／负集定义的桥（依赖文件提供）。
-/

noncomputable section

namespace SandronesLibrary

namespace RealAnalysis.SignedMeasure

open MeasureTheory

open scoped MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. Jordan 分解定理（存在性） -/

/-- **Jordan 分解定理**（Folland §3.1 定理 3.1，存在方向）：任意有符号测度 `s` 与其
Jordan 分解 `s.toJordanDecomposition` 所对应的有符号测度相等，即
`s = s.toJordanDecomposition.posPart - s.toJordanDecomposition.negPart`。
这是 `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` 的课程命名。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_decomposition (s : SignedMeasure α) :
    s.toJordanDecomposition.toSignedMeasure = s :=
  s.toSignedMeasure_toJordanDecomposition

/-- **Jordan 分解定理（反向伴随）**：给定 Jordan 分解 `j`，先取对应有符号测度再取
Jordan 分解，回到 `j` 本身。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_decomposition_toSignedMeasure (j : JordanDecomposition α) :
    j.toSignedMeasure.toJordanDecomposition = j :=
  j.toJordanDecomposition_toSignedMeasure

/-- **Jordan 分解唯一性（按有符号测度定位）**：若 `s = j.toSignedMeasure`，则 `s` 的
Jordan 分解就是 `j`。即分解由有符号测度唯一决定。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_decomposition_unique {s : SignedMeasure α} {j : JordanDecomposition α}
    (h : s = j.toSignedMeasure) : s.toJordanDecomposition = j :=
  s.toJordanDecomposition_eq h

/-- **Jordan 分解的特征刻画（iff）**：`s = j.toSignedMeasure` 当且仅当
`s.toJordanDecomposition = j`。这是 Jordan 分解定理的“等价形式”。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_decomposition_iff {s : SignedMeasure α} {j : JordanDecomposition α} :
    s = j.toSignedMeasure ↔ s.toJordanDecomposition = j := by
  constructor
  · exact s.toJordanDecomposition_eq
  · intro h
    rw [← h]
    exact (MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition s).symm

/-! ## 2. 正／负变差之差（逐点展开） -/

/-- **正、负变差之差的展开**：Jordan 分解对应的有符号测度就是两个正测度之差
`j.toSignedMeasure = j.posPart.toSignedMeasure - j.negPart.toSignedMeasure`。
教材记号 `ν = ν⁺ − ν⁻` 的结构性陈述。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_toSignedMeasure_eq_posPart_sub_negPart (j : JordanDecomposition α) :
    j.toSignedMeasure = j.posPart.toSignedMeasure - j.negPart.toSignedMeasure :=
  rfl

/-- **逐点展开**：对可测集 `i`，`s i = s.toJordanDecomposition.posPart.real i -
s.toJordanDecomposition.negPart.real i`。这是 Jordan 分解在实数取值上的逐点形式，
也是教材记号 `ν = ν⁺ − ν⁻` 的直接含义。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_apply_eq_posPart_real_sub_negPart_real (s : SignedMeasure α) {i : Set α}
    (hi : MeasurableSet i) :
    s i = s.toJordanDecomposition.posPart.real i - s.toJordanDecomposition.negPart.real i :=
  s.apply_eq_posPart_real_sub_negPart_real hi

/-- **正、负变差互奇异**：Jordan 分解的两个部分 `j.posPart`、`j.negPart` 互奇异。
这正是 Folland 定理 3.1 中“互奇异”这一条要求。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_posPart_mutuallySingular_negPart (j : JordanDecomposition α) :
    j.posPart ⟂ₘ j.negPart :=
  j.mutuallySingular

/-! ## 3. 唯一性与等价 -/

/-- **Jordan 分解映射的单射性**：`JordanDecomposition.toSignedMeasure` 是单射，即
不同的 Jordan 分解给出不同的有符号测度。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_toSignedMeasure_injective :
    Function.Injective (JordanDecomposition.toSignedMeasure (α := α)) :=
  JordanDecomposition.toSignedMeasure_injective

/-- **Jordan 分解唯一性（成对形式）**：两个 Jordan 分解相等当且仅当它们对应的有符号
测度相等。这是定理 3.1 中“唯一一对”的精确陈述。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_decomposition_unique' {j₁ j₂ : JordanDecomposition α} :
    j₁ = j₂ ↔ j₁.toSignedMeasure = j₂.toSignedMeasure := by
  constructor
  · intro h; rw [h]
  · intro h; exact jordan_toSignedMeasure_injective h

/-- **Jordan 分解的等价**：有符号测度与 Jordan 分解之间存在典范等价
`SignedMeasure α ≃ JordanDecomposition α`。它是存在性与唯一性的打包。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
def jordan_decomposition_equiv : SignedMeasure α ≃ JordanDecomposition α :=
  SignedMeasure.toJordanDecompositionEquiv α

/-! ## 4. 与课程正／负集 Hahn 分解的桥 -/

/-- **Hahn 分解与 Jordan 分解的桥**：任意有符号测度都存在可测正集 `P`，其补集 `Pᶜ` 为
负集。该存在性由依赖文件 `exists_hahnDecomposition` 给出，是把 Jordan 分解的正／负部分
与课程 `IsPositiveSet`／`IsNegativeSet` 量词定义连接起来的入口。
> **Entry**: real-analysis.signed-measure.jordan-decomposition-/
theorem jordan_exists_hahnDecomposition (s : SignedMeasure α) :
    ∃ P : Set α, IsPositiveSet s P ∧ IsNegativeSet s Pᶜ :=
  exists_hahnDecomposition s

end RealAnalysis.SignedMeasure

end SandronesLibrary
