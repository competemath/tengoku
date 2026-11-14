/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.SignedMeasureDefinition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / SignedMeasureVariation —— 正／负／全变差（Folland RA-F1）

本文件当前条目（引理清单）：

* **real-analysis.signed-measure.variation**（有符号测度的正变差 ν⁺、负变差 ν⁻ 与
  全变差 |ν|：Jordan 分解承载、全变差与 sup-over-partitions 变差的桥、有限性、
  逐点不等式、可加性与互奇异）✅。

> **语言说明**：正变差 ν⁺ 与负变差 ν⁻ 由 Jordan 分解
> `SignedMeasure.toJordanDecomposition.posPart / negPart` 正式承载；全变差 |ν| 由
> `SignedMeasure.totalVariation : Measure α` 承载，Mathlib 中它就是 ν⁺ + ν⁻。
> Folland 教材另用 `|ν|(E) = sup Σ |ν(E_j)|`（对可测分划取上确界）定义全变差，
> Mathlib 把这一 sup-over-partitions 版本实现为 `VectorMeasure.variation`，
> 本文件给出二者的具名桥 `totalVariation_eq_variation`。

### Mathlib 角色（本文件）

* `SignedMeasure.toJordanDecomposition.posPart / negPart`：**正式公开承载**（ν⁺ / ν⁻）。
* `SignedMeasure.totalVariation`：**正式公开承载**（|ν| = ν⁺ + ν⁻ 的测度）。
* `VectorMeasure.variation`：**语义一致的教材对照后端**（`|ν|(E) = sup Σ |ν(E_j)|`）。
* `SignedMeasure.norm_le_totalVariation` / `enorm_le_totalVariation` /
  `null_of_totalVariation_zero`：**语义一致的展开／桥后端**。
-/

namespace SandronesLibrary

namespace RealAnalysis.SignedMeasure

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. Jordan 分解与全变差的展开 -/

/-- **全变差 = 正变差 + 负变差**。Mathlib 的 `SignedMeasure.totalVariation` 就是
Jordan 分解 `s.toJordanDecomposition` 的 `posPart + negPart` 之和，故为定义等式。
教材记号的 `|ν| = ν⁺ + ν⁻`。
> **Entry**: real-analysis.signed-measure.variation-/
theorem totalVariation_eq_posPart_add_negPart (s : SignedMeasure α) :
    s.totalVariation = s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart :=
  rfl

/-- **全变差逐点展开**。对任意集 `i`，`|ν|(i) = ν⁺(i) + ν⁻(i)`；测度加法即逐点相加。
教材中由 ν⁺、ν⁻ 的非负性保证这是 `ℝ≥0∞` 中的普通和。
> **Entry**: real-analysis.signed-measure.variation-/
theorem totalVariation_apply (s : SignedMeasure α) (i : Set α) :
    s.totalVariation i = s.toJordanDecomposition.posPart i + s.toJordanDecomposition.negPart i :=
  rfl

/-- **全变差与 sup-over-partitions 变差的桥**。Folland 用可测分划的上确界
`|ν|(E) = sup Σ |ν(E_j)|` 定义全变差；Mathlib 把该版本实现为 `VectorMeasure.variation`，
本桥说明它与 Jordan 分解版本 `SignedMeasure.totalVariation` 相等。
> **Entry**: real-analysis.signed-measure.variation-/
theorem totalVariation_eq_variation (s : SignedMeasure α) : s.totalVariation = s.variation :=
  MeasureTheory.SignedMeasure.totalVariation_eq_variation s

/-! ## 2. 全变差的有限性、零与取负 -/

/-- **全变差是有限测度**。`SignedMeasure α = VectorMeasure α ℝ` 的取值有限，故
`|ν|` 是有限测度：`|ν|(univ) < ∞`，从而 `|ν|` 的任意集取值也是 `ℝ≥0∞` 中的有限值。
这是全变差通往既有正测度主线（如 `Measure.real` 与 `toReal` 运算）的有限性门。
> **Entry**: real-analysis.signed-measure.variation-/
theorem totalVariation_univ_lt_top (s : SignedMeasure α) :
    s.totalVariation Set.univ < ∞ :=
  measure_lt_top s.totalVariation Set.univ

/-- **零有符号测度的全变差为零**：`|0| = 0`。
> **Entry**: real-analysis.signed-measure.variation-/
theorem totalVariation_zero : (0 : SignedMeasure α).totalVariation = 0 :=
  MeasureTheory.SignedMeasure.totalVariation_zero

/-- **取负不改变全变差**：`|-ν| = |ν|`，与教材 `|ν|` 只度量“大小”的直觉一致。
> **Entry**: real-analysis.signed-measure.variation-/
theorem totalVariation_neg (s : SignedMeasure α) : (-s).totalVariation = s.totalVariation :=
  MeasureTheory.SignedMeasure.totalVariation_neg s

/-- **全变差为零推出取值为零**。若 `|ν|(i) = 0`，则 `ν(i) = 0`：这是 `|ν|` 控制 `ν`
的最粗界，也是绝对值不等式的退化情形。
> **Entry**: real-analysis.signed-measure.variation-/
theorem null_of_totalVariation_zero (s : SignedMeasure α) {i : Set α}
    (h : s.totalVariation i = 0) : s i = 0 :=
  MeasureTheory.SignedMeasure.null_of_totalVariation_zero s h

/-! ## 3. 全变差控制原测度（逐点不等式） -/

/-- **全变差控制原测度（实数形式）**。对任意集 `i`，`|ν(i)| ≤ |ν|(i)`；这里把
`ℝ≥0∞` 取值的 `|ν|(i)` 经 `toReal` 转成实数后比较。Mathlib 的
`SignedMeasure.norm_le_totalVariation` 给出 `‖ν(i)‖ ≤ |ν|.real i`，
而 `Measure.real μ i` 正是 `(μ i).toReal`。
> **Entry**: real-analysis.signed-measure.variation-/
theorem abs_apply_le_totalVariation (s : SignedMeasure α) (i : Set α) :
    |s i| ≤ (s.totalVariation i).toReal := by
  simpa only [Real.norm_eq_abs, measureReal_def]
    using MeasureTheory.SignedMeasure.norm_le_totalVariation s i

/-- **全变差控制原测度（`ℝ≥0∞` 形式）**。把实数的绝对值提升到 `enorm` 后，
`‖ν(i)‖ₑ ≤ |ν|(i)` 在 `ℝ≥0∞` 中不需要 `toReal` 转换，是最干净的逐点控制。
> **Entry**: real-analysis.signed-measure.variation-/
theorem enorm_apply_le_totalVariation (s : SignedMeasure α) (i : Set α) :
    ‖s i‖ₑ ≤ s.totalVariation i :=
  MeasureTheory.SignedMeasure.enorm_le_totalVariation s i

/-! ## 4. 全变差作为测度的可加性 -/

/-- **全变差的可加性**。`|ν|` 是测度，故对不交可测集 `A`、`B` 有
`|ν|(A ∪ B) = |ν|(A) + |ν|(B)`。由于 `|ν|` 已由 Mathlib 注册为测度，这里直接调用
正测度的有限可加性。
> **Entry**: real-analysis.signed-measure.variation-/
theorem totalVariation_union (s : SignedMeasure α) {A B : Set α} (h : Disjoint A B)
    (hA : MeasurableSet A) (_hB : MeasurableSet B) :
    s.totalVariation (A ∪ B) = s.totalVariation A + s.totalVariation B := by
  rw [Set.union_comm]
  exact (measure_union h.symm hA).trans (add_comm _ _)

/-! ## 5. ν⁺ 与 ν⁻ 互奇异 -/

/-- **正变差与负变差互奇异**：`ν⁺ ⟂ₘ ν⁻`。Jordan 分解的结构字段直接给出这一事实；
教材中它来自 Hahn 分解：ν⁺ 集中在正集 `P` 上、ν⁻ 集中在 `Pᶜ` 上，而 `P` 与 `Pᶜ` 不交。
> **Entry**: real-analysis.signed-measure.variation-/
theorem posPart_mutuallySingular_negPart (s : SignedMeasure α) :
    s.toJordanDecomposition.posPart ⟂ₘ s.toJordanDecomposition.negPart :=
  s.toJordanDecomposition.mutuallySingular

end RealAnalysis.SignedMeasure

end SandronesLibrary
