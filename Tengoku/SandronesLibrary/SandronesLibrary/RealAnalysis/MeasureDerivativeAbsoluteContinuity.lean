/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / MeasureDerivativeAbsoluteContinuity —— 测度的绝对连续（Folland RA-F2）

本文件当前条目（引理清单）：

* **real-analysis.measure-derivative.absolute-continuity**（测度的绝对连续 `μ ≪ ν`：教材定义
  “`ν(E)=0 ⟹ μ(E)=0`”的显式量词展开、与几乎处处滤子的等价刻画、代数性质，以及“由密度构造的
  测度绝对连续”这一后续 Radon–Nikodym 反方向所依赖的入口）✅。

> **语言说明**：实分析阶段（§Phase5）mathlib 的 `MeasureTheory.Measure.AbsolutelyContinuous`
> 与 Folland 第 3 章 §3.2 的定义逐字一致（`ν s = 0 → μ s = 0`），故本库直接复用该谓词与记号
> `μ ≪ ν` 作为**正式公开承载**，不另造同构 `def`；本文件只补教材量词展开、a.e. 滤子桥与
> 实数测度论需要的代数性质。

### Mathlib 角色（本文件）

* `MeasureTheory.Measure.AbsolutelyContinuous` + 记号 `≪`：**正式公开承载**（课程定义直接采用）。
* `Measure.AbsolutelyContinuous.mk/refl/rfl/zero/trans/add/add_left/add_right/smul/smul_right/
  of_le/of_eq/ae_le/ae_eq/null_mono/pos_mono`：语义一致的**性质后端**，本文件把它们提升为
  教材命题名（如“更大测度绝对连续”）。
* `Measure.ae_le_iff_absolutelyContinuous`：绝对连续 ↔ a.e. 滤子单调性的**桥**。
* `MeasureTheory.withDensity_absolutelyContinuous`：密度测度 `μ.withDensity f` 的绝对连续方向，
  是 RA-F2 Radon–Nikodym“由密度构造”一侧的入口。
-/

namespace SandronesLibrary

namespace RealAnalysis.MeasureDerivative

open MeasureTheory
open scoped MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ ν ν' ν₁ ν₂ : Measure α}

/-! ## 1. 定义与量词展开 -/

/-- **绝对连续（Folland §3.2 定义）**：`μ` 关于 `ν` 绝对连续，当且仅当任意满足 `ν s = 0` 的集合
`s` 也满足 `μ s = 0`。本定理给出教材量词的显式展开；Mathlib 的定义本身即为该量词，故为 `Iff.rfl`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_iff (μ ν : Measure α) :
    μ ≪ ν ↔ ∀ s : Set α, ν s = 0 → μ s = 0 :=
  Iff.rfl

/-- **绝对连续（可测集形式）**：由“每个可测零测集的 `μ` 测度为零”即可推出绝对连续。
教材通常只对可测集陈述该条件；Mathlib 的 `Measure` 在非可测集上取外测度，故两种量词等价。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_iff_measurable (μ ν : Measure α) :
    μ ≪ ν ↔ ∀ s : Set α, MeasurableSet s → ν s = 0 → μ s = 0 := by
  constructor
  · intro h s _ hs; exact h hs
  · exact fun h => Measure.AbsolutelyContinuous.mk h

/-! ## 2. 基本代数性质 -/

/-- **更大的测度绝对连续**：若 `μ ≤ ν`（逐集比较），则 `μ ≪ ν`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_of_le (h : μ ≤ ν) : μ ≪ ν :=
  Measure.absolutelyContinuous_of_le h

/-- **相等的测度互相绝对连续**：`μ = ν ⟹ μ ≪ ν`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_of_eq (h : μ = ν) : μ ≪ ν :=
  Measure.absolutelyContinuous_of_eq h

/-- **自反性**：`μ ≪ μ`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_refl (μ : Measure α) : μ ≪ μ :=
  Measure.AbsolutelyContinuous.refl μ

/-- **零测度绝对连续**：`0 ≪ μ`。教材中零测度关于任何测度绝对连续。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_zero (μ : Measure α) : (0 : Measure α) ≪ μ :=
  Measure.AbsolutelyContinuous.zero μ

/-- **传递性**：`μ₁ ≪ μ₂`、`μ₂ ≪ μ₃` 蕴含 `μ₁ ≪ μ₃`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_trans (h₁ : μ ≪ ν) (h₂ : ν ≪ ν') : μ ≪ ν' :=
  h₁.trans h₂

/-- **加法（同时换两边）**：`μ₁ ≪ ν₁`、`μ₂ ≪ ν₂` 蕴含 `μ₁ + μ₂ ≪ ν₁ + ν₂`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_add (h₁ : μ ≪ ν) (h₂ : ν₁ ≪ ν₂) : μ + ν₁ ≪ ν + ν₂ :=
  h₁.add h₂

/-- **加法（固定右端）**：`μ₁ ≪ ν`、`μ₂ ≪ ν` 蕴含 `μ₁ + μ₂ ≪ ν`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_add_left (h₁ : μ ≪ ν) (h₂ : ν₁ ≪ ν) : μ + ν₁ ≪ ν :=
  Measure.AbsolutelyContinuous.add_left h₁ h₂

/-- **右端添加测度**：`μ ≪ ν ⟹ μ ≪ ν + ν'`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_add_right (h : μ ≪ ν) (ν' : Measure α) : μ ≪ ν + ν' :=
  h.add_right ν'

/-- **对零测度绝对连续刻画零测度**：`μ ≪ 0 ↔ μ = 0`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_zero_iff : μ ≪ 0 ↔ μ = 0 :=
  Measure.absolutelyContinuous_zero_iff

/-! ## 3. 与几乎处处滤子的桥、零集单调性 -/

/-- **a.e. 滤子桥（Folland §3.2）**：`μ ≪ ν` 当且仅当几乎处处滤子满足 `ae μ ≤ ae ν`。
这把测度层的绝对连续翻译成“`ν`-a.e. 成立蕴含 `μ`-a.e. 成立”的滤子语义。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_iff_ae_le : μ ≪ ν ↔ ae μ ≤ ae ν :=
  Measure.ae_le_iff_absolutelyContinuous.symm

/-- **a.e. 等式的传输**：若 `μ ≪ ν` 且 `f =ᵐ[ν] g`，则 `f =ᵐ[μ] g`。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_ae_eq (h : μ ≪ ν) {β : Type*} {f g : α → β} (h' : f =ᵐ[ν] g) :
    f =ᵐ[μ] g :=
  h.ae_eq h'

/-- **零集单调性**：`μ ≪ ν` 时，`ν`-零集也是 `μ`-零集（教材定义的逐点形式）。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_null_mono (h : μ ≪ ν) {t : Set α} (ht : ν t = 0) : μ t = 0 :=
  h.null_mono ht

/-- **正测度集单调性**：`μ ≪ ν` 时，`μ t > 0` 蕴含 `ν t > 0`；这是零集单调性的对偶形式。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem absolutelyContinuous_pos_mono (h : μ ≪ ν) {t : Set α} (ht : 0 < μ t) : 0 < ν t :=
  h.pos_mono ht

/-! ## 4. 由密度构造的测度绝对连续（Radon–Nikodym 反方向入口） -/

/-- **密度测度绝对连续**：对任意 `f : α → ℝ≥0∞`，`μ.withDensity f ≪ μ`。这是 RA-F2 中
Radon–Nikodym 定理“`ν.withDensity (μ.rnDeriv ν) = μ`”一侧之所以可能的入口（反方向 `⟸`）。
> **Entry**: real-analysis.measure-derivative.absolute-continuity-/
theorem withDensity_absolutelyContinuous (μ : Measure α) (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ :=
  MeasureTheory.withDensity_absolutelyContinuous μ f

end RealAnalysis.MeasureDerivative

end SandronesLibrary
