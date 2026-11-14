/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / MeasureDerivativeLebesgueDecomposition —— Lebesgue 分解（Folland RA-F2）

本文件当前条目（引理清单）：

* **real-analysis.measure-derivative.lebesgue-decomposition**（Lebesgue 分解定理：任意 σ-有限
  测度 `ν` 关于任意 `SFinite` 测度 `μ` 都有分解 `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`，
  其中奇异部分 `μ.singularPart ν` 与 `ν` 互相奇异、绝对连续部分由密度给出；并给出两部分的
  唯一性——奇异部分作为测度唯一，密度作为 `ν`-a.e. 函数唯一）✅。

> **语言说明**：实分析阶段（§Phase5）mathlib 的 `MeasureTheory.Measure.HaveLebesgueDecomposition`
> 及其附属对象 `singularPart`、`rnDeriv` 与 Folland 第 3 章 §3.2 的 Lebesgue 分解逐字一致
> （把 `μ` 分成关于 `ν` 绝对连续的部分与 `ν`-奇异的部分）。本库直接复用这些结构与记号作为
> **正式公开承载**，不另造同构 `def`；本文件把它们整理成教材命题名并给出存在性、分解等式、
> 唯一性与奇异部分的零点刻画。

### Mathlib 角色（本文件）

* `Measure.HaveLebesgueDecomposition`、`Measure.singularPart`、`Measure.rnDeriv`：
  **正式公开承载**（课程定义直接采用）。
* `Measure.haveLebesgueDecomposition_of_sigmaFinite`、`Measure.haveLebesgueDecomposition_add`、
  `Measure.mutuallySingular_singularPart`、`Measure.singularPart_le`、
  `Measure.withDensity_rnDeriv_le`、`Measure.measurable_rnDeriv`：
  语义一致的**性质后端**，本文件把它们提升为教材命题名。
* `Measure.eq_singularPart`、`Measure.eq_rnDeriv`：分解唯一性的后端（教材 §3.2 唯一性论断）。
* `Measure.MutuallySingular.haveLebesgueDecomposition`：互相奇异 ⇒ 可取退化分解的**桥**。
* `Measure.singularPart_eq_zero`、`Measure.singularPart_eq_zero_of_ac`、
  `Measure.singularPart_eq_self`：奇异部分为零／等于全测度的刻画后端。
-/

namespace SandronesLibrary

namespace RealAnalysis.MeasureDerivative

open MeasureTheory
open scoped MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. 分解的存在性 -/

/-- **Lebesgue 分解的存在性（σ-有限情形，Folland §3.2）**：设 `μ` 是 `SFinite`（可数可加意义下
σ-有限的推广）测度、`ν` 是 σ-有限测度，则 `μ` 关于 `ν` 有 Lebesgue 分解，即存在与 `ν` 互相奇异的
`μ.singularPart ν` 和绝对连续部分 `ν.withDensity (μ.rnDeriv ν)` 使 `μ` 为其和。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem haveLebesgueDecomposition_of_sigmaFinite (μ ν : Measure α) [SFinite μ] [SigmaFinite ν] :
    μ.HaveLebesgueDecomposition ν :=
  Measure.haveLebesgueDecomposition_of_sigmaFinite μ ν

/-- **Lebesgue 分解等式（Folland §3.2 主等式）**：`μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`。
右端两项分别是对 `ν` 奇异的部分与关于 `ν` 绝对连续的部分。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem haveLebesgueDecomposition_add (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  Measure.haveLebesgueDecomposition_add μ ν

/-! ## 2. 两部分的基本刻画 -/

/-- **奇异部分与 `ν` 互相奇异**：`μ.singularPart ν ⟂ₘ ν`；这正是教材中“分解的奇异部分”。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν :=
  Measure.mutuallySingular_singularPart μ ν

/-- **奇异部分被 `μ` 控制**：`μ.singularPart ν ≤ μ`，即分解的两项都逐集不超过原测度。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem singularPart_le (μ ν : Measure α) : μ.singularPart ν ≤ μ :=
  Measure.singularPart_le μ ν

/-- **密度部分被 `μ` 控制**：`ν.withDensity (μ.rnDeriv ν) ≤ μ`。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) ≤ μ :=
  Measure.withDensity_rnDeriv_le μ ν

/-- **Lebesgue 分解的合取刻画**：给定 `μ.HaveLebesgueDecomposition ν`，Radon–Nikodym 导数可测、
奇异部分与 `ν` 互相奇异、且分解等式成立；这是教材对分解三要素（可测密度、奇异、等式）的一步陈述。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem haveLebesgueDecomposition_spec (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    Measurable (μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧
      μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  ⟨Measure.measurable_rnDeriv μ ν, Measure.mutuallySingular_singularPart μ ν,
    Measure.haveLebesgueDecomposition_add μ ν⟩

/-! ## 3. 唯一性 -/

/-- **奇异部分唯一性（Folland §3.2）**：设 `s ⟂ₘ ν`、`f` 可测且 `μ = s + ν.withDensity f`，
则 `s = μ.singularPart ν`；即分解中与 `ν` 奇异的测度部分是唯一的。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem singularPart_unique {μ ν s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f)
    (hs : s ⟂ₘ ν) (hμ : μ = s + ν.withDensity f) : s = μ.singularPart ν :=
  Measure.eq_singularPart hf hs hμ

/-- **密度唯一性（a.e.，Folland §3.2）**：在 σ-有限 `ν` 下，设 `s ⟂ₘ ν`、`f` 可测且
`μ = s + ν.withDensity f`，则 `f =ᵐ[ν] μ.rnDeriv ν`；即 Radon–Nikodym 导数在 `ν`-a.e. 意义下唯一。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem rnDeriv_unique {μ ν : Measure α} [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞}
    (hf : Measurable f) (hs : s ⟂ₘ ν) (hμ : μ = s + ν.withDensity f) :
    f =ᵐ[ν] μ.rnDeriv ν :=
  Measure.eq_rnDeriv hf hs hμ

/-! ## 4. 退化情形、零点刻画与可测性 -/

/-- **互相奇异测度的分解**：若 `μ ⟂ₘ ν`，则 `μ` 关于 `ν` 有 Lebesgue 分解（取奇异部分为 `μ`、
密度部分为 `0`）；教材中奇异测度是分解的极端情形。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem mutuallySingular_haveLebesgueDecomposition {μ ν : Measure α} (h : μ ⟂ₘ ν) :
    μ.HaveLebesgueDecomposition ν :=
  h.haveLebesgueDecomposition

/-- **奇异部分为零的刻画**：`μ.singularPart ν = 0 ↔ μ ≪ ν`；即分解的奇异部分消失当且仅当
`μ` 关于 `ν` 绝对连续。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem singularPart_eq_zero_iff (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.singularPart ν = 0 ↔ μ ≪ ν :=
  Measure.singularPart_eq_zero μ ν

/-- **绝对连续 ⇒ 奇异部分为零**：若 `μ ≪ ν`，则 `μ.singularPart ν = 0`。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem singularPart_eq_zero_of_absolutelyContinuous {μ ν : Measure α} (h : μ ≪ ν) :
    μ.singularPart ν = 0 :=
  Measure.singularPart_eq_zero_of_ac h

/-- **奇异部分自反为零**：`μ.singularPart μ = 0`（`μ` 关于自身绝对连续）。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem singularPart_self (μ : Measure α) : μ.singularPart μ = 0 :=
  Measure.singularPart_self μ

/-- **奇异部分等于全测度的刻画**：`μ.singularPart ν = μ ↔ μ ⟂ₘ ν`。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem singularPart_eq_self_iff {μ ν : Measure α} : μ.singularPart ν = μ ↔ μ ⟂ₘ ν :=
  Measure.singularPart_eq_self

/-- **Radon–Nikodym 导数的可测性**：`μ.rnDeriv ν` 总是可测函数。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem measurable_rnDeriv (μ ν : Measure α) : Measurable (μ.rnDeriv ν) :=
  Measure.measurable_rnDeriv μ ν

/-- **密度测度的分解**：对可测 `f`，`μ.withDensity f` 关于 `μ` 有 Lebesgue 分解
（密度部分即 `f`，奇异部分为零）。
> **Entry**: real-analysis.measure-derivative.lebesgue-decomposition-/
theorem haveLebesgueDecomposition_withDensity (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) : (μ.withDensity f).HaveLebesgueDecomposition μ :=
  Measure.haveLebesgueDecomposition_withDensity μ hf

end RealAnalysis.MeasureDerivative

end SandronesLibrary
