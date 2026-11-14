/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.Measure
import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 乘积测度、Tonelli 定理与 Fubini 定理

本模块进入实分析 R4。乘积测度把两个测度空间组合成一个二维空间；它在矩形
`s ×ˢ t` 上的值是 `μ s * ν t`。Tonelli 定理允许非负可测函数在不预设有限积分时
化为迭代积分，Fubini 定理则在可积性假设下处理 Banach 空间值函数并交换积分次序。

类型类 `SFinite` 是 Mathlib 中适合乘积积分的标准 σ-有限推广。通常教材中的
σ-有限测度自动满足这里的假设。
-/

namespace SandronesLibrary.RealAnalysis.ProductMeasure

open Set MeasureTheory
open scoped ENNReal

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β)

/-- **矩形测度公式**：乘积测度在集合直积上的值等于两个边测度之积。

Mathlib 的结论实际上不要求 `s`、`t` 可测；`SFinite ν` 保证所使用的乘积测度具有
教材期望的矩形性质。

> **Entry**: real-analysis.measure.product-measure
@isnad1 id=eq.0h6v.s6.e69b8b4b1863 from=translated src=- shape=45eb8507 vocab=ac1a5ec9
-/
theorem rectangle_measure [SFinite ν] (s : Set α) (t : Set β) :
    μ.prod ν (s ×ˢ t) = μ s * ν t := by
  exact Measure.prod_prod s t

/-- **Tonelli 定理**：非负扩展实数值的几乎处处可测函数，其乘积积分等于先对第二个
变量积分、再对第一个变量积分所得的迭代积分。

> **Entry**: real-analysis.measure.tonelli
@isnad1 id=eq.1h5v.s6.15eb81d1e192 from=translated src=- shape=e027d630 vocab=c032472e
-/
theorem tonelli [SFinite ν] (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  exact lintegral_prod f hf

/-- **Tonelli 定理的反向次序**：若两个测度均 `SFinite`，可以先对第一个变量积分。
@isnad1 id=eq.1h5v.s6.c66bdf981101 from=translated src=- shape=87a9d62e vocab=c032472e
-/
theorem tonelli_swap [SFinite μ] [SFinite ν] (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  exact lintegral_prod_symm f hf

/-- **Fubini 定理**：乘积空间上的 Bochner 可积函数可以先沿第二个变量积分，再沿
第一个变量积分。

> **Entry**: real-analysis.measure.fubini
@isnad1 id=eq.1h6v.s7.4f23fd85b773 from=translated src=- shape=406d3d65 vocab=699d6838
-/
theorem fubini [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SFinite μ] [SFinite ν] (f : α × β → E)
    (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  exact integral_prod f hf

/-- **Fubini 换序公式**：绝对可积性（Lean 中的 `Integrable`）保证两个迭代积分相等。
@isnad1 id=eq.1h6v.s7.1758246629e1 from=translated src=- shape=4b20e682 vocab=044935a8
-/
theorem fubini_swap [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SFinite μ] [SFinite ν] (f : α → β → E)
    (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν := by
  exact integral_integral_swap hf

end SandronesLibrary.RealAnalysis.ProductMeasure
