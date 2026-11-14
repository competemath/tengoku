/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Model
import Tengoku.Seed.Probability.Kernel.RadonNikodym

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 支配统计模型与联合可测密度

统计模型 `P : Kernel Θ 𝓧` 被参考测度 `ν` 支配，是指每个参数纤维都满足 `P θ ≪ ν`。课程中的
似然或密度应当既能逐参数重建 `P θ`，又作为 `(θ,x)` 的函数联合可测。

本文件不逐参数任意选择 `Measure.rnDeriv` 的版本，而直接使用

`P.rnDeriv (Kernel.const Θ ν) θ x`。

这是 Mathlib 为 kernel 构造的联合可测 Radon--Nikodym 导数。联合可测构造需要
`MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧`；当前重建 API 还要求两个 kernel 有限，故固定
参考测度在本条目中取有限测度。Markov kernel `P` 自动是有限 kernel。

密度取值于 `ℝ≥0∞`，并且只在 `ν`-几乎处处意义下唯一。本文件证明它联合可测、逐参数等于普通
测度 RN 导数、重建模型、在可测集合上积分为模型概率、总积分为一，并且几乎处处不为无穷。

> **Entry**: statistics.model.density
-/

namespace SandronesLibrary.Statistics

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

/-- Kernel RN 密度作为 `(θ,x)` 的函数联合可测。-/
theorem statisticalModel_density_jointlyMeasurable
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) :
    Measurable (fun p : Θ × 𝓧 ↦ P.rnDeriv (Kernel.const Θ ν) p.1 p.2) :=
  Kernel.measurable_rnDeriv P (Kernel.const Θ ν)

/-- 固定参数后，kernel 密度与普通测度 RN 导数 `ν`-几乎处处相等。-/
theorem statisticalModel_density_ae_eq_measure_rnDeriv
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧) [IsFiniteMeasure ν]
    (θ : Θ) :
    (fun x ↦ P.rnDeriv (Kernel.const Θ ν) θ x) =ᵐ[ν] ∂(P θ)/∂ν := by
  simpa only [Kernel.const_apply] using
    (Kernel.rnDeriv_eq_rnDeriv_measure
      (κ := P) (η := Kernel.const Θ ν) (a := θ))

/-- 若参数纤维 `P θ` 被 `ν` 支配，则以联合可测密度加权 `ν` 恰好重建 `P θ`。-/
theorem statisticalModel_withDensity_eq
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧) [IsFiniteMeasure ν]
    (θ : Θ) (hPν : P θ ≪ ν) :
    ν.withDensity (fun x ↦ P.rnDeriv (Kernel.const Θ ν) θ x) = P θ := by
  have h := Kernel.withDensity_rnDeriv_eq
    (κ := P) (η := Kernel.const Θ ν) (a := θ) hPν
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv P (Kernel.const Θ ν))] at h
  simpa only [Kernel.const_apply] using h

/-- 在可测集合 `s` 上积分模型密度，得到参数 `θ` 下事件 `s` 的概率。-/
theorem statisticalModel_setLIntegral_density
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧) [IsFiniteMeasure ν]
    (θ : Θ) (hPν : P θ ≪ ν) {s : Set 𝓧} (hs : MeasurableSet s) :
    ∫⁻ x in s, P.rnDeriv (Kernel.const Θ ν) θ x ∂ν = P θ s := by
  simpa only [Kernel.const_apply] using
    (Kernel.setLIntegral_rnDeriv
      (κ := P) (η := Kernel.const Θ ν) (a := θ) hPν hs)

/-- 概率模型的密度关于支配测度的总积分为一。-/
theorem statisticalModel_lintegral_density_eq_one
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧) [IsFiniteMeasure ν]
    (θ : Θ) (hPν : P θ ≪ ν) :
    ∫⁻ x, P.rnDeriv (Kernel.const Θ ν) θ x ∂ν = 1 := by
  simpa only [Kernel.const_apply, measure_univ] using
    (Kernel.lintegral_rnDeriv
      (κ := P) (η := Kernel.const Θ ν) (a := θ) hPν)

/-- 有限 kernel 的联合密度关于参考测度几乎处处不是无穷。

这一步是日后安全转成实值密度所需的边界之一；本条目不直接把 `ℝ≥0∞` 密度静默 `.toReal`。-/
theorem statisticalModel_density_ne_top_ae
    {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧) [IsFiniteMeasure ν]
    (θ : Θ) :
    ∀ᵐ x ∂ν, P.rnDeriv (Kernel.const Θ ν) θ x ≠ ∞ := by
  simpa only [Kernel.const_apply] using
    (Kernel.rnDeriv_ne_top P (Kernel.const Θ ν) (a := θ))

end SandronesLibrary.Statistics
