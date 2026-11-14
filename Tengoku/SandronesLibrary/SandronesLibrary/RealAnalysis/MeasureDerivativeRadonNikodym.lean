/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / MeasureDerivativeRadonNikodym —— Radon–Nikodym 定理（Folland RA-F2）

本文件当前条目（引理清单）：

* **real-analysis.measure-derivative.radon-nikodym**（测度导数 `μ.rnDeriv ν` 与 Radon–Nikodym
  定理：存在性／唯一性、由密度构造测度、积分换测度、链式法则与互逆边界，以及通往 RA-F1
  `SignedMeasure` 的有符号测度桥）✅。

> **语言说明**：Folland《Real Analysis》2nd ed. §3.2 的 Radon–Nikodym 导数由 Mathlib 的
> `Measure.rnDeriv ν μ`（记号 `μ.rnDeriv ν`）正式承载；教材定理“存在 `ν`-a.e. 唯一的
> `f ≥ 0` 使 `dμ = f dν`”在 `σ`-有限假设下等价于 `ν.withDensity (μ.rnDeriv ν) = μ`。
> 本文件直接复用 Mathlib 的 `Measure.withDensity`、`Measure.withDensityᵥ` 与
> `Measure.rnDeriv`，只补教材形式的存在性、iff 形式、唯一性／零族、乘密度链式与互逆、
> 积分换测度，以及有符号测度一侧的桥。

### Mathlib 角色（本文件）

* `Measure.rnDeriv`：**正式公开承载**（Radon–Nikodym 导数 `dμ/dν`）。
* `Measure.withDensity_rnDeriv_eq` / `Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`：
  **语义一致的定理后端**（RN 存在性与 iff 形式）。
* `Measure.HaveLebesgueDecomposition`：RN 定理所需的存在性假设，由 `σ`-有限自动满足。
* `Measure.setLIntegral_rnDeriv` / `Measure.lintegral_rnDeriv` /
  `Measure.setIntegral_toReal_rnDeriv` / `Measure.integral_toReal_rnDeriv`：
  **积分换测度后端**（lintegral 与 Bochner 两种形式）。
* `Measure.rnDeriv_pos` / `Measure.rnDeriv_self` / `Measure.rnDeriv_withDensity` /
  `Measure.rnDeriv_withDensity_left` / `Measure.rnDeriv_withDensity_right` /
  `Measure.inv_rnDeriv` / `Measure.rnDeriv_mul_rnDeriv`：**语义一致的链式与互逆后端**。
* `Measure.rnDeriv_lt_top` / `Measure.rnDeriv_ne_top`：**`σ`-有限下 a.e. 有限性后端**。
* `SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq`：**连接 RA-F1 有符号测度的桥**。
-/

namespace SandronesLibrary

namespace RealAnalysis.MeasureDerivative

open MeasureTheory
open scoped MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. Radon–Nikodym 存在性与 iff 形式 -/

/-- **Radon–Nikodym 存在性（Folland §3.2）**：若 `μ` 关于 `ν` 绝对连续且 `μ` 对 `ν` 有
Lebesgue 分解（`σ`-有限时自动成立），则存在 `ν`-a.e. 定义的密度 `μ.rnDeriv ν`，使得
`ν.withDensity (μ.rnDeriv ν) = μ`。这是测度相等（而非 a.e. 相等）。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eq.1h3v.s5.df95e277b1b4 from=translated src=- shape=3f9f7b70 vocab=01922475
-/
theorem radonNikodym {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] (h : μ ≪ ν) :
    ν.withDensity (μ.rnDeriv ν) = μ :=
  Measure.withDensity_rnDeriv_eq μ ν h

/-- **Radon–Nikodym 定理（iff 形式）**：在 Lebesgue 分解假设下，`μ ≪ ν` 当且仅当
`ν.withDensity (μ.rnDeriv ν) = μ`。反方向即“由密度构造的测度绝对连续”。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=iff.0h3v.s5.5d12d363b8f2 from=translated src=- shape=ce030857 vocab=01922475
-/
theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq {μ ν : Measure α}
    [μ.HaveLebesgueDecomposition ν] :
    μ ≪ ν ↔ ν.withDensity (μ.rnDeriv ν) = μ :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq

/-! ## 2. 导数的正性与零族 -/

/-- **Radon–Nikodym 导数 `μ`-a.e. 为正**：`μ ≪ ν` 时，`μ.rnDeriv ν` 在 `μ`-几乎处处严格为正。
注意这是关于 `μ` 的 a.e. 陈述：在 `μ`-零集上导数可以任意。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.1h3v.s5.e78e7feb7947 from=translated src=- shape=129d32cb vocab=8c8675a3
-/
theorem rnDeriv_pos {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] (h : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x :=
  Measure.rnDeriv_pos h

/-- **自导数为 1**：`σ`-有限测度 `μ` 关于自身的 Radon–Nikodym 导数 `μ`-a.e. 等于常数 `1`。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.0h2v.s5.8b70fbe3aeef from=translated src=- shape=5595fc8e vocab=02329a30
-/
theorem rnDeriv_self (μ : Measure α) [SigmaFinite μ] :
    μ.rnDeriv μ =ᵐ[μ] fun _ => 1 :=
  Measure.rnDeriv_self μ

/-! ## 3. 由密度构造测度的导数 -/

/-- **密度测度的导数**：对可测 `f`，`ν.withDensity f` 关于 `ν` 的导数 `ν`-a.e. 等于 `f`。
这是“由密度构造 → 导数还原密度”的方向，与存在性定理互为逆。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.1h3v.s5.bc8ee1827def from=translated src=- shape=a2404463 vocab=c02e1283
-/
theorem rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  Measure.rnDeriv_withDensity ν hf

/-- **链式（乘密度，左侧）**：`(μ.withDensity f).rnDeriv ν =ᵐ[ν] f * μ.rnDeriv ν`，假设
`f` 关于 `ν` 可测且 `μ`-a.e. 有限。这是教材链式法则 `d(μ.withDensity f)/dν = f · dμ/dν`
的 `ℝ≥0∞` 形式。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.2h4v.s6.8355066bd79c from=translated src=- shape=0d3a968d vocab=5938a741
-/
theorem rnDeriv_withDensity_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hfin : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x => f x * μ.rnDeriv ν x :=
  Measure.rnDeriv_withDensity_left hf hfin

/-- **链式（右端乘密度）**：`μ.rnDeriv (ν.withDensity f) =ᵐ[ν] f⁻¹ * μ.rnDeriv ν`，假设
`f` 关于 `ν` 可测、`ν`-a.e. 非零且非 `⊤`。这是把右端换成一个密度测度时导数的“除法”形式。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.3h4v.s7.3cf26645930e from=translated src=- shape=0ccb54f0 vocab=cdb380a9
-/
theorem rnDeriv_withDensity_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hne : ∀ᵐ x ∂ν, f x ≠ 0)
    (hfin : ∀ᵐ x ∂ν, f x ≠ ⊤) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x => (f x)⁻¹ * μ.rnDeriv ν x :=
  Measure.rnDeriv_withDensity_right μ ν hf hne hfin

/-! ## 4. 互逆与链式法则 -/

/-- **互逆边界**：`μ ≪ ν` 且两者都 `σ`-有限时，`(μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ`。
即两个互逆的 Radon–Nikodym 导数在 `μ`-a.e. 意义下互为倒数。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.1h3v.s6.436f286dfe5f from=translated src=- shape=40da7d74 vocab=071a189f
-/
theorem inv_rnDeriv {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ :=
  Measure.inv_rnDeriv h

/-- **链式法则**：`μ ≪ ν`、三者都 `σ`-有限时，`μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ`。
这是教材 `dμ/dκ = (dμ/dν)(dν/dκ)` 的 a.e. 形式，是概率论中换测度公式的核心。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.1h4v.s6.3c566675dac6 from=translated src=- shape=ec4fad8d vocab=bda232c4
-/
theorem rnDeriv_mul_rnDeriv {μ ν κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (h : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ :=
  Measure.rnDeriv_mul_rnDeriv h

/-! ## 5. 积分换测度公式 -/

/-- **积分换测度（lintegral，集合形式）**：`μ ≪ ν` 时，`∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s`。
把关于 `μ` 的积分换成关于 `ν` 的加权积分，权重为 Radon–Nikodym 导数。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eq.1h4v.s6.6ba16b46a1f0 from=translated src=- shape=af8858e4 vocab=619e11aa
-/
theorem setLIntegral_rnDeriv {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] [SFinite ν]
    (h : μ ≪ ν) (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s :=
  Measure.setLIntegral_rnDeriv h s

/-- **积分换测度（lintegral，全集形式）**：`∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ`。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eq.1h3v.s5.590ab8ab0cfb from=translated src=- shape=08fbc72f vocab=be686d3f
-/
theorem lintegral_rnDeriv {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] (h : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ :=
  Measure.lintegral_rnDeriv h

/-- **积分换测度（Bochner/toReal，集合形式）**：在 `σ`-有限 `μ`、`ν` 下，
`∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s`。这里必须用 `toReal` 把 `ℝ≥0∞` 导数
映到 `ℝ`，等式才落在 Bochner 积分一侧；`μ.real s` 是 `μ s` 的 `ℝ` 值版本。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eq.1h4v.s6.316c1a64bfa6 from=translated src=- shape=9cf13884 vocab=1bf3208a
-/
theorem setIntegral_toReal_rnDeriv {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (h : μ ≪ ν) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s :=
  Measure.setIntegral_toReal_rnDeriv h s

/-- **积分换测度（Bochner/toReal，全集形式）**：`∫ x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ`。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eq.1h3v.s5.f45cb69a68c5 from=translated src=- shape=15850c93 vocab=47f027a8
-/
theorem integral_toReal_rnDeriv {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (h : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ :=
  Measure.integral_toReal_rnDeriv h

/-! ## 6. `σ`-有限下导数的 a.e. 有限性 -/

/-- **导数 `ν`-a.e. 小于 `⊤`**：`μ` 为 `σ`-有限时，`μ.rnDeriv ν` 关于 `ν` 几乎处处有限。
这是把 `ℝ≥0∞` 导数送入 `toReal` 做 Bochner 积分的类型前提。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.0h3v.s5.0194389c9b4f from=translated src=- shape=de4d1cee vocab=323bcff1
-/
theorem rnDeriv_lt_top (μ ν : Measure α) [SigmaFinite μ] :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x < ⊤ :=
  Measure.rnDeriv_lt_top μ ν

/-- **导数 `ν`-a.e. 不等于 `⊤`**：`rnDeriv_lt_top` 的 `≠ ⊤` 表述，常直接用于 a.e. 重写。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=eventual.0h3v.s5.7a55c3021b27 from=translated src=- shape=de4d1cee vocab=6b3ec7f1
-/
theorem rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ⊤ :=
  Measure.rnDeriv_ne_top μ ν

/-! ## 7. 有符号测度的 Radon–Nikodym 桥（连接 RA-F1） -/

/-- **有符号测度 Radon–Nikodym 桥**：对 `σ`-有限正测度 `μ`，一个实值有符号测度 `s` 关于
`μ` 的向量测度意义绝对连续（`s ≪ᵥ μ.toENNRealVectorMeasure`）当且仅当
`μ.withDensityᵥ (s.rnDeriv μ) = s`。这把 RA-F2 的 Radon–Nikodym 导数接到 RA-F1 的
`SignedMeasure`／向量测度框架；本文件只给桥，不展开其证明。
> **Entry**: real-analysis.measure-derivative.radon-nikodym
@isnad1 id=iff.0h3v.s6.226a8e65bf5c from=translated src=- shape=abcdf1b6 vocab=ae88849d
-/
theorem signedMeasure_absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (s : SignedMeasure α)
    (μ : Measure α) [SigmaFinite μ] :
    s ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  s.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq μ

end RealAnalysis.MeasureDerivative

end SandronesLibrary
