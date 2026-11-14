/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.Lp
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Tengoku.Seed.MeasureTheory.Integral.MeanInequalities
import Tengoku.Seed.MeasureTheory.Function.L1Space.Integrable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Lᵖ` 函数的 Hölder、Chebyshev 与 Minkowski 不等式

本模块集中收录 `Lᵖ` 理论中三个最常用的估计。

* Hölder 不等式控制共轭指数函数的乘积，并给出 `Lᵖ · Lᑫ ⊆ L¹`；
* Chebyshev–Markov 不等式把函数的 `Lᵖ` 大小转化为超水平集的测度上界；它是从
  `Lᵖ` 控制推出依测度控制、尾部估计及概率论 Markov 不等式的基本工具。
* Minkowski 不等式说明 `p ≥ 1` 时 `Lᵖ` 半范数满足三角不等式。这里既保留适用于
  一般赋范加法群值函数的 `eLpNorm` 形式，也给出非负扩展实值函数的显式积分形式。

`eLpNorm` 取值于 `ℝ≥0∞`，所以这些陈述在尚未假设函数属于 `Lᵖ` 时仍然有意义。
特别地，Minkowski 的抽象形式也覆盖 `p = ∞`；显式幂积分形式则使用实指数 `p`。
-/

namespace SandronesLibrary.RealAnalysis.Lp

open MeasureTheory
open scoped ENNReal

variable {α E 𝕜 : Type*} [MeasurableSpace α] (μ : Measure α)

/-- **Hölder 不等式（范数形式）**：共轭指数下，范数乘积的积分不超过两个幂积分
所定义的 `Lᵖ` 与 `Lᑫ` 半范数之积。

> **Entry**: real-analysis.lp.holder
@isnad1 id=le.3h7v.s8.ceb7e213d2db from=translated src=- shape=b208ad0e vocab=8ada777a
-/
theorem holder_norm {E : Type*} [NormedAddCommGroup E]
    {f g : α → E} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) * (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) := by
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg

/-- **Hölder 不等式（非负实函数形式）**：几乎处处非负时可去掉绝对值。
@isnad1 id=le.5h6v.s8.0ab6bc4febf3 from=translated src=- shape=64a1a39a vocab=67ff2766
-/
theorem holder_nonneg {f g : α → ℝ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ x, f x * g x ∂μ ≤
      (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, g x ^ q ∂μ) ^ (1 / q) := by
  exact integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0 hf hg

/-- **`Lᵖ · Lᑫ ⊆ L¹`**：满足 `HolderTriple p q 1` 时，两个函数的逐点乘积可积。
该接口也覆盖端点指数 `1` 与 `∞`。
@isnad1 id=integrab.2h7v.s7.84cfdbc580ec from=translated src=- shape=ff87bb45 vocab=eb50b59d
-/
theorem holder_product_integrable [NormedRing 𝕜] {p q : ENNReal}
    [ENNReal.HolderTriple p q 1] {f g : α → 𝕜}
    (hf : MemLp f p μ) (hg : MemLp g q μ) : Integrable (f * g) μ := by
  exact hf.integrable_mul hg

/-- **Chebyshev–Markov 不等式**：若 `0 < p < ∞`，则函数超过阈值 `ε` 的集合满足

`ε ^ p * μ {x | ε ≤ ‖f x‖} ≤ ‖f‖ₚ ^ p`。

这里采用不含除法的乘法型陈述，因此 `ε = 0` 时也成立，不必另加正阈值假设。
有限且非零的指数条件分别由 `hp_top` 与 `hp0` 表达；强可测性保证半范数和水平集
之间的标准 Chebyshev 估计可以应用。

> **Entry**: real-analysis.lp.chebyshev
@isnad1 id=le.3h6v.s7.352e5a7d12c8 from=translated src=- shape=0b161157 vocab=f30ad976
-/
theorem chebyshev_markov [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp_top : p ≠ ∞) {f : α → E}
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε ^ p.toReal * μ {x | ε ≤ ‖f x‖ₑ} ≤ eLpNorm f p μ ^ p.toReal := by
  exact mul_meas_ge_le_pow_eLpNorm' μ hp0 hp_top hf ε

/-- **Minkowski 不等式（`eLpNorm` 形式）**：当 `p ≥ 1` 时，两个几乎处处强可测
函数之和的 `Lᵖ` 半范数不超过各自半范数之和。

该形式不要求 `f`、`g` 已经具有有限半范数；等式两边均在 `ℝ≥0∞` 中比较，故也
自然涵盖无穷值。取 `p = ∞` 时，它同时表达本质上确界范数的三角不等式。

> **Entry**: real-analysis.lp.minkowski
@isnad1 id=le.3h6v.s7.470563f5dd18 from=translated src=- shape=db64f3b8 vocab=4a410865
-/
theorem minkowski [NormedAddCommGroup E] {p : ℝ≥0∞}
    {f g : α → E} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hp : 1 ≤ p) :
    eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  exact eLpNorm_add_le hf hg hp

/-- **Minkowski 不等式（非负函数的积分形式）**：对于 `p ≥ 1`，非负扩展实值函数
满足教材中熟悉的

`(∫ (f+g)^p)^(1/p) ≤ (∫ f^p)^(1/p) + (∫ g^p)^(1/p)`。

函数值域为 `ℝ≥0∞`，所以不需要额外写非负性假设；`lintegral` 也允许积分为无穷。
这个版本把上一条抽象半范数不等式展开成可直接用于非负函数估计的公式。
@isnad1 id=le.3h5v.s7.de58f88ce6a2 from=translated src=- shape=9abae3cb vocab=ded4ce3b
-/
theorem minkowski_nonneg {p : ℝ} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hp : 1 ≤ p) :
    (∫⁻ x, (f + g) x ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) +
        (∫⁻ x, g x ^ p ∂μ) ^ (1 / p) := by
  exact ENNReal.lintegral_Lp_add_le hf hg hp

end SandronesLibrary.RealAnalysis.Lp
