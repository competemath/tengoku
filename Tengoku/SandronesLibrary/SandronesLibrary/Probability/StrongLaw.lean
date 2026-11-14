/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.WeakLaw
import Tengoku.Seed.Probability.StrongLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 强大数律

强大数律把弱大数律的“依概率收敛”加强为几乎必然收敛。对独立同分布的实值随机变量序列，首个
随机变量只需一阶可积，样本均值便在几乎每个样本点上收敛到共同期望。

本文件同时给出两层接口：

* Etemadi 的最小版本只要求两两独立；
* 标准 iid 版本使用 `iIndepFun`，并通过 `iIndepFun.indepFun` 进入最小版本。

正式证明复用 Mathlib 的 `strong_law_ae_real`。这不是把一个黑箱结论冒充教材证明：Mathlib
`StrongLaw.lean` 已用 `strong_law_aux1` 至 `strong_law_aux7` 完整实现截断、几何子列、尾部替换、
子列间填隙和正负部分分解。对应 Entry 逐步解释这条证明地图及每个接口的角色。

公开签名保留 `[IsProbabilityMeasure μ]`，明确课程讨论的是概率空间。Mathlib 后端事实上能在更一般
测度上陈述并在非平凡情形内部推出概率测度性质，但这不是首个教材接口应暴露的额外强度。

> **Entry**: probability.law-large-numbers.strong
-/

namespace SandronesLibrary.Probability

open Filter MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory Topology BigOperators

/-- **Etemadi 强大数律**：一阶可积、同分布且两两独立的实值随机变量，其样本均值几乎必然收敛
到共同期望。

相比标准 iid 假设，两两独立是更弱且已足够的独立性条件。相比弱大数律的方差证明，这里只要求
一阶可积，不要求二次矩存在。
@isnad1 id=eventual.3h3v.s7.a81278289938 from=translated src=- shape=60d2ec47 vocab=546e66a3
-/
theorem strongLaw_of_pairwise_independent_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise (Function.onFun (fun f g ↦ f ⟂ᵢ[μ] g) X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω)
        atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
  simpa [div_eq_mul_inv, mul_comm] using strong_law_ae_real X hint hindep hident

/-- **iid 强大数律**：一阶可积的 iid 实值随机变量样本均值几乎必然收敛到共同期望。

`iIndepFun` 表达标准教材中的全族独立；证明仅提取其两两独立后调用 Etemadi 版本。
@isnad1 id=eventual.3h3v.s7.a1bf5e8e118a from=translated src=- shape=120eb8e3 vocab=761b05de
-/
theorem strongLaw_of_iid_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω)
        atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
  exact strongLaw_of_pairwise_independent_integrable X hint
    (fun i j hij ↦ hindep.indepFun hij) hident

end SandronesLibrary.Probability
