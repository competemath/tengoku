/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.CLTCharacteristicFoundation
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.DistributionConvergenceBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 一般 iid 中心极限定理（中心化与标准化）

本文件在已验收的标准化核心 `probability.clt.characteristic-foundation` 之上完成教材的一般
iid 中心极限定理。设 `X₀, X₁, …` 独立同分布、二阶矩有限，均值 `𝔼[X₀] = μ`、方差
`Var[X₀] = σ² > 0`。记

`(σ √n)⁻¹ ∑_{k<n} (Xₖ - μ)`。

本文件证明它的分布作为 `ProbabilityMeasure ℝ` 弱收敛到标准正态 `gaussianReal 0 1`，并把结论
经 `probability.convergence.distribution-bridge` 送回随机变量层的 `TendstoInDistribution`。

**证明策略是中心化 + 标准化归约**：令 `Yₖ = (Xₖ - μ)/σ`。独立性与同分布经逐点映射保持；
`Yₖ` 的均值为零、二阶矩为一；归一化和 `(√n)⁻¹ ∑ Yₖ` 与被积随机变量恒等。于是直接调用标准化
核心，不重新做特征函数或 Taylor 展开。

**退化边界单独处理**：`σ² = 0` 时标准化无定义。此时用 `Var[X₀] = 0` 推出 `X₀` 几乎必然等于
其均值，逐项同分布给出整列几乎必然为常数，归一化和几乎必然为零，分布恒为 `gaussianReal 0 0`。

上述一般情形只需要**已知目标测度** `gaussianReal 0 1` 的 Lévy 反向，因此不触及“任意点态
特征函数极限是否仍是特征函数”的存在性问题，也没有 import 或调用 Mathlib 的最终
`CentralLimitTheorem`。

> **Entry**: probability.clt.central-limit-theorem
-/

namespace SandronesLibrary.Probability

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℕ → Ω → ℝ}

/-- 逐项中心化再除以常数保持独立同分布：`Yₖ = (Xₖ - μ)/σ` 仍 `iIndepFun`。
@isnad1 id=iindepfu.1h6v.s6.28bae1693171 from=translated src=- shape=4f39d8e6 vocab=f8f38975
-/
theorem iIndepFun_centeredScaled (hindep : iIndepFun X P) (μ σ : ℝ) :
    iIndepFun (fun k ω ↦ (X k ω - μ) / σ) P :=
  hindep.comp (fun _ x ↦ (x - μ) / σ) (fun _ ↦ by fun_prop)

/-- 逐项中心化再除以常数保持同分布：`IdentDistrib (X i) (X 0)` 传递到
`IdentDistrib ((X i - μ)/σ) ((X 0 - μ)/σ)`。
@isnad1 id=identdis.1h7v.s6.683542501a9c from=translated src=- shape=f4245044 vocab=e8695d4e
-/
theorem identDistrib_centeredScaled
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (μ σ : ℝ) :
    ∀ i, IdentDistrib (fun ω ↦ (X i ω - μ) / σ)
      (fun ω ↦ (X 0 ω - μ) / σ) P P :=
  fun i ↦ (hident i).comp (u := fun x : ℝ ↦ (x - μ) / σ) (by fun_prop)

variable [IsProbabilityMeasure P]

/-- 标准化的均值条件：`P[X₀] = μ` 时 `P[(X₀ - μ)/σ] = 0`（要求 `X₀` 可积）。
@isnad1 id=eq.2h6v.s7.0f032048bba5 from=translated src=- shape=8576c228 vocab=19c15df1
-/
theorem integral_centeredScaled_eq_zero
    (hint : Integrable (X 0) P) (hmean : P[X 0] = μ) :
    P[fun ω ↦ (X 0 ω - μ) / σ] = 0 := by
  rw [integral_div, integral_sub hint (integrable_const μ), integral_const, hmean]
  simp

omit [IsProbabilityMeasure P] in
/-- 标准化的二阶矩条件：二阶中心矩为 `σ²` 时 `P[((X₀ - μ)/σ)²] = 1`（要求 `σ ≠ 0`）。
@isnad1 id=eq.2h6v.s7.0edd85be1c40 from=translated src=- shape=aa255e9f vocab=5fc704bf
-/
theorem integral_sq_centeredScaled_eq_one
    (hvar : P[fun ω ↦ (X 0 ω - μ) ^ 2] = σ ^ 2) (hσ : σ ≠ 0) :
    P[fun ω ↦ ((X 0 ω - μ) / σ) ^ 2] = 1 := by
  have hfun : (fun ω ↦ ((X 0 ω - μ) / σ) ^ 2)
      = fun ω ↦ (X 0 ω - μ) ^ 2 / σ ^ 2 := by
    funext ω; rw [div_pow]
  rw [hfun, integral_div, hvar]
  exact div_self (pow_ne_zero 2 hσ)

/-- 中心化、再按 `σ √n` 缩放的 `n` 项和的分布，打包为 `ProbabilityMeasure ℝ`。-/
noncomputable def centeredScaledSumLaw (X : ℕ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) P)
    (μ σ : ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨P.map (fun ω ↦ (σ * √n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - μ)),
    Measure.isProbabilityMeasure_map
      ((Finset.aemeasurable_fun_sum _ fun i _ ↦ (hX i).sub_const μ).const_mul (σ * √n)⁻¹)⟩

/-- 标准化序列的归一化和律与中心化缩放和律是同一个推前测度，逐点由域的乘法结合律给出。
@isnad1 id=eq.1h7v.s6.16e78d834380 from=translated src=- shape=3afffd39 vocab=7b02fd2c
-/
theorem centeredScaledSumLaw_eq_normalizedSumLaw
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (μ σ : ℝ) (n : ℕ) :
    normalizedSumLaw (fun k ω ↦ (X k ω - μ) / σ)
        (fun i ↦ ((hident i).aemeasurable_fst.sub_const μ).div_const σ) n =
      centeredScaledSumLaw X (fun i ↦ (hident i).aemeasurable_fst) μ σ n := by
  apply Subtype.ext
  simp only [normalizedSumLaw, centeredScaledSumLaw]
  apply Measure.map_congr
  filter_upwards with ω
  rw [← Finset.sum_div, div_eq_mul_inv, mul_inv_rev]
  ring

/-- **一般 iid 中心极限定理（正方差情形）**。设实值 iid 序列 `X` 满足 `X₀ ∈ L²`、
`P[X₀] = μ`、`Var[X₀] = σ²` 且 `σ > 0`，则中心化并按 `σ √n` 缩放的 `n` 项和的分布弱收敛到
标准正态 `gaussianReal 0 1`。

证明把 `Yₖ = (Xₖ - μ)/σ` 代入已验收的标准化核心；不调用 Mathlib 最终 CLT。
@isnad1 id=tendsto.6h6v.s8.367710fe8473 from=translated src=- shape=506c4d9a vocab=5fed4aa3
-/
theorem iid_centeredScaled_clt
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hXmem : MemLp (X 0) 2 P)
    (hmean : P[X 0] = μ) (hvar : variance (X 0) P = σ ^ 2)
    (hσ : 0 < σ) :
    Tendsto (fun n ↦ centeredScaledSumLaw X (fun i ↦ (hident i).aemeasurable_fst) μ σ n)
      atTop (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hint : Integrable (X 0) P := hXmem.integrable (by norm_num)
  have hvarInt : P[fun ω ↦ (X 0 ω - μ) ^ 2] = σ ^ 2 := by
    rw [← hmean, ← variance_eq_integral hXmem.aemeasurable, hvar]
  have hbase := normalizedSum_probabilityMeasure_tendsto_standardGaussian
    (P := P) (X := fun k ω ↦ (X k ω - μ) / σ)
    (iIndepFun_centeredScaled hindep μ σ)
    (identDistrib_centeredScaled hident μ σ)
    (integral_centeredScaled_eq_zero hint hmean)
    (integral_sq_centeredScaled_eq_one hvarInt hσ.ne')
  exact hbase.congr' (Eventually.of_forall fun n ↦
    centeredScaledSumLaw_eq_normalizedSumLaw hident μ σ n)

/-- **一般 iid 中心极限定理的随机变量层消费者**。在上一段弱收敛之外，若 `Z` 的分布是标准正态，
则中心化缩放和依分布收敛到 `Z`（`TendstoInDistribution`）。
@isnad1 id=tendstoi.8h10v.s8.dac387be0776 from=translated src=- shape=aab27284 vocab=b813dc14
-/
theorem iid_centeredScaled_clt_tendstoInDistribution
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : AEMeasurable Z P') (hZlaw : P'.map Z = gaussianReal 0 1)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hXmem : MemLp (X 0) 2 P)
    (hmean : P[X 0] = μ) (hvar : variance (X 0) P = σ ^ 2)
    (hσ : 0 < σ) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (σ * √n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - μ))
      atTop Z (fun _ ↦ P) P' :=
  tendstoInDistribution_of_tendsto_law_gaussian
    (Y := fun (n : ℕ) ω ↦ (σ * √n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - μ))
    (fun n ↦ (Finset.aemeasurable_fun_sum _ fun i _ ↦
      (hident i).aemeasurable_fst.sub_const μ).const_mul (σ * √n)⁻¹)
    hZ hZlaw
    (by simpa [lawProbabilityMeasure, centeredScaledSumLaw] using
      iid_centeredScaled_clt hindep hident hXmem hmean hvar hσ)

/-- **退化方差边界**。若 `X₀ ∈ L²`、`P[X₀] = μ` 且 `Var[X₀] = 0`，则 `X₀` 几乎必然等于 `μ`；
同分布把这一点传给每一项，于是中心化归一化和几乎必然为零，其分布恒为 `gaussianReal 0 0`
（即 `dirac 0`）。
@isnad1 id=tendsto.4h5v.s8.ef548deea06a from=translated src=- shape=33db3111 vocab=a9c0b1c7
-/
theorem degenerateVariance_centeredSum_tendsto
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hXmem : MemLp (X 0) 2 P) (hmean : P[X 0] = μ)
    (hvar : variance (X 0) P = 0) :
    Tendsto
      (fun n : ℕ ↦ lawProbabilityMeasure
        (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - μ))
        ((Finset.aemeasurable_fun_sum _ fun i _ ↦
          (hident i).aemeasurable_fst.sub_const μ).const_mul (√n)⁻¹))
      atTop (𝓝 (⟨gaussianReal 0 0, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hconst0 : ∀ᵐ ω ∂P, X 0 ω = μ := by
    have h := ae_eq_integral_of_variance_eq_zero hXmem hvar
    filter_upwards [h] with ω hω
    rwa [hmean] at hω
  have hconst : ∀ k, ∀ᵐ ω ∂P, X k ω = μ := fun k ↦
    (hident k).symm.ae_snd (measurableSet_singleton μ) hconst0
  have hmap : ∀ n : ℕ, P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - μ)) =
      Measure.dirac 0 := by
    intro n
    have hae : (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - μ)) =ᵐ[P] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(Finset.eventually_all (Finset.range n)).2 (fun k _ ↦ hconst k)] with ω hω
      have hzero : (∑ k ∈ Finset.range n, (X k ω - μ)) = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        rw [hω k hk, sub_self]
      rw [hzero, mul_zero]
    rw [Measure.map_congr hae, Measure.map_const]
    simp
  refine tendsto_const_nhds.congr' (Eventually.of_forall fun n ↦ ?_)
  apply Subtype.ext
  simp only [lawProbabilityMeasure]
  rw [gaussianReal_zero_var, hmap n]

end

end SandronesLibrary.Probability
