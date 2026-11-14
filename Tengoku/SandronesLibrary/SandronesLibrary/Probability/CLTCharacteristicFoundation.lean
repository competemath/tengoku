/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.LevyContinuity
import Tengoku.Seed.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Tengoku.Seed.Probability.Distributions.Gaussian.Real
import Tengoku.Seed.Probability.Independence.CharacteristicFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 中心极限定理的特征函数基础链

本文件只处理中心为零、二阶矩为一的实值 iid 序列。首先把

`(√n)⁻¹ ∑_{k<n} Xₖ`

的特征函数化为单个 `X₀` 特征函数在 `t/√n` 处的 `n` 次幂；随后由二阶 Taylor 小量证明该幂趋于
`exp (-t²/2)`；最后把这个函数识别为 `gaussianReal 0 1` 的特征函数，并通过本库 Lévy 接口得到
归一化和的概率测度弱收敛。

证明没有 import 或调用 Mathlib 的最终 `CentralLimitTheorem`。本文件尚未处理一般均值、一般正
方差、方差为零的退化边界，也没有把测度弱收敛转换为本库随机变量的 `TendstoInDistribution`
接口；因此它是最终 CLT 的基础，不是最终课程条目。

> **Entry**: probability.clt.characteristic-foundation
-/

namespace SandronesLibrary.Probability

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℕ → Ω → ℝ}

/-- 独立同分布序列的归一化前 `n` 项和，其特征函数等于单项特征函数在 `t/√n` 处的 `n` 次幂。
@isnad1 id=eq.2h6v.s7.7024cc082034 from=translated src=- shape=8cb7882c vocab=2c879681
-/
theorem normalizedSum_charFun_eq_pow
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {n : ℕ} {t : ℝ} :
    charFun (P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t =
      (charFun (P.map (X 0)) ((√n)⁻¹ * t)) ^ n := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp,
    (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ ↦ mX _)]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

variable [IsProbabilityMeasure P]

/-- 把实值随机变量序列的归一化前 `n` 项和的分布打包成 `ProbabilityMeasure ℝ`。-/
noncomputable def normalizedSumLaw
    (X : ℕ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) P) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω),
    Measure.isProbabilityMeasure_map
      ((Finset.aemeasurable_fun_sum (Finset.range n) (fun i _ ↦ hX i)).const_mul (√n)⁻¹)⟩

/-- 若 `Z` 中心为零且二阶矩为一，则其特征函数在 `t/√n` 处的 `n` 次幂趋于
`exp (-t²/2)`。
@isnad1 id=tendsto.3h5v.s7.2495c36c18de from=translated src=- shape=966ad40f vocab=d0396a2d
-/
theorem centeredVarianceOne_charFun_pow_tendsto
    {Z : Ω → ℝ} (hZ : AEMeasurable Z P)
    (h0 : P[Z] = 0) (h1 : P[Z ^ 2] = 1) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ (charFun (P.map Z) ((√n)⁻¹ * t)) ^ n)
      atTop (𝓝 (Complex.exp (-t ^ 2 / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  suffices (fun n : ℕ ↦ charFun (P.map Z) ((√n)⁻¹ * t) -
      (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : ℂ))) =o[atTop]
        fun n ↦ ((√n)⁻¹ * t) ^ 2 by
    have aux : (fun n : ℕ ↦ ‖(1 / n : ℂ)‖) = fun n : ℕ ↦ ‖(1 / n : ℝ)‖ := by simp
    rw [← Asymptotics.isLittleO_norm_right, aux, Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert! this using 4 with n <;> norm_cast <;> simp [field]
  have ht : Tendsto (fun n : ℕ ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert! (taylor_charFun_two hZ h0 h1).comp_tendsto ht using 2
  simp
  ring

/-- 中心零、二阶矩一的实值 iid 归一化和之分布，弱收敛到标准正态分布。
@isnad1 id=tendsto.4h4v.s7.17ea18a342d9 from=translated src=- shape=4d808a8b vocab=614c38bc
-/
theorem normalizedSum_probabilityMeasure_tendsto_standardGaussian
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1) :
    Tendsto
      (fun n : ℕ ↦ normalizedSumLaw X (fun i ↦ (hident i).aemeasurable_fst) n)
      atTop
      (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  refine probabilityMeasure_tendsto_iff_charFun.2 fun t ↦ ?_
  simpa [normalizedSumLaw, normalizedSum_charFun_eq_pow hindep hident,
    charFun_gaussianReal, neg_div] using
      centeredVarianceOne_charFun_pow_tendsto
        (hident 0).aemeasurable_fst h0 h1 t

end

end SandronesLibrary.Probability
