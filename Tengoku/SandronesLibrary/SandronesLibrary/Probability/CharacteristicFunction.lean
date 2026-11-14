/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Tengoku.Seed.Probability.Independence.CharacteristicFunction
import Tengoku.Seed.Probability.IdentDistrib

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 实值随机变量的特征函数

随机变量 `X : Ω → ℝ` 在测度 `μ` 下的特征函数只依赖于它的分布，因此本文件把 Mathlib 的
`charFun (μ.map X)` 直接作为正式承载。`realCharFun_eq_integral` 将这个分布层定义展开为教材公式

`φ_X(t) = ∫ ω, exp (i t X(ω)) ∂μ`。

随后证明零点归一化、连续性、模长上界、负参数共轭、缩放和平移公式。独立随机变量之和的特征
函数等于各自特征函数之积，而两个实值随机变量同分布当且仅当它们的特征函数相同。最后一个反向
命题使用有限实内积空间测度的特征函数唯一性；这里值域固定为 `ℝ`，没有把结论未经说明推广到
任意拓扑向量空间。

本文件不包含 Lévy 连续性定理、矩 Taylor 展开或中心极限定理。

> **Entry**: probability.characteristic-function
-/

namespace SandronesLibrary.Probability

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

/-- 随机变量的分布特征函数等于教材中的复指数期望。可测性保证推前积分公式适用。-/
theorem realCharFun_eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (t : ℝ) :
    charFun (μ.map X) t = ∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) ∂μ := by
  rw [charFun_apply_real, integral_map hX]
  · congr with ω
    push_cast
    rfl
  · fun_prop

/-- 概率分布的特征函数在零点取值为一。-/
theorem realCharFun_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    charFun (μ.map X) 0 = 1 := by
  rw [charFun_zero, Measure.real_def, Measure.map_apply_of_aemeasurable hX .univ]
  simp

/-- 实值随机变量的特征函数连续；不需要任何矩存在。-/
theorem realCharFun_continuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (_hX : AEMeasurable X μ) :
    Continuous (charFun (μ.map X)) := by
  exact continuous_charFun

/-- 概率特征函数的复模不超过一。-/
theorem norm_realCharFun_le_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (t : ℝ) :
    ‖charFun (μ.map X) t‖ ≤ 1 := by
  let _ : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  exact norm_charFun_le_one t

/-- 在负参数处的特征函数值是原值的复共轭。-/
theorem realCharFun_neg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (_hX : AEMeasurable X μ) (t : ℝ) :
    charFun (μ.map X) (-t) = conj (charFun (μ.map X) t) := by
  exact charFun_neg t

/-- 随机变量缩放把特征函数的参数按同一实数缩放。-/
theorem realCharFun_scale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (r t : ℝ) :
    charFun (μ.map (fun ω ↦ r * X ω)) t = charFun (μ.map X) (r * t) := by
  exact charFun_map_mul_comp hX r t

/-- 随机变量平移 `a` 后，特征函数乘上相位因子 `exp (i a t)`。-/
theorem realCharFun_translate
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (a t : ℝ) :
    charFun (μ.map (fun ω ↦ X ω + a)) t =
      charFun (μ.map X) t * Complex.exp ((a * t : ℝ) * Complex.I) := by
  rw [show (fun ω ↦ X ω + a) = (fun x ↦ x + a) ∘ X from rfl,
    ← AEMeasurable.map_map_of_aemeasurable]
  · simpa [mul_comm] using charFun_map_add_const (μ := μ.map X) a t
  · fun_prop
  · exact hX

/-- 独立实值随机变量之和的特征函数等于两个特征函数的逐点乘积。-/
theorem realCharFun_independent_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : X ⟂ᵢ[μ] Y) :
    charFun (μ.map (fun ω ↦ X ω + Y ω)) =
      charFun (μ.map X) * charFun (μ.map Y) := by
  exact hXY.charFun_map_fun_add_eq_mul hX hY

/-- 两个实值随机变量同分布，当且仅当它们的特征函数处处相同。-/
theorem identDistrib_iff_realCharFun_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν) :
    IdentDistrib X Y μ ν ↔ charFun (μ.map X) = charFun (ν.map Y) := by
  constructor
  · exact fun h ↦ congrArg charFun h.map_eq
  · intro h
    exact ⟨hX, hY, Measure.ext_of_charFun h⟩

end SandronesLibrary.Probability
