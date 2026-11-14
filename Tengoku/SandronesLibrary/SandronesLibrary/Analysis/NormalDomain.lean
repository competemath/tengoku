/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.JordanRiemannBridge
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.ProductMeasure
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.RiemannIntegralBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二维正常区域的累次积分

本模块定义由两条可测边界围成的 `x`-型正常区域，并将抽象 Fubini 定理转成教材中的
变限累次积分公式。文件末尾进一步给出完整的教材计算链：多元 Riemann 积分先化为
Lebesgue 积分，经 Fubini 降维，再用本库的一维数值桥转回 Riemann 积分。核心接口
不要求区域 Jordan 可测；Jordan 边界零测仅作为保证零延拓几乎处处连续的充分条件。
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory
open BoxIntegral
open SandronesLibrary.RealAnalysis.Riemann

/-- `x`-型正常区域：`a ≤ x ≤ b` 且 `lower x ≤ y ≤ upper x`。

> **Entry**: analysis.multivariable.normal-domain-/
def xNormalDomain (a b : ℝ) (lower upper : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}

/-- 可测上下边界已经足以保证 `x`-型正常区域可测；连续性不是 Fubini 的必要条件。
@isnad1 id=measurab.2h4v.s5.f09ce87bc32c from=translated src=- shape=5b65dbf3 vocab=e1fb438e
-/
theorem measurableSet_xNormalDomain_of_measurable {a b : ℝ} {lower upper : ℝ → ℝ}
    (hlower : Measurable lower) (hupper : Measurable upper) :
    MeasurableSet (xNormalDomain a b lower upper) := by
  unfold xNormalDomain
  measurability

/-- 连续上下边界围成的 `x`-型正常区域可测。
@isnad1 id=measurab.2h4v.s5.52d53dbfa481 from=translated src=- shape=5b65dbf3 vocab=c6da4ef0
-/
theorem measurableSet_xNormalDomain {a b : ℝ} {lower upper : ℝ → ℝ}
    (hlower : Continuous lower) (hupper : Continuous upper) :
    MeasurableSet (xNormalDomain a b lower upper) := by
  exact measurableSet_xNormalDomain_of_measurable hlower.measurable hupper.measurable

/-- `x`-型正常区域的示性函数按竖直截面分解。
@isnad1 id=eq.0h6v.s6.84cc48ec27e7 from=translated src=- shape=f73f9971 vocab=652b87de
-/
lemma indicator_xNormalDomain_section (f : ℝ × ℝ → ℝ) (a b : ℝ)
    (lower upper : ℝ → ℝ) (x : ℝ) :
    (fun y ↦ (xNormalDomain a b lower upper).indicator f (x, y)) =
      (Icc a b).indicator
        (fun x ↦ (Icc (lower x) (upper x)).indicator (fun y ↦ f (x, y))) x := by
  funext y
  by_cases hx : x ∈ Icc a b
  · by_cases hy : y ∈ Icc (lower x) (upper x)
    · simp only [mem_Icc] at hx hy
      simp [Set.indicator, xNormalDomain, hx, hy]
    · simp only [mem_Icc] at hx hy
      simp [Set.indicator, xNormalDomain, hx, hy]
  · simp only [mem_Icc] at hx
    simp [Set.indicator, xNormalDomain, hx]

/-- **正常区域累次积分公式**：`x`-型区域上的二重积分等于先沿竖直截面积分，
再对 `x` 积分。
@isnad1 id=eq.3h5v.s7.6fd5d58956b0 from=translated src=- shape=6919988a vocab=1c53da08
-/
theorem integral_xNormalDomain_eq_iterated {f : ℝ × ℝ → ℝ} {a b : ℝ}
    {lower upper : ℝ → ℝ} (hlower : Continuous lower) (hupper : Continuous upper)
    (hf : IntegrableOn f (xNormalDomain a b lower upper) (volume.prod volume)) :
    (∫ z in xNormalDomain a b lower upper, f z ∂(volume.prod volume)) =
      ∫ x in Icc a b, ∫ y in Icc (lower x) (upper x), f (x, y) := by
  have hD := measurableSet_xNormalDomain (a := a) (b := b) hlower hupper
  have hfi : Integrable ((xNormalDomain a b lower upper).indicator f)
      (volume.prod volume) := hf.integrable_indicator hD
  calc
    (∫ z in xNormalDomain a b lower upper, f z ∂(volume.prod volume)) =
        ∫ z, (xNormalDomain a b lower upper).indicator f z ∂(volume.prod volume) :=
      (integral_indicator hD).symm
    _ = ∫ x, ∫ y, (xNormalDomain a b lower upper).indicator f (x, y) :=
      integral_prod _ hfi
    _ = ∫ x, (Icc a b).indicator
        (fun x ↦ ∫ y, (Icc (lower x) (upper x)).indicator (fun y ↦ f (x, y)) y) x := by
      congr 1
      funext x
      rw [indicator_xNormalDomain_section]
      by_cases hx : x ∈ Icc a b <;> simp [hx]
    _ = ∫ x in Icc a b, ∫ y in Icc (lower x) (upper x), f (x, y) := by
      simp_rw [integral_indicator measurableSet_Icc]

/-- **可测正常区域的 Fubini 公式**：上下边界只需可测。连续边界版本是它的教材型
特例；真正执行降维的是区域可测性和被积函数的可积性。
@isnad1 id=eq.3h5v.s7.56fe68616f0b from=translated src=- shape=6919988a vocab=830b49f2
-/
theorem integral_xNormalDomain_eq_iterated_of_measurable
    {f : ℝ × ℝ → ℝ} {a b : ℝ} {lower upper : ℝ → ℝ}
    (hlower : Measurable lower) (hupper : Measurable upper)
    (hf : IntegrableOn f (xNormalDomain a b lower upper) (volume.prod volume)) :
    (∫ z in xNormalDomain a b lower upper, f z ∂(volume.prod volume)) =
      ∫ x in Icc a b, ∫ y in Icc (lower x) (upper x), f (x, y) := by
  have hD := measurableSet_xNormalDomain_of_measurable
    (a := a) (b := b) hlower hupper
  have hfi : Integrable ((xNormalDomain a b lower upper).indicator f)
      (volume.prod volume) := hf.integrable_indicator hD
  calc
    (∫ z in xNormalDomain a b lower upper, f z ∂(volume.prod volume)) =
        ∫ z, (xNormalDomain a b lower upper).indicator f z ∂(volume.prod volume) :=
      (integral_indicator hD).symm
    _ = ∫ x, ∫ y, (xNormalDomain a b lower upper).indicator f (x, y) :=
      integral_prod _ hfi
    _ = ∫ x, (Icc a b).indicator
        (fun x ↦ ∫ y, (Icc (lower x) (upper x)).indicator (fun y ↦ f (x, y)) y) x := by
      congr 1
      funext x
      rw [indicator_xNormalDomain_section]
      by_cases hx : x ∈ Icc a b <;> simp [hx]
    _ = ∫ x in Icc a b, ∫ y in Icc (lower x) (upper x), f (x, y) := by
      simp_rw [integral_indicator measurableSet_Icc]

/-! ## 从多元 Riemann 积分到二次 Riemann 积分 -/

/-- 把积坐标中的 `x`-型正常区域搬到盒积分使用的 `Fin 2 → ℝ` 坐标。

`MeasurableEquiv.finTwoArrow` 将向量 `v` 送到 `(v 0, v 1)`；取原像后，区域的
几何含义不变，但类型与多元盒积分接口一致。-/
def xNormalDomainFin (a b : ℝ) (lower upper : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  MeasurableEquiv.finTwoArrow ⁻¹' xNormalDomain a b lower upper

/-- `Fin 2` 坐标上的正常区域 Lebesgue 积分等于积坐标版本。

这里使用 `finTwoArrow` 的保体积性；它正是从多元盒积分坐标进入 Fubini 所需的
坐标桥，不涉及任何积分计算。
@isnad1 id=eq.2h5v.s8.4569409caad1 from=translated src=- shape=db539d1a vocab=ca3176ce
-/
lemma integral_xNormalDomainFin_eq_prod
    (f : ℝ × ℝ → ℝ) (a b : ℝ) (lower upper : ℝ → ℝ)
    (hlower : Continuous lower) (hupper : Continuous upper) :
    (∫ v in xNormalDomainFin a b lower upper,
        f (MeasurableEquiv.finTwoArrow v)) =
      ∫ p in xNormalDomain a b lower upper, f p := by
  let e : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.finTwoArrow
  let g : ℝ × ℝ → ℝ := (xNormalDomain a b lower upper).indicator f
  have he : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_finTwoArrow ℝ
  have hemb : MeasurableEmbedding e := MeasurableEquiv.finTwoArrow.measurableEmbedding
  have hD : MeasurableSet (xNormalDomain a b lower upper) :=
    measurableSet_xNormalDomain hlower hupper
  have hDFin : MeasurableSet (xNormalDomainFin a b lower upper) := by
    exact hD.preimage MeasurableEquiv.finTwoArrow.measurable
  calc
    (∫ v in xNormalDomainFin a b lower upper,
        f (MeasurableEquiv.finTwoArrow v)) =
        ∫ v, (xNormalDomainFin a b lower upper).indicator
          (fun v ↦ f (MeasurableEquiv.finTwoArrow v)) v :=
      (integral_indicator hDFin).symm
    _ = ∫ v, g (e v) := by rfl
    _ = ∫ p, g p ∂(volume.prod volume) := he.integral_comp hemb g
    _ = ∫ p in xNormalDomain a b lower upper, f p := integral_indicator hD

/-- **放宽区域要求后的 Riemann--Fubini 计算桥**。

这里不假设正常区域是 Jordan 可测，也不要求边界连续。核心假设直接落在真正需要
Riemann 可积的对象——区域零延拓——上：它在外包盒中有界且几乎处处连续。区域
本身只需由可测边界给出，因而 Fubini 可以使用。随后每条截面连续即可把一维
Lebesgue 积分改写成本库的一维 Riemann 积分。
@isnad1 id=eq.8h6v.s10.ba84b21e19bc from=translated src=- shape=35ddbc77 vocab=6ea8c11e
-/
theorem riemannBoxIntegral_xNormalDomain_eq_integral_riemann_of_aeContinuous
    {f : ℝ × ℝ → ℝ} {a b : ℝ} {lower upper : ℝ → ℝ}
    (hlower : Measurable lower) (hupper : Measurable upper)
    (hlu : ∀ x ∈ Icc a b, lower x < upper x)
    (hsection : ∀ x ∈ Icc a b,
      ContinuousOn (fun y ↦ f (x, y)) (Icc (lower x) (upper x)))
    (hfi : IntegrableOn f (xNormalDomain a b lower upper) (volume.prod volume))
    (I : RiemannBox 2)
    (hb : ∃ C : ℝ, ∀ v ∈ Box.Icc I,
      ‖(xNormalDomainFin a b lower upper).indicator
        (fun w ↦ f (MeasurableEquiv.finTwoArrow w)) v‖ ≤ C)
    (hc : ∀ᵐ v ∂volume, ContinuousAt
      ((xNormalDomainFin a b lower upper).indicator
        (fun w ↦ f (MeasurableEquiv.finTwoArrow w))) v)
    (hsub : xNormalDomainFin a b lower upper ⊆ (I : Set (Fin 2 → ℝ))) :
    riemannBoxIntegral
        ((xNormalDomainFin a b lower upper).indicator
          (fun v ↦ f (MeasurableEquiv.finTwoArrow v))) I =
      ∫ x in Icc a b, riemannIntegral (fun y ↦ f (x, y)) (lower x) (upper x) := by
  have hD : MeasurableSet (xNormalDomain a b lower upper) :=
    measurableSet_xNormalDomain_of_measurable hlower hupper
  have hDFin : MeasurableSet (xNormalDomainFin a b lower upper) :=
    hD.preimage MeasurableEquiv.finTwoArrow.measurable
  calc
    riemannBoxIntegral
        ((xNormalDomainFin a b lower upper).indicator
          (fun v ↦ f (MeasurableEquiv.finTwoArrow v))) I =
        ∫ v in xNormalDomainFin a b lower upper,
          f (MeasurableEquiv.finTwoArrow v) :=
      (hasRiemannBoxIntegral_indicator_eq_setIntegral_of_aeContinuous
        hDFin.nullMeasurableSet I hb hc hsub).integral_eq
    _ = ∫ p in xNormalDomain a b lower upper, f p := by
      let e : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.finTwoArrow
      let g : ℝ × ℝ → ℝ := (xNormalDomain a b lower upper).indicator f
      have he : MeasurePreserving e volume (volume.prod volume) :=
        volume_preserving_finTwoArrow ℝ
      have hemb : MeasurableEmbedding e := MeasurableEquiv.finTwoArrow.measurableEmbedding
      calc
        _ = ∫ v, (xNormalDomainFin a b lower upper).indicator
            (fun v ↦ f (MeasurableEquiv.finTwoArrow v)) v :=
          (integral_indicator hDFin).symm
        _ = ∫ v, g (e v) := by rfl
        _ = ∫ p, g p ∂(volume.prod volume) := he.integral_comp hemb g
        _ = _ := integral_indicator hD
    _ = ∫ x in Icc a b, ∫ y in Icc (lower x) (upper x), f (x, y) :=
      integral_xNormalDomain_eq_iterated_of_measurable hlower hupper hfi
    _ = ∫ x in Icc a b,
        riemannIntegral (fun y ↦ f (x, y)) (lower x) (upper x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp
      rw [riemannIntegral_eq_interval (hlu x hx) (hsection x hx)]
      exact integral_Icc_eq_integral_Ioc

/-- **正常区域的 Riemann–Fubini 计算桥**。

该等式显式实现教材计算流程：

1. 左端的多元 Riemann 积分通过 Jordan 桥变成区域 Lebesgue 积分；
2. 保体积坐标桥将 `Fin 2 → ℝ` 改写成 `(x,y)`；
3. Fubini 将二重积分化为竖直截面的累次 Lebesgue 积分；
4. 每个截面再由本库的一维 Riemann–Lebesgue 数值桥改写成 Riemann 积分。

外层暂时保留为 Lebesgue 积分，因此本定理不需要预先证明截面积分关于 `x` 连续。
@isnad1 id=eq.7h6v.s8.b299305aa6a5 from=translated src=- shape=15494390 vocab=102035fd
-/
theorem riemannBoxIntegral_xNormalDomain_eq_integral_riemann
    {f : ℝ × ℝ → ℝ} {a b : ℝ} {lower upper : ℝ → ℝ}
    (hlower : Continuous lower) (hupper : Continuous upper)
    (hlu : ∀ x ∈ Icc a b, lower x < upper x) (hf : Continuous f)
    (hfi : IntegrableOn f (xNormalDomain a b lower upper) (volume.prod volume))
    (hs : IsJordanMeasurable (xNormalDomainFin a b lower upper))
    (I : RiemannBox 2) (hsub : xNormalDomainFin a b lower upper ⊆ (I : Set (Fin 2 → ℝ))) :
    riemannBoxIntegral
        ((xNormalDomainFin a b lower upper).indicator
          (fun v ↦ f (MeasurableEquiv.finTwoArrow v))) I =
      ∫ x in Icc a b, riemannIntegral (fun y ↦ f (x, y)) (lower x) (upper x) := by
  have hecont : Continuous (fun v : Fin 2 → ℝ ↦ MeasurableEquiv.finTwoArrow v) := by
    simpa [MeasurableEquiv.finTwoArrow_apply] using
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).continuous
  have hfFin : Continuous (fun v : Fin 2 → ℝ ↦ f (MeasurableEquiv.finTwoArrow v)) :=
    hf.comp hecont
  exact riemannBoxIntegral_xNormalDomain_eq_integral_riemann_of_aeContinuous
    hlower.measurable hupper.measurable hlu
    (fun _ _ ↦ (hf.comp (continuous_const.prodMk continuous_id)).continuousOn)
    hfi I (jordan_indicator_bounded_on_box hfFin I)
    (jordan_indicator_ae_continuous hs hfFin) hsub

/-- 若截面 Riemann 积分关于外层变量连续，则外层 Lebesgue 积分也可由一维数值桥
转回 Riemann 积分。于是左端的多元 Riemann 积分等于完整的二次 Riemann 积分。
@isnad1 id=eq.9h6v.s8.6facffa8531d from=translated src=- shape=ef8a2e1a vocab=c5a16bd8
-/
theorem riemannBoxIntegral_xNormalDomain_eq_iteratedRiemann
    {f : ℝ × ℝ → ℝ} {a b : ℝ} {lower upper : ℝ → ℝ}
    (hab : a < b) (hlower : Continuous lower) (hupper : Continuous upper)
    (hlu : ∀ x ∈ Icc a b, lower x < upper x) (hf : Continuous f)
    (hfi : IntegrableOn f (xNormalDomain a b lower upper) (volume.prod volume))
    (hs : IsJordanMeasurable (xNormalDomainFin a b lower upper))
    (houter : ContinuousOn
      (fun x ↦ riemannIntegral (fun y ↦ f (x, y)) (lower x) (upper x)) (Icc a b))
    (I : RiemannBox 2) (hsub : xNormalDomainFin a b lower upper ⊆ (I : Set (Fin 2 → ℝ))) :
    riemannBoxIntegral
        ((xNormalDomainFin a b lower upper).indicator
          (fun v ↦ f (MeasurableEquiv.finTwoArrow v))) I =
      riemannIntegral
        (fun x ↦ riemannIntegral (fun y ↦ f (x, y)) (lower x) (upper x)) a b := by
  rw [riemannBoxIntegral_xNormalDomain_eq_integral_riemann
    hlower hupper hlu hf hfi hs I hsub]
  rw [riemannIntegral_eq_interval hab houter]
  exact integral_Icc_eq_integral_Ioc

/-! ## `y`-型正常区域 -/

/-- `y`-型正常区域：`c ≤ y ≤ d` 且 `left y ≤ x ≤ right y`。-/
def yNormalDomain (c d : ℝ) (left right : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc c d ∧ p.1 ∈ Icc (left p.2) (right p.2)}

/-- 可测左右边界围成的 `y`-型正常区域可测。
@isnad1 id=measurab.2h4v.s5.d9622164cc56 from=translated src=- shape=5b65dbf3 vocab=66336ce7
-/
theorem measurableSet_yNormalDomain_of_measurable {c d : ℝ} {left right : ℝ → ℝ}
    (hleft : Measurable left) (hright : Measurable right) :
    MeasurableSet (yNormalDomain c d left right) := by
  unfold yNormalDomain
  measurability

/-- `y`-型正常区域的示性函数按水平截面分解。
@isnad1 id=eq.0h6v.s6.cfd83c090c64 from=translated src=- shape=1a8d5c29 vocab=3b7840a5
-/
lemma indicator_yNormalDomain_section (f : ℝ × ℝ → ℝ) (c d : ℝ)
    (left right : ℝ → ℝ) (y : ℝ) :
    (fun x ↦ (yNormalDomain c d left right).indicator f (x, y)) =
      (Icc c d).indicator
        (fun y ↦ (Icc (left y) (right y)).indicator (fun x ↦ f (x, y))) y := by
  funext x
  by_cases hy : y ∈ Icc c d
  · by_cases hx : x ∈ Icc (left y) (right y)
    · simp only [mem_Icc] at hy hx
      simp [Set.indicator, yNormalDomain, hy, hx]
    · simp only [mem_Icc] at hy hx
      simp [Set.indicator, yNormalDomain, hy, hx]
  · simp only [mem_Icc] at hy
    simp [Set.indicator, yNormalDomain, hy]

/-- **`y`-型正常区域的 Fubini 公式**：先沿水平截面对 `x` 积分，再对 `y` 积分。
左右边界只需可测。
@isnad1 id=eq.3h5v.s7.1297c9609f11 from=translated src=- shape=0ab96b85 vocab=66996b36
-/
theorem integral_yNormalDomain_eq_iterated_of_measurable
    {f : ℝ × ℝ → ℝ} {c d : ℝ} {left right : ℝ → ℝ}
    (hleft : Measurable left) (hright : Measurable right)
    (hf : IntegrableOn f (yNormalDomain c d left right) (volume.prod volume)) :
    (∫ z in yNormalDomain c d left right, f z ∂(volume.prod volume)) =
      ∫ y in Icc c d, ∫ x in Icc (left y) (right y), f (x, y) := by
  have hD := measurableSet_yNormalDomain_of_measurable
    (c := c) (d := d) hleft hright
  have hfi : Integrable ((yNormalDomain c d left right).indicator f)
      (volume.prod volume) := hf.integrable_indicator hD
  calc
    (∫ z in yNormalDomain c d left right, f z ∂(volume.prod volume)) =
        ∫ z, (yNormalDomain c d left right).indicator f z ∂(volume.prod volume) :=
      (integral_indicator hD).symm
    _ = ∫ y, ∫ x, (yNormalDomain c d left right).indicator f (x, y) :=
      integral_prod_symm _ hfi
    _ = ∫ y, (Icc c d).indicator
        (fun y ↦ ∫ x, (Icc (left y) (right y)).indicator (fun x ↦ f (x, y)) x) y := by
      congr 1
      funext y
      rw [indicator_yNormalDomain_section]
      by_cases hy : y ∈ Icc c d <;> simp [hy]
    _ = ∫ y in Icc c d, ∫ x in Icc (left y) (right y), f (x, y) := by
      simp_rw [integral_indicator measurableSet_Icc]

/-- 把 `y`-型正常区域搬到盒积分的 `Fin 2 → ℝ` 坐标。-/
def yNormalDomainFin (c d : ℝ) (left right : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  MeasurableEquiv.finTwoArrow ⁻¹' yNormalDomain c d left right

/-- **`y`-型区域的 Riemann--Fubini 计算桥**：多元 Riemann 积分先变成 Lebesgue
积分，交换 Fubini 次序后，再把每条水平截面转回一维 Riemann 积分。区域不需要
Jordan 可测，左右边界也只需可测。
@isnad1 id=eq.8h6v.s10.79a49a6b2c37 from=translated src=- shape=5f6c3ad9 vocab=2ca42e4d
-/
theorem riemannBoxIntegral_yNormalDomain_eq_integral_riemann_of_aeContinuous
    {f : ℝ × ℝ → ℝ} {c d : ℝ} {left right : ℝ → ℝ}
    (hleft : Measurable left) (hright : Measurable right)
    (hlr : ∀ y ∈ Icc c d, left y < right y)
    (hsection : ∀ y ∈ Icc c d,
      ContinuousOn (fun x ↦ f (x, y)) (Icc (left y) (right y)))
    (hfi : IntegrableOn f (yNormalDomain c d left right) (volume.prod volume))
    (I : RiemannBox 2)
    (hb : ∃ C : ℝ, ∀ v ∈ Box.Icc I,
      ‖(yNormalDomainFin c d left right).indicator
        (fun w ↦ f (MeasurableEquiv.finTwoArrow w)) v‖ ≤ C)
    (hc : ∀ᵐ v ∂volume, ContinuousAt
      ((yNormalDomainFin c d left right).indicator
        (fun w ↦ f (MeasurableEquiv.finTwoArrow w))) v)
    (hsub : yNormalDomainFin c d left right ⊆ (I : Set (Fin 2 → ℝ))) :
    riemannBoxIntegral
        ((yNormalDomainFin c d left right).indicator
          (fun v ↦ f (MeasurableEquiv.finTwoArrow v))) I =
      ∫ y in Icc c d, riemannIntegral (fun x ↦ f (x, y)) (left y) (right y) := by
  have hD := measurableSet_yNormalDomain_of_measurable
    (c := c) (d := d) hleft hright
  have hDFin : MeasurableSet (yNormalDomainFin c d left right) :=
    hD.preimage MeasurableEquiv.finTwoArrow.measurable
  calc
    riemannBoxIntegral
        ((yNormalDomainFin c d left right).indicator
          (fun v ↦ f (MeasurableEquiv.finTwoArrow v))) I =
        ∫ v in yNormalDomainFin c d left right,
          f (MeasurableEquiv.finTwoArrow v) :=
      (hasRiemannBoxIntegral_indicator_eq_setIntegral_of_aeContinuous
        hDFin.nullMeasurableSet I hb hc hsub).integral_eq
    _ = ∫ p in yNormalDomain c d left right, f p := by
      let e : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.finTwoArrow
      let g : ℝ × ℝ → ℝ := (yNormalDomain c d left right).indicator f
      have he : MeasurePreserving e volume (volume.prod volume) :=
        volume_preserving_finTwoArrow ℝ
      have hemb : MeasurableEmbedding e := MeasurableEquiv.finTwoArrow.measurableEmbedding
      calc
        _ = ∫ v, (yNormalDomainFin c d left right).indicator
            (fun v ↦ f (MeasurableEquiv.finTwoArrow v)) v :=
          (integral_indicator hDFin).symm
        _ = ∫ v, g (e v) := by rfl
        _ = ∫ p, g p ∂(volume.prod volume) := he.integral_comp hemb g
        _ = _ := integral_indicator hD
    _ = ∫ y in Icc c d, ∫ x in Icc (left y) (right y), f (x, y) :=
      integral_yNormalDomain_eq_iterated_of_measurable hleft hright hfi
    _ = ∫ y in Icc c d,
        riemannIntegral (fun x ↦ f (x, y)) (left y) (right y) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp
      rw [riemannIntegral_eq_interval (hlr y hy) (hsection y hy)]
      exact integral_Icc_eq_integral_Ioc

end SandronesLibrary.Analysis.Multivariable
