/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.MultivariableRiemann
import Tengoku.Seed.Analysis.BoxIntegral.UnitPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Jordan 区域 Riemann–Lebesgue 积分桥

本模块证明连续函数在 Jordan 可测区域上作零延拓后，在任意外包闭盒上 Riemann
可积，且积分值恒等于区域上的 Lebesgue 积分。因此教材定义不依赖外包盒的选择。
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory Filter
open BoxIntegral

/-- **一般零延拓 Riemann--Lebesgue 桥**：集合不必是 Jordan 可测。只要集合零可测，
零延拓在外包盒上有界并且几乎处处连续，它的多元 Riemann 积分就等于集合上的
Lebesgue 积分。

这个定理是后续放宽积分区域要求的核心接口；Jordan 边界零测只是产生“几乎处处
连续”的一种充分条件。

> **Entry**: analysis.multivariable.jordan-riemann-bridge-/
theorem hasRiemannBoxIntegral_indicator_eq_setIntegral_of_aeContinuous {n : ℕ}
    {s : Set (JordanEuc n)} {f : JordanEuc n → ℝ}
    (hs : NullMeasurableSet s volume) (I : RiemannBox n)
    (hb : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖s.indicator f x‖ ≤ C)
    (hc : ∀ᵐ x ∂volume, ContinuousAt (s.indicator f) x)
    (hsub : s ⊆ (I : Set (JordanEuc n))) :
    HasRiemannBoxIntegral (s.indicator f) I (∫ x in s, f x) := by
  have hbox := MeasureTheory.AEContinuous.hasBoxIntegral volume hb hc
    IntegrationParams.Riemann
  have hI_meas : MeasurableSet (I : Set (JordanEuc n)) := I.measurableSet_coe
  have heq : (∫ x in (I : Set (JordanEuc n)), s.indicator f x) = ∫ x in s, f x := by
    calc
      (∫ x in (I : Set (JordanEuc n)), s.indicator f x) =
          ∫ x, s.indicator f x := by
            rw [← integral_indicator hI_meas]
            congr 1
            funext x
            by_cases hx : x ∈ s
            · simp [hx, hsub hx]
            · simp [hx]
      _ = ∫ x in s, f x := integral_indicator₀ hs
  rw [← heq]
  exact hbox

/-- 连续函数在 Jordan 区域上的零延拓除边界外处处连续。-/
lemma jordan_indicator_ae_continuous {n : ℕ} {s : Set (JordanEuc n)}
    {f : JordanEuc n → ℝ} (hs : IsJordanMeasurable s) (hf : Continuous f) :
    ∀ᵐ x ∂volume, ContinuousAt (s.indicator f) x := by
  filter_upwards [compl_mem_ae_iff.mpr hs.2] with x hx
  exact hf.continuousOn.continuousAt_indicator hx

/-- 连续函数的 Jordan 零延拓在任意闭盒上有界。-/
lemma jordan_indicator_bounded_on_box {n : ℕ} {s : Set (JordanEuc n)}
    {f : JordanEuc n → ℝ} (hf : Continuous f) (I : RiemannBox n) :
    ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖s.indicator f x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := I.isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 0 C₀, fun x hx ↦ ?_⟩
  rw [Set.indicator]
  split_ifs
  · exact le_max_of_le_right (hC₀ x hx)
  · exact norm_zero.trans_le (le_max_left 0 C₀)

/-- **Jordan 区域积分桥**：在任意包含区域的盒上对零延拓取多元 Riemann 积分，
所得值等于区域上的 Lebesgue 积分。-/
theorem hasRiemannBoxIntegral_indicator_eq_setIntegral {n : ℕ}
    {s : Set (JordanEuc n)} {f : JordanEuc n → ℝ} (hs : IsJordanMeasurable s)
    (hf : Continuous f) (I : RiemannBox n) (hsub : s ⊆ (I : Set (JordanEuc n))) :
    HasRiemannBoxIntegral (s.indicator f) I (∫ x in s, f x) := by
  exact hasRiemannBoxIntegral_indicator_eq_setIntegral_of_aeContinuous
    hs.nullMeasurableSet I (jordan_indicator_bounded_on_box hf I)
      (jordan_indicator_ae_continuous hs hf) hsub

/-- 每个 Jordan 可测区域都能放进一个闭盒，并在该盒上通过零延拓取得 Riemann
积分；该积分值就是区域 Lebesgue 积分。-/
theorem exists_box_hasRiemannIntegral_jordan {n : ℕ} {s : Set (JordanEuc n)}
    {f : JordanEuc n → ℝ} (hs : IsJordanMeasurable s) (hf : Continuous f) :
    ∃ I : RiemannBox n, s ⊆ (I : Set (JordanEuc n)) ∧
      HasRiemannBoxIntegral (s.indicator f) I (∫ x in s, f x) := by
  obtain ⟨I, _, hsub⟩ := BoxIntegral.le_hasIntegralVertices_of_isBounded hs.1
  exact ⟨I, hsub, hasRiemannBoxIntegral_indicator_eq_setIntegral hs hf I hsub⟩

/-- **外包盒无关性**：两个包含同一 Jordan 区域的盒给出的零延拓 Riemann 积分值
相同，并都等于区域 Lebesgue 积分。-/
theorem riemannIntegral_jordan_independent_of_box {n : ℕ}
    {s : Set (JordanEuc n)} {f : JordanEuc n → ℝ} (hs : IsJordanMeasurable s)
    (hf : Continuous f) (I J : RiemannBox n)
    (hI : s ⊆ (I : Set (JordanEuc n))) (hJ : s ⊆ (J : Set (JordanEuc n))) :
    riemannBoxIntegral (s.indicator f) I = riemannBoxIntegral (s.indicator f) J := by
  rw [(hasRiemannBoxIntegral_indicator_eq_setIntegral hs hf I hI).integral_eq,
    (hasRiemannBoxIntegral_indicator_eq_setIntegral hs hf J hJ).integral_eq]

end SandronesLibrary.Analysis.Multivariable
