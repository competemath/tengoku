/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.RiemannCriterion
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.Calculus
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.SpecialFunctions
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Riemann 积分值桥、微积分基本定理与计算公式

`Riemann.lean` 已经对闭区间连续函数证明了自建 Darboux 积分与 Mathlib 的
Lebesgue 区间积分数值相同。本文件利用 `RiemannCriterion.lean` 中完成的 Lebesgue
判据，把该结论推广到标准意义下的全部 Riemann 可积函数。后半部分在这一桥梁上
集中建立微积分基本定理、分部积分、换元法以及初等函数的定积分公式。

这里的“标准意义”由 `RiemannIntegrableWithBound f a b` 表示：函数在 `[a,b]`
有界，并且 Darboux 上下和之差可以任意小。之所以不直接使用早期定义
`RiemannIntegrable`，是因为后者只记录上下和逼近条件，没有把教材定义中的有界性
写入类型。

证明分三层：

1. Lebesgue 判据给出几乎处处连续性；删去包含全部不连续点的可测零测集后，函数在
   剩余可测集上连续，因此强可测，再与全局有界性合并得到 `Ioc a b` 上可积。
2. 对任意 Darboux 分划，用各小闭区间上的下确界和上确界构造两个阶梯函数。全局
   有界性保证这些确界有限，并逐点得到 `sP ≤ f ≤ uP`。
3. 阶梯函数积分分别等于 Darboux 下和与上和，故每个下和不超过 Lebesgue 积分、
   每个上和不小于它。最后用 Riemann 可积性提供任意小的上下和间隙完成夹逼。
-/

namespace SandronesLibrary.RealAnalysis.Riemann

open MeasureTheory
open scoped ENNReal Interval BigOperators Topology

/-- 标准 Riemann 可积函数在相应半开区间上也是 Lebesgue 可积的。

由 Lebesgue 判据取得几乎处处连续性，再把坏点装入可测零测集 `N`。函数在
`Icc a b \ N` 上连续，所以在该集合的限制测度下强可测；零测集不改变限制测度。
最后由闭区间有界性和区间有限测度得到可积性。-/
private lemma integrableOn_Ioc_of_riemannIntegrableWithBound {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h : RiemannIntegrableWithBound f a b) :
    IntegrableOn f (Set.Ioc a b) volume := by
  have hc := riemannIntegrableWithBound_ae_continuousOn hab h
  obtain ⟨N, hNmeas, hbad, hNnull⟩ := ae_continuity_exceptional_measurable_hull hc
  let G := Set.Icc a b \ N
  have hGmeas : MeasurableSet G := measurableSet_Icc.diff hNmeas
  have hfG : ContinuousOn f G := by
    intro x hx
    have hxcont : ContinuousWithinAt f (Set.Icc a b) x := by
      by_contra hxnot
      exact hx.2 (hbad ⟨hx.1, hxnot⟩)
    exact hxcont.mono Set.sdiff_subset
  have hmeasG : AEStronglyMeasurable f (volume.restrict G) :=
    hfG.aestronglyMeasurable hGmeas
  have haeN : ∀ᵐ x ∂volume, x ∉ N := by
    rw [ae_iff]
    simpa using hNnull
  have hae : Set.Icc a b =ᵐ[volume] G := by
    filter_upwards [haeN] with x hx
    apply propext
    change x ∈ Set.Icc a b ↔ x ∈ Set.Icc a b ∧ x ∉ N
    exact ⟨fun hmem => ⟨hmem, hx⟩, fun hmem => hmem.1⟩
  have hmeasIcc : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)) := by
    rw [Measure.restrict_congr_set hae]
    exact hmeasG
  have hmeasIoc : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)) :=
    hmeasIcc.mono_set Set.Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ := h.1
  have hfinite : (volume.restrict (Set.Ioc a b)) Set.univ ≠ ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)).restrict Set.univ, ‖f x‖ ≤ C := by
    rw [Measure.restrict_univ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa [Real.norm_eq_abs] using hC x (Set.Ioc_subset_Icc_self hx)
  simpa [IntegrableOn] using
    Measure.integrableOn_of_bounded (μ := volume.restrict (Set.Ioc a b))
      (s := Set.univ) hfinite hmeasIoc hbound

/-- 任意 Darboux 下和都不超过函数的 Lebesgue 区间积分。

下阶梯函数在第 `i` 个小区间上取函数像集的下确界。有界性确保像集有下界，故该
下确界不超过区间内每个函数值；积分保序后使用阶梯积分公式即可。-/
private lemma lowerSum_le_integral_of_riemannIntegrableWithBound {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (h : RiemannIntegrableWithBound f a b) (P : DarbouxPartition a b) :
    lowerSum f P ≤ ∫ x in Set.Ioc a b, f x ∂volume := by
  let sP : ℝ → ℝ := fun t => ∑ i ∈ Finset.range P.n,
    (Set.Ioc (P.x i) (P.x (i+1))).indicator
      (fun _ : ℝ => sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) t
  have hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1) := by
    intro i hi
    exact (P.strict i (Finset.mem_range.mp hi)).le
  have hsub := partition_subinterval_sub hab.le P hstep
  have hsP : ∀ t, (Set.Ioc a b).indicator sP t = sP t := by
    intro t
    exact step_indicator_identity
      (c := fun i => sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) hsub t
  have hsP_le : ∀ t ∈ Set.Ioc a b, sP t ≤ f t := by
    intro t ht
    rcases partition_cover P.x0 P.xN P.strict ht with ⟨i, hi, hti, hti1⟩
    have hdisj : ∀ j, j < P.n → j ≠ i →
        t ∉ Set.Ioc (P.x j) (P.x (j+1)) := by
      intro j hj hji
      exact partition_disjoint P.strict hi hj hji.symm ⟨hti, hti1⟩
    have heval : sP t = sInf (f '' Set.Icc (P.x i) (P.x (i+1))) := by
      exact step_eval_at hi ⟨hti, hti1⟩ hdisj
    obtain ⟨C, hC⟩ := h.1
    have hbdd : BddBelow (f '' Set.Icc (P.x i) (P.x (i+1))) := by
      refine ⟨-C, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have hxi := partition_point_mem hab.le P.x0 P.xN P.strict (le_of_lt hi)
      have hxi1 := partition_point_mem hab.le P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)
      have hxab : x ∈ Set.Icc a b :=
        Set.Icc_subset_Icc hxi.1 hxi1.2 ⟨hx.1, hx.2⟩
      exact (abs_le.mp (hC x hxab)).1
    rw [heval]
    exact csInf_le hbdd ⟨t, ⟨le_of_lt hti, hti1⟩, rfl⟩
  have hmono : ∀ t, (Set.Ioc a b).indicator sP t ≤
      (Set.Ioc a b).indicator f t := by
    intro t
    by_cases ht : t ∈ Set.Ioc a b
    · simpa [Set.indicator_of_mem ht] using hsP_le t ht
    · simp [Set.indicator, ht]
  have hisP : Integrable ((Set.Ioc a b).indicator sP) volume := by
    have hsP_int : Integrable sP volume := by
      apply integrable_finsetSum
      intro i hi
      rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
      have hfin : volume (Set.Ioc (P.x i) (P.x (i+1))) ≠ ∞ := by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      exact integrableOn_const (μ := volume) (s := Set.Ioc (P.x i) (P.x (i+1)))
        (C := sInf (f '' Set.Icc (P.x i) (P.x (i+1)))) (hs := hfin)
    have hident : (Set.Ioc a b).indicator sP = sP := funext hsP
    rwa [hident]
  have hif : Integrable ((Set.Ioc a b).indicator f) volume := by
    rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
    exact integrableOn_Ioc_of_riemannIntegrableWithBound hab.le h
  have hmain := lower_sum_le_interval (f := f) (sP := sP) (s := Set.Ioc a b)
    (hs := measurableSet_Ioc) (hsP := hsP) (hf_mono := hmono)
    (hisP := hisP) (hif := hif)
  calc
    lowerSum f P = ∫ t : ℝ, sP t ∂volume := (step_integral_eq_lowerSum P hstep).symm
    _ ≤ ∫ x in Set.Ioc a b, f x ∂volume := hmain

/-- 函数的 Lebesgue 区间积分不超过任意 Darboux 上和。

这是上一引理的对偶版本：上阶梯函数在每个小区间取函数像集的上确界；有界性保证
像集有上界，而上确界逐点支配 `f`。-/
private lemma integral_le_upperSum_of_riemannIntegrableWithBound {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (h : RiemannIntegrableWithBound f a b) (P : DarbouxPartition a b) :
    (∫ x in Set.Ioc a b, f x ∂volume) ≤ upperSum f P := by
  let uP : ℝ → ℝ := fun t => ∑ i ∈ Finset.range P.n,
    (Set.Ioc (P.x i) (P.x (i+1))).indicator
      (fun _ : ℝ => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) t
  have hstep : ∀ i ∈ Finset.range P.n, P.x i ≤ P.x (i+1) := by
    intro i hi
    exact (P.strict i (Finset.mem_range.mp hi)).le
  have hsub := partition_subinterval_sub hab.le P hstep
  have huP : ∀ t, (Set.Ioc a b).indicator uP t = uP t := by
    intro t
    exact step_indicator_identity
      (c := fun i => sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) hsub t
  have hf_le : ∀ t ∈ Set.Ioc a b, f t ≤ uP t := by
    intro t ht
    rcases partition_cover P.x0 P.xN P.strict ht with ⟨i, hi, hti, hti1⟩
    have hdisj : ∀ j, j < P.n → j ≠ i →
        t ∉ Set.Ioc (P.x j) (P.x (j+1)) := by
      intro j hj hji
      exact partition_disjoint P.strict hi hj hji.symm ⟨hti, hti1⟩
    have heval : uP t = sSup (f '' Set.Icc (P.x i) (P.x (i+1))) := by
      exact step_eval_at hi ⟨hti, hti1⟩ hdisj
    obtain ⟨C, hC⟩ := h.1
    have hbdd : BddAbove (f '' Set.Icc (P.x i) (P.x (i+1))) := by
      refine ⟨C, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have hxi := partition_point_mem hab.le P.x0 P.xN P.strict (le_of_lt hi)
      have hxi1 := partition_point_mem hab.le P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)
      have hxab : x ∈ Set.Icc a b :=
        Set.Icc_subset_Icc hxi.1 hxi1.2 ⟨hx.1, hx.2⟩
      exact (abs_le.mp (hC x hxab)).2
    rw [heval]
    exact le_csSup hbdd ⟨t, ⟨le_of_lt hti, hti1⟩, rfl⟩
  have hmono : ∀ t, (Set.Ioc a b).indicator f t ≤
      (Set.Ioc a b).indicator uP t := by
    intro t
    by_cases ht : t ∈ Set.Ioc a b
    · simpa [Set.indicator_of_mem ht] using hf_le t ht
    · simp [Set.indicator, ht]
  have hif : Integrable ((Set.Ioc a b).indicator f) volume := by
    rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
    exact integrableOn_Ioc_of_riemannIntegrableWithBound hab.le h
  have hiuP : Integrable ((Set.Ioc a b).indicator uP) volume := by
    have huP_int : Integrable uP volume := by
      apply integrable_finsetSum
      intro i hi
      rw [integrable_indicator_iff (hs := measurableSet_Ioc)]
      have hfin : volume (Set.Ioc (P.x i) (P.x (i+1))) ≠ ∞ := by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      exact integrableOn_const (μ := volume) (s := Set.Ioc (P.x i) (P.x (i+1)))
        (C := sSup (f '' Set.Icc (P.x i) (P.x (i+1)))) (hs := hfin)
    have hident : (Set.Ioc a b).indicator uP = uP := funext huP
    rwa [hident]
  calc
    (∫ x in Set.Ioc a b, f x ∂volume) =
        ∫ t : ℝ, (Set.Ioc a b).indicator f t ∂volume :=
      (integral_indicator (hs := measurableSet_Ioc)).symm
    _ ≤ ∫ t : ℝ, (Set.Ioc a b).indicator uP t ∂volume :=
      integral_mono hif hiuP hmono
    _ = ∫ t : ℝ, uP t ∂volume := by rw [funext huP]
    _ = upperSum f P := step_sup_integral_eq_upperSum P hstep

/-- **任意标准 Riemann 可积函数的积分值桥梁**：若 `a < b`，且 `f` 在 `[a,b]`
有界并满足 Darboux 可积条件，则本库定义的 Riemann 积分值等于 Mathlib 的 Lebesgue
区间积分值。

第一方向对所有下和取上确界；第二方向选择上下和间隙小于任意 `ε > 0` 的分划，
并把 Lebesgue 积分夹在该分划的下和与上和之间。

> **Entry**: real-analysis.riemann.eq-lebesgue-general
@isnad1 id=eq.2h3v.s5.67069f572668 from=translated src=- shape=0b557429 vocab=e7665729
-/
theorem riemannIntegral_eq_interval_of_riemannIntegrableWithBound {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (h : RiemannIntegrableWithBound f a b) :
    riemannIntegral f a b = ∫ x in Set.Ioc a b, f x ∂volume := by
  apply le_antisymm
  · unfold riemannIntegral
    apply csSup_le
    · exact ⟨lowerSum f (uniformPartition a b 1 hab (by norm_num)),
        ⟨uniformPartition a b 1 hab (by norm_num), rfl⟩⟩
    · rintro y ⟨P, rfl⟩
      exact lowerSum_le_integral_of_riemannIntegrableWithBound hab h P
  · unfold riemannIntegral
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨P, hgap⟩ := h.2 ε hε
    have hU := integral_le_upperSum_of_riemannIntegrableWithBound hab h P
    have hL : lowerSum f P ≤
        sSup {x : ℝ | ∃ Q : DarbouxPartition a b, x = lowerSum f Q} := by
      apply le_csSup
      · refine ⟨∫ x in Set.Ioc a b, f x ∂volume, ?_⟩
        rintro y ⟨Q, rfl⟩
        exact lowerSum_le_integral_of_riemannIntegrableWithBound hab h Q
      · exact ⟨P, rfl⟩
    linarith

/-! ## 微积分基本定理 -/

/-- **Newton–Leibniz 公式**：连续函数若有原函数，则其 Riemann 积分等于原函数的
端点差。

> **Entry**: real-analysis.riemann.ftc
@isnad1 id=eq.3h4v.s6.9ae4849a4f64 from=translated src=- shape=cd4e858e vocab=1b22885a
-/
theorem riemannIntegral_eq_sub_of_hasDerivAt {a b : ℝ} {F f : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) :
    riemannIntegral f a b = F b - F a := by
  rw [riemannIntegral_eq_interval hab hf,
    ← intervalIntegral.integral_of_le hab.le]
  apply RealAnalysis.Calculus.ftc_2
  · simpa [Set.uIcc_of_le hab.le] using hderiv
  · have hf' : ContinuousOn f [[a, b]] := by
      simpa [Set.uIcc_of_le hab.le] using hf
    exact hf'.intervalIntegrable

/-- **微积分基本定理第一形式**：连续函数的变上限 Riemann 积分在 `x>a` 处的
导数等于被积函数在 `x` 处的值。
@isnad1 id=hasderiv.2h3v.s6.e9a65cea4d25 from=translated src=- shape=95811a0b vocab=d3ed4575
-/
theorem hasDerivAt_riemannIntegral_right {a x : ℝ} {f : ℝ → ℝ}
    (hax : a < x) (hf : Continuous f) :
    HasDerivAt (fun u => riemannIntegral f a u) (f x) x := by
  have hFTC : HasDerivAt (fun u : ℝ => ∫ t in a..u, f t) (f x) x :=
    (RealAnalysis.Calculus.ftc_1_right (hf.intervalIntegrable a x)
      (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt).hasDerivAt
  apply hFTC.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hax] with u hau
  rw [riemannIntegral_eq_interval hau hf.continuousOn,
    ← intervalIntegral.integral_of_le hau.le]

/-! ## 分部积分与换元法 -/

/-- **分部积分公式**：`∫ u v' = u(b)v(b)-u(a)v(a)-∫u'v`。

> **Entry**: real-analysis.riemann.parts-substitution
@isnad1 id=eq.7h6v.s8.c3941dc8a53f from=translated src=- shape=8fde59be vocab=f99e6fe8
-/
theorem riemannIntegral_mul_deriv_eq_deriv_mul {a b : ℝ}
    {u v u' v' : ℝ → ℝ} (hab : a < b)
    (hu : ContinuousOn u (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc a b))
    (hu' : ContinuousOn u' (Set.Icc a b)) (hv' : ContinuousOn v' (Set.Icc a b))
    (hdu : ∀ x ∈ Set.Icc a b, HasDerivAt u (u' x) x)
    (hdv : ∀ x ∈ Set.Icc a b, HasDerivAt v (v' x) x) :
    riemannIntegral (fun x => u x * v' x) a b =
      u b * v b - u a * v a - riemannIntegral (fun x => u' x * v x) a b := by
  rw [riemannIntegral_eq_interval (f := fun x => u x * v' x) hab (hu.mul hv'),
    riemannIntegral_eq_interval (f := fun x => u' x * v x) hab (hu'.mul hv),
    ← intervalIntegral.integral_of_le hab.le,
    ← intervalIntegral.integral_of_le hab.le]
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
  · simpa [Set.uIcc_of_le hab.le] using hdu
  · simpa [Set.uIcc_of_le hab.le] using hdv
  · have hu'' : ContinuousOn u' [[a, b]] := by
      simpa [Set.uIcc_of_le hab.le] using hu'
    exact hu''.intervalIntegrable
  · have hv'' : ContinuousOn v' [[a, b]] := by
      simpa [Set.uIcc_of_le hab.le] using hv'
    exact hv''.intervalIntegrable

/-- **换元积分公式**：若 `φ'=φ'` 且 `g` 连续，则
`∫ₐᵇ g(φ(x))φ'(x) dx = ∫_{φ(a)}^{φ(b)} g(u) du`。
@isnad1 id=eq.6h5v.s7.b4335d1e8ee0 from=translated src=- shape=bc059aed vocab=c0b9d24d
-/
theorem riemannIntegral_comp_mul_deriv {a b : ℝ} {φ φ' g : ℝ → ℝ}
    (hab : a < b) (hφab : φ a < φ b)
    (hφ : ContinuousOn φ (Set.Icc a b))
    (hφ' : ContinuousOn φ' (Set.Icc a b))
    (hdφ : ∀ x ∈ Set.Icc a b, HasDerivAt φ (φ' x) x)
    (hg : Continuous g) :
    riemannIntegral (fun x => (g ∘ φ) x * φ' x) a b =
      riemannIntegral g (φ a) (φ b) := by
  have hcomp : ContinuousOn (g ∘ φ) (Set.Icc a b) := hg.comp_continuousOn hφ
  rw [riemannIntegral_eq_interval
      (f := fun x => (g ∘ φ) x * φ' x) hab (hcomp.mul hφ'),
    riemannIntegral_eq_interval hφab hg.continuousOn,
    ← intervalIntegral.integral_of_le hab.le,
    ← intervalIntegral.integral_of_le hφab.le]
  apply intervalIntegral.integral_comp_mul_deriv
  · simpa [Set.uIcc_of_le hab.le] using hdφ
  · simpa [Set.uIcc_of_le hab.le] using hφ'
  · exact hg

/-- 分部积分例：`∫ₐᵇ x eˣ dx = b eᵇ-a eᵃ-(eᵇ-eᵃ)`。
@isnad1 id=eq.1h2v.s6.2fd1479ec986 from=translated src=- shape=6ef0a8fd vocab=e77a4bad
-/
theorem riemannIntegral_id_mul_exp {a b : ℝ} (hab : a < b) :
    riemannIntegral (fun x => x * Real.exp x) a b =
      b * Real.exp b - a * Real.exp a - (Real.exp b - Real.exp a) := by
  have hparts := riemannIntegral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x) (v := Real.exp)
    (u' := fun _ : ℝ => 1) (v' := Real.exp) hab
    continuousOn_id Real.continuous_exp.continuousOn
    continuousOn_const Real.continuous_exp.continuousOn
    (fun x _ => hasDerivAt_id x) (fun x _ => Real.hasDerivAt_exp x)
  have hexp : riemannIntegral Real.exp a b = Real.exp b - Real.exp a :=
    riemannIntegral_eq_sub_of_hasDerivAt hab Real.continuous_exp.continuousOn
      (fun x _ => Real.hasDerivAt_exp x)
  simp only [one_mul] at hparts
  rw [hexp] at hparts
  simpa using hparts

/-- 线性换元例：`c>0` 时，`∫ₐᵇ c exp(cx+d) dx = exp(cb+d)-exp(ca+d)`。
@isnad1 id=eq.2h4v.s6.caedded57664 from=translated src=- shape=8f44db78 vocab=15779463
-/
theorem riemannIntegral_const_mul_exp_affine {a b c d : ℝ}
    (hab : a < b) (hc : 0 < c) :
    riemannIntegral (fun x => Real.exp (c * x + d) * c) a b =
      Real.exp (c * b + d) - Real.exp (c * a + d) := by
  have hφab : c * a + d < c * b + d := by
    simpa [add_comm] using add_lt_add_right (mul_lt_mul_of_pos_left hab hc) d
  have hsubst := riemannIntegral_comp_mul_deriv
    (φ := fun x : ℝ => c * x + d) (φ' := fun _ : ℝ => c)
    (g := Real.exp) hab hφab
    ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
    continuousOn_const
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul c).add_const d)
    Real.continuous_exp
  have hexp : riemannIntegral Real.exp (c * a + d) (c * b + d) =
      Real.exp (c * b + d) - Real.exp (c * a + d) :=
    riemannIntegral_eq_sub_of_hasDerivAt hφab Real.continuous_exp.continuousOn
      (fun x _ => Real.hasDerivAt_exp x)
  rw [hexp] at hsubst
  simpa [Function.comp_def] using hsubst

/-! ## 初等函数的定积分公式 -/

/-- **幂函数积分**：`∫ₐᵇ xⁿ dx = bⁿ⁺¹/(n+1)-aⁿ⁺¹/(n+1)`。

> **Entry**: analysis.integral.examples
@isnad1 id=eq.1h3v.s7.c5557c7dbf4c from=translated src=- shape=6a8339df vocab=da1cc87e
-/
theorem riemannIntegral_pow {a b : ℝ} (n : ℕ) (hab : a < b) :
    riemannIntegral (fun x : ℝ => x ^ n) a b =
      b ^ (n + 1) / (n + 1) - a ^ (n + 1) / (n + 1) := by
  apply riemannIntegral_eq_sub_of_hasDerivAt hab (continuousOn_pow n)
  intro x hx
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simpa [Nat.add_sub_cancel, hn] using
    (hasDerivAt_pow (n + 1) x).div_const (n + 1 : ℝ)

/-- **指数函数积分**：`∫ₐᵇ eˣ dx=eᵇ-eᵃ`。
@isnad1 id=eq.1h2v.s4.57b4a3619669 from=translated src=- shape=d2ade15d vocab=6b2a0735
-/
theorem riemannIntegral_exp {a b : ℝ} (hab : a < b) :
    riemannIntegral Real.exp a b = Real.exp b - Real.exp a := by
  exact riemannIntegral_eq_sub_of_hasDerivAt hab Real.continuous_exp.continuousOn
    (fun x _ => Real.hasDerivAt_exp x)

/-- **余弦函数积分**：`∫ₐᵇ cos x dx=sin b-sin a`。
@isnad1 id=eq.1h2v.s4.25f5a3c0e170 from=translated src=- shape=fef9f537 vocab=a312ff79
-/
theorem riemannIntegral_cos {a b : ℝ} (hab : a < b) :
    riemannIntegral Real.cos a b = Real.sin b - Real.sin a := by
  exact riemannIntegral_eq_sub_of_hasDerivAt hab Real.continuous_cos.continuousOn
    (fun x _ => Real.hasDerivAt_sin x)

/-- **正弦函数积分**：`∫ₐᵇ sin x dx=cos a-cos b`。
@isnad1 id=eq.1h2v.s4.b29664bba7b8 from=translated src=- shape=ab0f0913 vocab=a312ff79
-/
theorem riemannIntegral_sin {a b : ℝ} (hab : a < b) :
    riemannIntegral Real.sin a b = Real.cos a - Real.cos b := by
  have h := riemannIntegral_eq_sub_of_hasDerivAt
    (F := fun x => -Real.cos x) hab Real.continuous_sin.continuousOn
    (fun x _ => (Real.hasDerivAt_cos x).neg.congr_deriv (neg_neg _))
  linarith

/-- **线性三角换元例**：`c>0` 时，`∫ₐᵇ c cos(cx+d) dx` 等于相应正弦端点差。
@isnad1 id=eq.2h4v.s6.bb2f094ac7a1 from=translated src=- shape=f3f49a55 vocab=e1b1a48d
-/
theorem riemannIntegral_const_mul_cos_affine {a b c d : ℝ}
    (hab : a < b) (hc : 0 < c) :
    riemannIntegral (fun x => Real.cos (c * x + d) * c) a b =
      Real.sin (c * b + d) - Real.sin (c * a + d) := by
  have hφab : c * a + d < c * b + d := by
    simpa [add_comm] using add_lt_add_right (mul_lt_mul_of_pos_left hab hc) d
  have hsubst := riemannIntegral_comp_mul_deriv
    (φ := fun x : ℝ => c * x + d) (φ' := fun _ : ℝ => c)
    (g := Real.cos) hab hφab
    ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
    continuousOn_const
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul c).add_const d)
    Real.continuous_cos
  rw [riemannIntegral_cos hφab] at hsubst
  simpa [Function.comp_def] using hsubst

end SandronesLibrary.RealAnalysis.Riemann
