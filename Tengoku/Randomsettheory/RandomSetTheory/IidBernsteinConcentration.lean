/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.IidConcentration
import Tengoku.Randomsettheory.RandomSetTheory.BernsteinEuclideanNet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bernstein concentration for iid random compact sets

This module discharges the independence and identical-distribution
hypotheses in the Bernstein random-set bound.  A Bernstein MGF certificate
is required only for the first observation in each unit direction; identical
distribution transports it to every observation, while independence follows
from measurable composition.

The deterministic radius is still explicit.  Thus this is the iid bridge for
the Bernstein API, not a derivation of Bernstein moments from an unbounded
Orlicz envelope.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Real Set Metric Finset MeasureTheory ProbabilityTheory Module
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal

noncomputable section

namespace RandomSetTheory

/-- Dimension-explicit iid Bernstein concentration around the closed convex
Aumann target.  It is enough to certify the Bernstein MGF bound for the
zeroth observation, uniformly over unit directions.
@isnad1 id=le.12h12v.s9.7fc392534b9e from=translated src=- shape=a6e9e744 vocab=087c3a50
-/
theorem hausdorffDist_convexified_iid_risk_bound_dimensional_bernstein
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    {R : ℝ} (hFbound : ∀ z, ∀ y ∈ F z, ‖y‖ ≤ R)
    (v b : ℝ≥0) (hv : 0 < (v : ℝ))
    (hB₀ : ∀ w : E, ‖w‖ ≤ 1 →
      ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω)))
          (iidAumannTarget μ (X 0) F) w 0) v b μ)
    {n : ℕ} (hn : 0 < n) {eps x : ℝ}
    (heps : 0 < eps) (hx : 0 ≤ x) :
    μ.real {ω |
        (Real.sqrt (2 *
              (((∑ _i ∈ Finset.range n, v : ℝ≥0) : ℝ)) * x) +
            2 * (b : ℝ) * x) / (n : ℝ) + (R + R) * eps <
          hausdorffDist
            (closedConvexHull ℝ
              (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
            (iidAumannTarget μ (X 0) F)} ≤
      (1 + 2 / eps) ^ finrank ℝ E * (2 * exp (-x)) := by
  let S₀ : Ω → Set E := fun ω => F (X 0 ω)
  let A : Set E := closure (aumannExpectation μ S₀)
  let L : Set E := closedConvexHull ℝ A
  have hS₀Effros : RandomSet.IsEffrosMeasurable S₀ :=
    hF.comp_measurable (hX 0)
  have hS₀compact : ∀ ω, IsCompact (S₀ ω) := fun ω =>
    hFcompact (X 0 ω)
  have hS₀ne : ∀ ω, (S₀ ω).Nonempty := fun ω =>
    hFne (X 0 ω)
  have hg : Integrable (fun _ : Ω => R) μ := integrable_const R
  have hS₀dom : ∀ ω, ∀ y ∈ S₀ ω, ‖y‖ ≤ R := fun ω =>
    hFbound (X 0 ω)
  have hAcompact : IsCompact A :=
    closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall hS₀dom)
  have hfOne : IsIntegrableSelection μ S₀
      (supportApproximateSelection
        hS₀Effros hS₀compact hS₀ne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom 0 (by norm_num)
  have hAne : A.Nonempty :=
    (aumannExpectation_nonempty_of_selection hfOne).closure
  have hLcompact : IsCompact L := closedConvexHull_compact hAcompact
  have hLne : L.Nonempty := hAne.mono subset_closedConvexHull
  have hLconv : Convex ℝ L := convex_closedConvexHull
  have hLbound : ∀ y ∈ L, ‖y‖ ≤ R := by
    have hAsub : A ⊆ Metric.closedBall (0 : E) R := by
      intro y hy
      have hyR := norm_le_integral_envelope_of_mem_closure_aumannExpectation
        hg (Filter.Eventually.of_forall hS₀dom) hy
      have hyR' : ‖y‖ ≤ R := by simpa using hyR
      simpa [Metric.mem_closedBall, dist_zero_right] using hyR'
    have hLsub : L ⊆ Metric.closedBall (0 : E) R :=
      closedConvexHull_min hAsub (convex_closedBall (0 : E) R)
        Metric.isClosed_closedBall
    intro y hy
    simpa [Metric.mem_closedBall, dist_zero_right] using hLsub hy
  have hHullCompact : ∀ i ω,
      IsCompact (closedConvexHull ℝ (F (X i ω))) := fun i ω =>
    closedConvexHull_compact (hFcompact (X i ω))
  have hHullNe : ∀ i ω,
      (closedConvexHull ℝ (F (X i ω))).Nonempty := fun i ω =>
    (hFne (X i ω)).mono subset_closedConvexHull
  have hHullBound : ∀ i ω, ∀ y ∈ closedConvexHull ℝ (F (X i ω)),
      ‖y‖ ≤ R := by
    intro i ω
    have hsub : closedConvexHull ℝ (F (X i ω)) ⊆
        Metric.closedBall (0 : E) R := by
      apply closedConvexHull_min
      · intro y hy
        simpa [Metric.mem_closedBall, dist_zero_right] using
          hFbound (X i ω) y hy
      · exact convex_closedBall (0 : E) R
      · exact Metric.isClosed_closedBall
    intro y hy
    simpa [Metric.mem_closedBall, dist_zero_right] using hsub hy
  have hdevIndep : ∀ w : E, ‖w‖ ≤ 1 →
      ProbabilityTheory.iIndepFun
        (directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω))) L w) μ :=
    fun w _ => iIndepFun_convexifiedDirectionalSupportDeviation
      X hindep F hF hFcompact hFne L w
  have hdevBernstein : ∀ w : E, ‖w‖ ≤ 1 → ∀ i ∈ Finset.range n,
      ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation
          (fun j ω => closedConvexHull ℝ (F (X j ω))) L w i) v b μ := by
    intro w hw i _hi
    have hmap : Measurable (fun z =>
        supportFunction (closedConvexHull ℝ (F z)) w - supportFunction L w) :=
      (measurable_supportFunction_closedConvexHull_of_effros
        hF hFcompact hFne w).sub_const (supportFunction L w)
    have hid : IdentDistrib
        (directionalSupportDeviation
          (fun j ω => closedConvexHull ℝ (F (X j ω))) L w 0)
        (directionalSupportDeviation
          (fun j ω => closedConvexHull ℝ (F (X j ω))) L w i) μ μ := by
      change IdentDistrib
        (fun ω => supportFunction (closedConvexHull ℝ (F (X 0 ω))) w -
          supportFunction L w)
        (fun ω => supportFunction (closedConvexHull ℝ (F (X i ω))) w -
          supportFunction L w) μ μ
      exact (hident i).symm.comp hmap
    have hbase : ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation
          (fun j ω => closedConvexHull ℝ (F (X j ω))) L w 0) v b μ := by
      simpa [L, iidAumannTarget, A, S₀] using hB₀ w hw
    exact hbase.congr_identDistrib hid
  have hV : 0 <
      ((∑ _i ∈ Finset.range n, v : ℝ≥0) : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    simpa [Finset.sum_const, nsmul_eq_mul] using mul_pos hnR hv
  have hbound :=
    hausdorffDist_minkowskiAverage_risk_bound_dimensional_bernstein_sqrt_add
      (μ := μ)
      (fun i ω => closedConvexHull ℝ (F (X i ω))) L
      (Finset.range n) (Finset.nonempty_range_iff.mpr hn.ne')
      (fun _ => v) b hHullCompact hHullNe
      (fun _ _ => convex_closedConvexHull)
      hLcompact hLne hLconv hHullBound hLbound heps hx
      hdevIndep hdevBernstein hV
  have hEvent :
      {ω |
        (Real.sqrt (2 *
              (((∑ _i ∈ Finset.range n, v : ℝ≥0) : ℝ)) * x) +
            2 * (b : ℝ) * x) / (n : ℝ) + (R + R) * eps <
          hausdorffDist
            (closedConvexHull ℝ
              (minkowskiAverage (Finset.range n) (fun i => F (X i ω)))) L} =
      {ω |
        (Real.sqrt (2 *
              (((∑ i ∈ Finset.range n, (fun _ => v) i : ℝ≥0) : ℝ)) * x) +
            2 * (b : ℝ) * x) / ((Finset.range n).card : ℝ) +
              (R + R) * eps <
          hausdorffDist
            (minkowskiAverage (Finset.range n)
              (fun i => closedConvexHull ℝ (F (X i ω)))) L} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.card_range]
    rw [closedConvexHull_minkowskiAverage (Finset.range n)
      (fun i => F (X i ω))
      (fun i _ => hFcompact (X i ω))
      (fun i _ => hFne (X i ω))]
  change μ.real {ω |
      (Real.sqrt (2 *
            (((∑ _i ∈ Finset.range n, v : ℝ≥0) : ℝ)) * x) +
          2 * (b : ℝ) * x) / (n : ℝ) + (R + R) * eps <
        hausdorffDist
          (closedConvexHull ℝ
            (minkowskiAverage (Finset.range n) (fun i => F (X i ω)))) L} ≤ _
  rw [hEvent]
  simpa only using hbound

/-- Iid confidence-level Bernstein bound.  The entropy and bilateral-tail
factors are absorbed into the logarithmic threshold, leaving failure
probability exactly `δ`.
@isnad1 id=le.13h12v.s9.b81cc39b5436 from=translated src=- shape=42e6db28 vocab=c5ae3e97
-/
theorem hausdorffDist_convexified_iid_risk_bound_bernstein_confidence
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    {R : ℝ} (hFbound : ∀ z, ∀ y ∈ F z, ‖y‖ ≤ R)
    (v b : ℝ≥0) (hv : 0 < (v : ℝ))
    (hB₀ : ∀ w : E, ‖w‖ ≤ 1 →
      ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω)))
          (iidAumannTarget μ (X 0) F) w 0) v b μ)
    {n : ℕ} (hn : 0 < n) {eps δ : ℝ}
    (heps : 0 < eps) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    μ.real {ω |
        (Real.sqrt (2 *
              (((∑ _i ∈ Finset.range n, v : ℝ≥0) : ℝ)) *
                Real.log
                  (2 * (1 + 2 / eps) ^ finrank ℝ E / δ)) +
            2 * (b : ℝ) *
              Real.log
                (2 * (1 + 2 / eps) ^ finrank ℝ E / δ)) /
            (n : ℝ) + (R + R) * eps <
          hausdorffDist
            (closedConvexHull ℝ
              (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
            (iidAumannTarget μ (X 0) F)} ≤ δ := by
  let C : ℝ := (1 + 2 / eps) ^ finrank ℝ E
  let x : ℝ := Real.log (2 * C / δ)
  have hbase : 1 ≤ 1 + 2 / eps := by
    have : 0 ≤ 2 / eps := by positivity
    linarith
  have hC : 1 ≤ C := by
    dsimp [C]
    exact one_le_pow₀ hbase
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have harg : 1 ≤ 2 * C / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hargpos : 0 < 2 * C / δ := lt_of_lt_of_le zero_lt_one harg
  have hx : 0 ≤ x := by
    dsimp [x]
    exact Real.log_nonneg harg
  have hprob :=
    hausdorffDist_convexified_iid_risk_bound_dimensional_bernstein
      X hX hindep hident F hF hFcompact hFne hFbound v b hv hB₀
      hn heps hx
  change μ.real {ω |
      (Real.sqrt (2 *
            (((∑ _i ∈ Finset.range n, v : ℝ≥0) : ℝ)) * x) +
          2 * (b : ℝ) * x) / (n : ℝ) + (R + R) * eps <
        hausdorffDist
          (closedConvexHull ℝ
            (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
          (iidAumannTarget μ (X 0) F)} ≤ δ
  refine hprob.trans ?_
  change C * (2 * exp (-x)) ≤ δ
  have heq : C * (2 * exp (-x)) = δ := by
    rw [Real.exp_neg]
    have hexp : Real.exp x = 2 * C / δ := by
      dsimp [x]
      exact Real.exp_log hargpos
    rw [hexp]
    field_simp [hδ.ne', hCpos.ne']
  exact heq.le

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
