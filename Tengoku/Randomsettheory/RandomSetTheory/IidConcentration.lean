/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.ArtsteinVitale
import Tengoku.Randomsettheory.RandomSetTheory.DirectionalConcentration
import Tengoku.Randomsettheory.RandomSetTheory.UnitBallNets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concentration for iid random compact sets

This file discharges the scalar hypotheses of `DirectionalConcentration` in
the natural observation model.  A mutually independent identically
distributed family `X i` is mapped by an Effros-measurable compact-valued
correspondence `F`.  Measurability and independence of directional support
deviations follow by composition.  Centering follows from identical
distribution and the support-function representation of the closed Aumann
expectation.

The final theorem controls the Hausdorff distance between the convexified
empirical Minkowski average and
`closedConvexHull ℝ (closure (aumannExpectation μ (F ∘ X 0)))`.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Real Set Metric Finset MeasureTheory ProbabilityTheory
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal

noncomputable section

namespace RandomSetTheory

/-- The support function of the closed convex hull of an Effros-measurable
compact random set is measurable.
@isnad1 id=measurab.3h4v.s7.3dbabcf4e3a5 from=translated src=- shape=1aaa1234 vocab=09089f67
-/
theorem measurable_supportFunction_closedConvexHull_of_effros
    {Z E : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Z → Set E} (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    (u : E) :
    Measurable (fun z => supportFunction (closedConvexHull ℝ (F z)) u) := by
  have hraw : Measurable (fun z => supportFunction (F z) u) :=
    measurable_supportFunction hF hFcompact hFne u
  rw [show (fun z => supportFunction (closedConvexHull ℝ (F z)) u) =
      (fun z => supportFunction (F z) u) by
    funext z
    exact supportFunction_closedConvexHull (hFcompact z) (hFne z) u]
  exact hraw

/-- Measurability of every convexified directional support deviation follows
from Effros measurability of `F` and measurability of the observation.
@isnad1 id=measurab.4h9v.s7.d0f2628ad2a3 from=translated src=- shape=eba94f5b vocab=8674f5cb
-/
theorem measurable_convexifiedDirectionalSupportDeviation
    {Ω Z E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : ι → Ω → Z) (hX : ∀ i, Measurable (X i))
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    (L : Set E) (u : E) (i : ι) :
    Measurable (directionalSupportDeviation
      (fun j ω => closedConvexHull ℝ (F (X j ω))) L u i) := by
  have hsupp := (measurable_supportFunction_closedConvexHull_of_effros
    hF hFcompact hFne u).comp (hX i)
  change Measurable (fun ω =>
    supportFunction (closedConvexHull ℝ (F (X i ω))) u - supportFunction L u)
  exact hsupp.sub_const (supportFunction L u)

/-- Mutual independence of observations is preserved by convexified
directional support deviations.
@isnad1 id=iindepfu.4h9v.s7.27507332e29e from=translated src=- shape=dd3c0132 vocab=f5dcd0a2
-/
theorem iIndepFun_convexifiedDirectionalSupportDeviation
    {Ω Z E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure Ω} (X : ι → Ω → Z)
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    (L : Set E) (u : E) :
    ProbabilityTheory.iIndepFun
      (directionalSupportDeviation
        (fun i ω => closedConvexHull ℝ (F (X i ω))) L u) μ := by
  have hsupp : Measurable
      (fun z => supportFunction (closedConvexHull ℝ (F z)) u) :=
    measurable_supportFunction_closedConvexHull_of_effros
      hF hFcompact hFne u
  have hcomp := hindep.comp
    (fun _ z => supportFunction (closedConvexHull ℝ (F z)) u -
      supportFunction L u)
    (fun _ => hsupp.sub_const (supportFunction L u))
  change ProbabilityTheory.iIndepFun (fun i ω =>
    supportFunction (closedConvexHull ℝ (F (X i ω))) u - supportFunction L u) μ
  simpa only [Function.comp_def] using hcomp

/-- Identical distribution and the population support identity center every
convexified directional deviation.
@isnad1 id=eq.6h9v.s8.2c914ba5d648 from=translated src=- shape=908e9e2f vocab=16db127d
-/
theorem integral_convexifiedDirectionalSupportDeviation_eq_zero
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    (L : Set E) (u : E)
    (hbaseInt : Integrable (fun ω => supportFunction (F (X 0 ω)) u) μ)
    (hLsupport : supportFunction L u =
      ∫ ω, supportFunction (F (X 0 ω)) u ∂μ)
    (i : ℕ) :
    μ[directionalSupportDeviation
      (fun j ω => closedConvexHull ℝ (F (X j ω))) L u i] = 0 := by
  have hsupp : Measurable
      (fun z => supportFunction (closedConvexHull ℝ (F z)) u) :=
    measurable_supportFunction_closedConvexHull_of_effros
      hF hFcompact hFne u
  have hid : IdentDistrib
      (fun ω => supportFunction (closedConvexHull ℝ (F (X i ω))) u)
      (fun ω => supportFunction (closedConvexHull ℝ (F (X 0 ω))) u) μ μ :=
    (hident i).comp hsupp
  have hbaseHullInt : Integrable
      (fun ω => supportFunction (closedConvexHull ℝ (F (X 0 ω))) u) μ := by
    apply hbaseInt.congr
    filter_upwards [] with ω
    exact (supportFunction_closedConvexHull
      (hFcompact (X 0 ω)) (hFne (X 0 ω)) u).symm
  have hiInt : Integrable
      (fun ω => supportFunction (closedConvexHull ℝ (F (X i ω))) u) μ :=
    hid.integrable_iff.mpr hbaseHullInt
  have hbaseIntegral :
      (∫ ω, supportFunction (closedConvexHull ℝ (F (X 0 ω))) u ∂μ) =
        ∫ ω, supportFunction (F (X 0 ω)) u ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact supportFunction_closedConvexHull
      (hFcompact (X 0 ω)) (hFne (X 0 ω)) u
  simp only [directionalSupportDeviation]
  rw [integral_sub hiInt (integrable_const (supportFunction L u))]
  rw [hid.integral_eq, hbaseIntegral, ← hLsupport]
  simp

/-- The population target for iid random-set concentration.-/
def iidAumannTarget
    {Ω Z E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (X₀ : Ω → Z) (F : Z → Set E) : Set E :=
  closedConvexHull ℝ
    (closure (aumannExpectation μ (fun ω => F (X₀ ω))))

/-- Finite-net Hoeffding concentration for bounded iid random compact sets.
All independence, measurability, boundedness, and centering hypotheses of
`hausdorffDist_minkowskiAverage_risk_bound_of_hoeffding` are derived inside
the proof.
@isnad1 id=le.12h11v.s9.9bc2917d0904 from=translated src=- shape=2cf30d35 vocab=e4e2f43a
-/
theorem hausdorffDist_convexified_iid_risk_bound_of_hoeffding
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
    {R : ℝ}
    (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ R)
    {n : ℕ} (hn : 0 < n) {eps t : ℝ}
    (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (N : Finset E) (hN : ∀ v ∈ N, ‖v‖ ≤ 1)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps) :
    μ.real {ω | t + (R + R) * eps <
        hausdorffDist
          (closedConvexHull ℝ
            (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
          (iidAumannTarget μ (X 0) F)} ≤
      N.card * symmetricSupportHoeffdingTail n t (R + R) := by
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
  have hS₀dom : ∀ ω, ∀ x ∈ S₀ ω, ‖x‖ ≤ R := fun ω =>
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
  have hLbound : ∀ x ∈ L, ‖x‖ ≤ R := by
    have hAsub : A ⊆ Metric.closedBall (0 : E) R := by
      intro x hx
      have hxR := norm_le_integral_envelope_of_mem_closure_aumannExpectation
        hg (Filter.Eventually.of_forall hS₀dom) hx
      have hxR' : ‖x‖ ≤ R := by simpa using hxR
      simpa [Metric.mem_closedBall, dist_zero_right] using hxR'
    have hLsub : L ⊆ Metric.closedBall (0 : E) R :=
      closedConvexHull_min hAsub (convex_closedBall (0 : E) R)
        Metric.isClosed_closedBall
    intro x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hLsub hx
  have hHullCompact : ∀ i ω,
      IsCompact (closedConvexHull ℝ (F (X i ω))) := fun i ω =>
    closedConvexHull_compact (hFcompact (X i ω))
  have hHullNe : ∀ i ω,
      (closedConvexHull ℝ (F (X i ω))).Nonempty := fun i ω =>
    (hFne (X i ω)).mono subset_closedConvexHull
  have hHullBound : ∀ i ω, ∀ x ∈ closedConvexHull ℝ (F (X i ω)),
      ‖x‖ ≤ R := by
    intro i ω
    have hsub : closedConvexHull ℝ (F (X i ω)) ⊆
        Metric.closedBall (0 : E) R := by
      apply closedConvexHull_min
      · intro x hx
        simpa [Metric.mem_closedBall, dist_zero_right] using
          hFbound (X i ω) x hx
      · exact convex_closedBall (0 : E) R
      · exact Metric.isClosed_closedBall
    intro x hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hsub hx
  have hbaseInt : ∀ u : E,
      Integrable (fun ω => supportFunction (F (X 0 ω)) u) μ := fun u =>
    integrable_supportFunction_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom u
  have hLsupport : ∀ u : E,
      supportFunction L u =
        ∫ ω, supportFunction (F (X 0 ω)) u ∂μ := by
    intro u
    rw [supportFunction_closedConvexHull hAcompact hAne]
    exact supportFunction_closure_aumannExpectation_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom hAcompact u
  have hbound := hausdorffDist_minkowskiAverage_risk_bound_of_hoeffding
    (μ := μ)
    (S := fun i ω => closedConvexHull ℝ (F (X i ω)))
    (L := L) (Finset.range n) (Finset.nonempty_range_iff.mpr hn.ne')
    hHullCompact hHullNe (fun _ _ => convex_closedConvexHull)
    hLcompact hLne hLconv hHullBound hLbound heps ht N hN hnet
    (fun v _hv =>
      iIndepFun_convexifiedDirectionalSupportDeviation
        X hindep F hF hFcompact hFne L v)
    (fun v _hv i =>
      (measurable_convexifiedDirectionalSupportDeviation
        X hX F hF hFcompact hFne L v i).aemeasurable)
    (fun v _hv i =>
      integral_convexifiedDirectionalSupportDeviation_eq_zero
        X hident F hF hFcompact hFne L v (hbaseInt v) (hLsupport v) i)
  have hEvent :
      {ω | t + (R + R) * eps <
        hausdorffDist
          (closedConvexHull ℝ
            (minkowskiAverage (Finset.range n) (fun i => F (X i ω)))) L} =
      {ω | t + (R + R) * eps <
        hausdorffDist
          (minkowskiAverage (Finset.range n)
            (fun i => closedConvexHull ℝ (F (X i ω)))) L} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [closedConvexHull_minkowskiAverage (Finset.range n)
      (fun i => F (X i ω))
      (fun i _ => hFcompact (X i ω))
      (fun i _ => hFne (X i ω))]
  change μ.real {ω | t + (R + R) * eps <
      hausdorffDist
        (closedConvexHull ℝ
          (minkowskiAverage (Finset.range n) (fun i => F (X i ω)))) L} ≤ _
  rw [hEvent]
  simpa only [Finset.card_range] using hbound

/-- Closed-form version of iid convexified concentration.
@isnad1 id=le.13h11v.s9.4d9028d90f04 from=translated src=- shape=d1fdc9e7 vocab=66053f26
-/
theorem hausdorffDist_convexified_iid_risk_bound_standard
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
    {R : ℝ} (hR : 0 < R)
    (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ R)
    {n : ℕ} (hn : 0 < n) {eps t : ℝ}
    (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (N : Finset E) (hN : ∀ v ∈ N, ‖v‖ ≤ 1)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps) :
    μ.real {ω | t + (R + R) * eps <
        hausdorffDist
          (closedConvexHull ℝ
            (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
          (iidAumannTarget μ (X 0) F)} ≤
      N.card * (2 * exp (-(n : ℝ) * t ^ 2 /
        (2 * (R + R) ^ 2))) := by
  have hbound := hausdorffDist_convexified_iid_risk_bound_of_hoeffding
    (μ := μ) X hX hindep hident F hF hFcompact hFne hFbound
    hn heps ht N hN hnet
  rw [symmetricSupportHoeffdingTail_eq hn t (by linarith : 0 < R + R)] at hbound
  exact hbound

/-- Automatic finite-net version of bounded iid concentration.  A suitable
net of the unit ball is chosen internally at every positive scale.
@isnad1 id=ex.10h10v.s9.ea8b8abe1dd5 from=translated src=- shape=05bca334 vocab=e4e2f43a
-/
theorem exists_finset_hausdorffDist_convexified_iid_risk_bound_of_hoeffding
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
    {R : ℝ} (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ R)
    {n : ℕ} (hn : 0 < n) {eps t : ℝ}
    (heps : 0 < eps) (ht : 0 ≤ t) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps) ∧
      μ.real {ω | t + (R + R) * eps <
          hausdorffDist
            (closedConvexHull ℝ
              (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
            (iidAumannTarget μ (X 0) F)} ≤
        N.card * symmetricSupportHoeffdingTail n t (R + R) := by
  obtain ⟨N, hN, hnet⟩ :=
    exists_finset_unitBall_closedNet_with_centers (E := E) heps
  exact ⟨N, hN, hnet,
    hausdorffDist_convexified_iid_risk_bound_of_hoeffding
      (μ := μ) X hX hindep hident F hF hFcompact hFne hFbound
      hn heps.le ht N hN hnet⟩

/-- Automatic finite-net concentration with the closed-form Hoeffding
exponent.
@isnad1 id=ex.11h10v.s9.0a031cd9e6a0 from=translated src=- shape=d5a390dc vocab=66053f26
-/
theorem exists_finset_hausdorffDist_convexified_iid_risk_bound_standard
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
    {R : ℝ} (hR : 0 < R)
    (hFbound : ∀ z, ∀ x ∈ F z, ‖x‖ ≤ R)
    {n : ℕ} (hn : 0 < n) {eps t : ℝ}
    (heps : 0 < eps) (ht : 0 ≤ t) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps) ∧
      μ.real {ω | t + (R + R) * eps <
          hausdorffDist
            (closedConvexHull ℝ
              (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
            (iidAumannTarget μ (X 0) F)} ≤
        N.card * (2 * exp (-(n : ℝ) * t ^ 2 /
          (2 * (R + R) ^ 2))) := by
  obtain ⟨N, hN, hnet⟩ :=
    exists_finset_unitBall_closedNet_with_centers (E := E) heps
  exact ⟨N, hN, hnet,
    hausdorffDist_convexified_iid_risk_bound_standard
      (μ := μ) X hX hindep hident F hF hFcompact hFne hR hFbound
      hn heps.le ht N hN hnet⟩

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
