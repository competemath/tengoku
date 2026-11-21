/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannHausdorff
import Tengoku.Randomsettheory.RandomSetTheory.AumannConvexification
import Tengoku.Randomsettheory.RandomSetTheory.EffrosCaratheodory
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableHausdorff
import Tengoku.Randomsettheory.RandomSetTheory.ZeroSetTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hausdorff continuity of parameterized Aumann expectations

This file connects the parameter regularity of a Carathéodory moment map to
the topology of its population correspondence.  If the moment map is
pointwise Lipschitz in the parameter with an integrable random Lipschitz
coefficient, then the closed Aumann expectation of its fibrewise closed
convex hull is Lipschitz in Hausdorff distance.  In particular it is
Hausdorff continuous, so the zero-set topology results apply automatically.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- Fibrewise Carathéodory image at a fixed parameter.-/
def caratheodoryImageAt
    {Ω Θ X E : Type*} (S : Ω → Set X) (φ : (Ω × Θ) × X → E)
    (θ : Θ) (ω : Ω) : Set E :=
  (fun x => φ ((ω, θ), x)) '' S ω

/-- Closed convexified population correspondence associated with a
parameterized Carathéodory image.-/
def convexifiedAumannExpectationParam
    {Ω Θ X E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (S : Ω → Set X) (φ : (Ω × Θ) × X → E)
    (θ : Θ) : Set E :=
  closure (aumannExpectation μ (fun ω =>
    closedConvexHull ℝ (caratheodoryImageAt S φ θ ω)))

/-- Pairing the same source point in two parameter images gives the basic
Hausdorff Lipschitz bound.
@isnad1 id=le.2h10v.s7.ea50d3eb7ec4 from=translated src=- shape=81a67d59 vocab=dca46007
-/
theorem hausdorffDist_caratheodoryImageAt_le
    {Ω Θ X E : Type*} [PseudoMetricSpace Θ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Ω → Set X) (φ : (Ω × Θ) × X → E)
    (L : Ω → ℝ) (hL : ∀ ω, 0 ≤ L ω)
    (hφLip : ∀ ω θ η x, x ∈ S ω →
      ‖φ ((ω, θ), x) - φ ((ω, η), x)‖ ≤ L ω * dist θ η)
    (ω : Ω) (θ η : Θ) :
    hausdorffDist (caratheodoryImageAt S φ θ ω)
        (caratheodoryImageAt S φ η ω) ≤ L ω * dist θ η := by
  apply hausdorffDist_le_of_mem_dist (mul_nonneg (hL ω) dist_nonneg)
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨φ ((ω, η), x), ⟨x, hx, rfl⟩, ?_⟩
    simpa [dist_eq_norm] using hφLip ω θ η x hx
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨φ ((ω, θ), x), ⟨x, hx, rfl⟩, ?_⟩
    simpa [dist_eq_norm, dist_comm] using hφLip ω η θ x hx

/-- Closed convexification preserves the preceding parameter bound.
@isnad1 id=le.5h10v.s8.0b865d370556 from=translated src=- shape=ffa572d1 vocab=9c0c2fef
-/
theorem hausdorffDist_closedConvexHull_caratheodoryImageAt_le
    {Ω Θ X E : Type*} [PseudoMetricSpace Θ]
    [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Ω → Set X) (φ : (Ω × Θ) × X → E)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    (L : Ω → ℝ) (hL : ∀ ω, 0 ≤ L ω)
    (hφLip : ∀ ω θ η x, x ∈ S ω →
      ‖φ ((ω, θ), x) - φ ((ω, η), x)‖ ≤ L ω * dist θ η)
    (ω : Ω) (θ η : Θ) :
    hausdorffDist
        (closedConvexHull ℝ (caratheodoryImageAt S φ θ ω))
        (closedConvexHull ℝ (caratheodoryImageAt S φ η ω)) ≤
      L ω * dist θ η := by
  have hθcompact : IsCompact (caratheodoryImageAt S φ θ ω) :=
    (hScompact ω).image (hφcont (ω, θ))
  have hηcompact : IsCompact (caratheodoryImageAt S φ η ω) :=
    (hScompact ω).image (hφcont (ω, η))
  have hθne : (caratheodoryImageAt S φ θ ω).Nonempty :=
    (hSne ω).image _
  have hηne : (caratheodoryImageAt S φ η ω).Nonempty :=
    (hSne ω).image _
  exact (hausdorffDist_closedConvexHull_le hθcompact hηcompact hθne hηne).trans
    (hausdorffDist_caratheodoryImageAt_le S φ L hL hφLip ω θ η)

/-- **Parameterized Aumann Lipschitz theorem.**  An integrable pointwise
Lipschitz coefficient for the moment map integrates to a deterministic
Hausdorff Lipschitz coefficient for the closed convexified Aumann population.

The common envelope is used only to make the closed Aumann expectations
compact and their support functions integrable.
@isnad1 id=le.10h11v.s9.70cc279577aa from=translated src=- shape=203d4f42 vocab=8acd1375
-/
theorem hausdorffDist_convexifiedAumannExpectationParam_le
    {Ω Θ X E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (S : Ω → Set X) (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (φ : (Ω × Θ) × X → E) (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    (L : Ω → ℝ) (hLint : Integrable L μ) (hL : ∀ ω, 0 ≤ L ω)
    (hφLip : ∀ ω θ η x, x ∈ S ω →
      ‖φ ((ω, θ), x) - φ ((ω, η), x)‖ ≤ L ω * dist θ η)
    (g : Ω → ℝ) (hg : Integrable g μ)
    (hdom : ∀ ω θ x, x ∈ S ω → ‖φ ((ω, θ), x)‖ ≤ g ω)
    (θ η : Θ) :
    hausdorffDist
        (convexifiedAumannExpectationParam μ S φ θ)
        (convexifiedAumannExpectationParam μ S φ η) ≤
      (∫ ω, L ω ∂μ) * dist θ η := by
  let I : Θ → Ω → Set E := fun ξ ω => caratheodoryImageAt S φ ξ ω
  let C : Θ → Ω → Set E := fun ξ ω => closedConvexHull ℝ (I ξ ω)
  have hφfixed_meas : ∀ ξ : Θ,
      Measurable (fun p : Ω × X => φ ((p.1, ξ), p.2)) := by
    intro ξ
    exact hφmeas.comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hIEffros : ∀ ξ, RandomSet.IsEffrosMeasurable (I ξ) := by
    intro ξ
    exact effrosMeasurable_caratheodoryImage hS
      (fun ω => (hScompact ω).isClosed) hSne
      (hφfixed_meas ξ) (fun ω => hφcont (ω, ξ))
  have hIcompact : ∀ ξ ω, IsCompact (I ξ ω) := by
    intro ξ ω
    exact (hScompact ω).image (hφcont (ω, ξ))
  have hIne : ∀ ξ ω, (I ξ ω).Nonempty := by
    intro ξ ω
    exact (hSne ω).image _
  have hCEffros : ∀ ξ, RandomSet.IsEffrosMeasurable (C ξ) := by
    intro ξ
    exact effrosMeasurable_closedConvexHull_of_compact
      (hIEffros ξ) (hIcompact ξ) (hIne ξ)
  have hCcompact : ∀ ξ ω, IsCompact (C ξ ω) := by
    intro ξ ω
    exact closedConvexHull_compact (hIcompact ξ ω)
  have hCne : ∀ ξ ω, (C ξ ω).Nonempty := by
    intro ξ ω
    exact (hIne ξ ω).mono subset_closedConvexHull
  have hCconv : ∀ ξ ω, Convex ℝ (C ξ ω) :=
    fun _ _ => convex_closedConvexHull
  have hCdom : ∀ ξ ω, ∀ y ∈ C ξ ω, ‖y‖ ≤ g ω := by
    intro ξ ω
    apply norm_le_on_closedConvexHull_of_norm_le
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hdom ω ξ x hx
  have hpoint : ∀ ω,
      hausdorffDist (C θ ω) (C η ω) ≤ L ω * dist θ η := by
    intro ω
    exact hausdorffDist_closedConvexHull_caratheodoryImageAt_le
      S φ hScompact hSne hφcont L hL hφLip ω θ η
  have hdistMeas : Measurable (fun ω => hausdorffDist (C θ ω) (C η ω)) :=
    measurable_hausdorffDist_correspondence
      (hCEffros θ) (hCEffros η)
      (fun ω => (hCcompact θ ω).isClosed)
      (fun ω => (hCcompact η ω).isClosed)
      (hCne θ) (hCne η)
  have hLipInt : Integrable (fun ω => L ω * dist θ η) μ :=
    hLint.mul_const _
  have hdistInt : Integrable (fun ω => hausdorffDist (C θ ω) (C η ω)) μ := by
    apply hLipInt.mono' hdistMeas.aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg hausdorffDist_nonneg,
      abs_of_nonneg (mul_nonneg (hL ω) dist_nonneg)] using hpoint ω
  have hmain :
      hausdorffDist (closure (aumannExpectation μ (C θ)))
          (closure (aumannExpectation μ (C η))) ≤
        (∫ ω, L ω ∂μ) * dist θ η := by
    calc
      hausdorffDist (closure (aumannExpectation μ (C θ)))
          (closure (aumannExpectation μ (C η))) ≤
          ∫ ω, hausdorffDist (C θ ω) (C η ω) ∂μ :=
        hausdorffDist_closure_aumannExpectation_le_integral
          (hCEffros θ) (hCEffros η) (hCcompact θ) (hCcompact η)
          (hCne θ) (hCne η) (hCconv θ) (hCconv η)
          hg hg (hCdom θ) (hCdom η) hdistInt
      _ ≤ ∫ ω, L ω * dist θ η ∂μ :=
        integral_mono hdistInt hLipInt hpoint
      _ = (∫ ω, L ω ∂μ) * dist θ η := integral_mul_const _ _
  simpa [convexifiedAumannExpectationParam, C, I] using hmain

/-- Compactness and nonemptiness of every closed convexified Aumann
population follow automatically from a common integrable envelope.
@isnad1 id=and.7h9v.s8.b24de7973fa7 from=translated src=- shape=ddaca672 vocab=e0b869b8
-/
theorem compact_nonempty_convexifiedAumannExpectationParam
    {Ω Θ X E : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (S : Ω → Set X) (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (φ : (Ω × Θ) × X → E) (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    (g : Ω → ℝ) (hg : Integrable g μ)
    (hdom : ∀ ω θ x, x ∈ S ω → ‖φ ((ω, θ), x)‖ ≤ g ω)
    (θ : Θ) :
    IsCompact (convexifiedAumannExpectationParam μ S φ θ) ∧
      (convexifiedAumannExpectationParam μ S φ θ).Nonempty := by
  let I : Ω → Set E := fun ω => caratheodoryImageAt S φ θ ω
  let C : Ω → Set E := fun ω => closedConvexHull ℝ (I ω)
  have hφfixed : Measurable (fun p : Ω × X => φ ((p.1, θ), p.2)) :=
    hφmeas.comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hIEffros : RandomSet.IsEffrosMeasurable I :=
    effrosMeasurable_caratheodoryImage hS
      (fun ω => (hScompact ω).isClosed) hSne hφfixed
      (fun ω => hφcont (ω, θ))
  have hIcompact : ∀ ω, IsCompact (I ω) := fun ω =>
    (hScompact ω).image (hφcont (ω, θ))
  have hIne : ∀ ω, (I ω).Nonempty := fun ω => (hSne ω).image _
  have hCEffros : RandomSet.IsEffrosMeasurable C :=
    effrosMeasurable_closedConvexHull_of_compact hIEffros hIcompact hIne
  have hCcompact : ∀ ω, IsCompact (C ω) := fun ω =>
    closedConvexHull_compact (hIcompact ω)
  have hCne : ∀ ω, (C ω).Nonempty := fun ω =>
    (hIne ω).mono subset_closedConvexHull
  have hCdom : ∀ ω, ∀ y ∈ C ω, ‖y‖ ≤ g ω := by
    intro ω
    apply norm_le_on_closedConvexHull_of_norm_le
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hdom ω θ x hx
  have hcompactA : IsCompact (closure (aumannExpectation μ C)) :=
    closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall hCdom)
  have hsel : HasIntegrableSupportSelection μ C 0 :=
    hasIntegrableSupportSelection_of_effros_of_envelope
      hCEffros hCcompact hCne hg hCdom 0
  rcases hsel with ⟨f, hf, _⟩
  have hneA : (closure (aumannExpectation μ C)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hf).closure
  simpa [convexifiedAumannExpectationParam, C, I] using
    And.intro hcompactA hneA

/-- The preceding Lipschitz estimate implies Hausdorff continuity of the
whole parameterized population correspondence.
@isnad1 id=hausdorf.10h9v.s8.0cdc13b99492 from=translated src=- shape=ee435c3f vocab=31f40f08
-/
theorem hausdorffContinuous_convexifiedAumannExpectationParam
    {Ω Θ X E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (S : Ω → Set X) (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (φ : (Ω × Θ) × X → E) (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    (L : Ω → ℝ) (hLint : Integrable L μ) (hL : ∀ ω, 0 ≤ L ω)
    (hφLip : ∀ ω θ η x, x ∈ S ω →
      ‖φ ((ω, θ), x) - φ ((ω, η), x)‖ ≤ L ω * dist θ η)
    (g : Ω → ℝ) (hg : Integrable g μ)
    (hdom : ∀ ω θ x, x ∈ S ω → ‖φ ((ω, θ), x)‖ ≤ g ω) :
    HausdorffContinuous (convexifiedAumannExpectationParam μ S φ) := by
  intro θ
  apply squeeze_zero
    (fun _ => hausdorffDist_nonneg)
    (fun η => hausdorffDist_convexifiedAumannExpectationParam_le
      S hS hScompact hSne φ hφmeas hφcont L hLint hL hφLip g hg hdom η θ)
  have hdist : Tendsto (fun η : Θ => dist η θ) (𝓝 θ) (𝓝 0) := by
    simpa using (continuousAt_id.dist (continuousAt_const :
      ContinuousAt (fun _ : Θ => θ) θ))
  simpa [mul_comm] using hdist.const_mul (∫ ω, L ω ∂μ)

/-- Under the parameterized Lipschitz and envelope assumptions, the exact
population zero set is closed.  This is the direct topological conclusion
used by identification arguments.
@isnad1 id=isclosed.10h9v.s8.b9f92f503127 from=translated src=- shape=2892e8b8 vocab=5e4839f5
-/
theorem isClosed_zeroSet_convexifiedAumannExpectationParam
    {Ω Θ X E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (S : Ω → Set X) (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (φ : (Ω × Θ) × X → E) (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    (L : Ω → ℝ) (hLint : Integrable L μ) (hL : ∀ ω, 0 ≤ L ω)
    (hφLip : ∀ ω θ η x, x ∈ S ω →
      ‖φ ((ω, θ), x) - φ ((ω, η), x)‖ ≤ L ω * dist θ η)
    (g : Ω → ℝ) (hg : Integrable g μ)
    (hdom : ∀ ω θ x, x ∈ S ω → ‖φ ((ω, θ), x)‖ ≤ g ω) :
    IsClosed (setValuedZeroSet
      (convexifiedAumannExpectationParam μ S φ)) := by
  have hhaus := hausdorffContinuous_convexifiedAumannExpectationParam
    S hS hScompact hSne φ hφmeas hφcont L hLint hL hφLip g hg hdom
  have hreg : ∀ θ,
      IsCompact (convexifiedAumannExpectationParam μ S φ θ) ∧
        (convexifiedAumannExpectationParam μ S φ θ).Nonempty := fun θ =>
    compact_nonempty_convexifiedAumannExpectationParam
      S hS hScompact hSne φ hφmeas hφcont g hg hdom θ
  exact hhaus.isClosed_setValuedZeroSet_of_compact
    (fun θ => (hreg θ).1) (fun θ => (hreg θ).2)

/-- On a compact parameter space, the exact population zero set is compact
under the same primitive assumptions.
@isnad1 id=iscompac.10h9v.s8.2a14b5c45785 from=translated src=- shape=8c3fbfda vocab=afb2d286
-/
theorem isCompact_zeroSet_convexifiedAumannExpectationParam
    {Ω Θ X E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (S : Ω → Set X) (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty)
    (φ : (Ω × Θ) × X → E) (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    (L : Ω → ℝ) (hLint : Integrable L μ) (hL : ∀ ω, 0 ≤ L ω)
    (hφLip : ∀ ω θ η x, x ∈ S ω →
      ‖φ ((ω, θ), x) - φ ((ω, η), x)‖ ≤ L ω * dist θ η)
    (g : Ω → ℝ) (hg : Integrable g μ)
    (hdom : ∀ ω θ x, x ∈ S ω → ‖φ ((ω, θ), x)‖ ≤ g ω) :
    IsCompact (setValuedZeroSet
      (convexifiedAumannExpectationParam μ S φ)) := by
  exact (isClosed_zeroSet_convexifiedAumannExpectationParam
    S hS hScompact hSne φ hφmeas hφcont L hLint hL hφLip g hg hdom).isCompact

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
