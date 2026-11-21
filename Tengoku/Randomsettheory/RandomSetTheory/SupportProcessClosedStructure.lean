/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.PointwiseRandomSetCLT

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed structural constraints for support-process limits

Support functions vanish at the zero direction and are positively homogeneous.
The same is true for scaled differences of support functions.  This file shows
that these two constraints define a closed subset of the continuous-path
space on the closed unit ball.  Portmanteau then implies that every weak limit
of structured support paths has the same structure almost surely.

This supplies the closed-structure step needed to rewrite the three limits in
the pointwise random-set CLT as suprema over the unit sphere.
-/

open Filter MeasureTheory Metric ProbabilityTheory Set Topology
open scoped InnerProductSpace ProbabilityTheory Topology

noncomputable section

namespace RandomSetTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Continuous paths satisfying the two structural identities inherited from
differences of support functions.-/
def structuredSupportProcessSet :
    Set C(Metric.closedBall (0 : E) 1, ℝ) :=
  {f | f (closedUnitBallZero (E := E)) = 0 ∧
    PositivelyHomogeneousOnClosedUnitBall f}

omit [FiniteDimensional ℝ E] in
/-- The structural support-process constraints are closed for uniform
convergence of continuous paths.
@isnad1 id=isclosed.0h1v.s7.ae2a919d6906 from=translated src=- shape=aa10c48a vocab=32bcbeeb
-/
theorem isClosed_structuredSupportProcessSet :
    IsClosed (structuredSupportProcessSet (E := E)) := by
  change IsClosed
    ({f : C(Metric.closedBall (0 : E) 1, ℝ) |
        f (closedUnitBallZero (E := E)) = 0} ∩
      {f : C(Metric.closedBall (0 : E) 1, ℝ) |
        PositivelyHomogeneousOnClosedUnitBall f})
  apply IsClosed.inter
  · exact isClosed_eq
      (continuous_eval_const (closedUnitBallZero (E := E))) continuous_const
  · simp only [PositivelyHomogeneousOnClosedUnitBall, Set.ofPred_forall]
    refine isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_iInter fun r ↦ isClosed_iInter fun _hr ↦
        isClosed_iInter fun _hxy ↦ ?_
    exact isClosed_eq (continuous_eval_const y)
      ((continuous_const : Continuous
        (fun _ : C(Metric.closedBall (0 : E) 1, ℝ) ↦ r)).mul
          (continuous_eval_const x))

omit [FiniteDimensional ℝ E] in
/-- A scaled difference of support functions vanishes at the zero direction.
@isnad1 id=eq.4h4v.s8.37ccd4f1154f from=translated src=- shape=62639145 vocab=e89a5ed8
-/
@[simp]
theorem scaledSupportDifferenceContinuousMap_zero
    (c : ℝ) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    scaledSupportDifferenceContinuousMap c K L hK hL hKne hLne
        (closedUnitBallZero (E := E)) = 0 := by
  rw [scaledSupportDifferenceContinuousMap_apply]
  change c * (supportFunction K (0 : E) - supportFunction L (0 : E)) = 0
  rw [supportFunction_zero hK hKne, supportFunction_zero hL hLne]
  ring

omit [FiniteDimensional ℝ E] in
/-- A scaled difference of support functions is positively homogeneous on
the closed unit ball.
@isnad1 id=positive.4h4v.s6.2dd284167d33 from=translated src=- shape=b2703b83 vocab=ce32c019
-/
theorem scaledSupportDifferenceContinuousMap_positivelyHomogeneous
    (c : ℝ) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    PositivelyHomogeneousOnClosedUnitBall
      (scaledSupportDifferenceContinuousMap c K L hK hL hKne hLne) := by
  intro x y r hr hxy
  simp only [scaledSupportDifferenceContinuousMap_apply]
  rw [hxy, supportFunction_smul_direction hK hKne hr,
    supportFunction_smul_direction hL hLne hr]
  ring

omit [FiniteDimensional ℝ E] in
/-- Every scaled support-difference path belongs to the closed structural
class.
@isnad1 id=mem.4h4v.s8.fc03ec996bd3 from=translated src=- shape=a8f41ddb vocab=6aa2ac73
-/
theorem scaledSupportDifferenceContinuousMap_mem_structured
    (c : ℝ) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    scaledSupportDifferenceContinuousMap c K L hK hL hKne hLne ∈
      structuredSupportProcessSet (E := E) :=
  ⟨scaledSupportDifferenceContinuousMap_zero c K L hK hL hKne hLne,
    scaledSupportDifferenceContinuousMap_positivelyHomogeneous
      c K L hK hL hKne hLne⟩

/-- Portmanteau preserves any closed path constraint which holds pointwise
for every member of the approximating family.
@isnad1 id=eventual.3h12v.s7.918fb5c33aec from=translated src=- shape=4db55891 vocab=a17f86cd
-/
theorem TendstoInDistribution.ae_mem_closed_of_forall_mem
    {I Ω' F : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Ω'} {mu' : Measure Ω'}
    [IsProbabilityMeasure mu']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    [HasOuterApproxClosed F]
    {X : (i : I) → Omega i → F} {Z : Ω' → F} {l : Filter I}
    [l.NeBot]
    (h : TendstoInDistribution X l Z mu mu')
    {S : Set F} (hS : IsClosed S)
    (hmem : ∀ i ω, X i ω ∈ S) :
    ∀ᵐ ω ∂mu', Z ω ∈ S := by
  have hport :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hS
  have hmass : ∀ i,
      ((⟨(mu i).map (X i),
          Measure.isProbabilityMeasure_map (h.forall_aemeasurable i)⟩ :
        ProbabilityMeasure F) : Measure F) S = 1 := by
    intro i
    rw [Measure.map_apply_of_aemeasurable
      (h.forall_aemeasurable i) hS.measurableSet]
    have hpre : X i ⁻¹' S = Set.univ := by
      exact Set.eq_univ_of_forall fun ω ↦ hmem i ω
    rw [hpre, measure_univ]
  have hport' :
      l.limsup (fun _ : I ↦ (1 : ENNReal)) ≤ (mu'.map Z) S := by
    have hfun :
        (fun i ↦
          ((⟨(mu i).map (X i),
              Measure.isProbabilityMeasure_map (h.forall_aemeasurable i)⟩ :
            ProbabilityMeasure F) : Measure F) S) =
          (fun _ : I ↦ (1 : ENNReal)) := by
      funext i
      exact hmass i
    calc
      l.limsup (fun _ : I ↦ (1 : ENNReal)) =
          l.limsup (fun i ↦
            ((⟨(mu i).map (X i),
                Measure.isProbabilityMeasure_map (h.forall_aemeasurable i)⟩ :
              ProbabilityMeasure F) : Measure F) S) :=
        congrArg (fun f : I → ENNReal ↦ l.limsup f) hfun.symm
      _ ≤ (mu'.map Z) S := by
        simpa only [ProbabilityMeasure.coe_mk] using hport
  have hone : (mu'.map Z) S = 1 := by
    apply le_antisymm prob_le_one
    simpa only [Filter.limsup_const] using hport'
  rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit
    hS.measurableSet] at hone
  have hpre : NullMeasurableSet (Z ⁻¹' S) mu' :=
    h.aemeasurable_limit.nullMeasurableSet_preimage hS.measurableSet
  have hae : ∀ᵐ ω ∂mu', ω ∈ Z ⁻¹' S :=
    (ae_mem_iff_measure_eq hpre).2
      (by simpa only [measure_univ] using hone)
  simpa only [Set.mem_preimage] using hae

/-- A weak limit of scaled support-difference paths vanishes at zero and is
positively homogeneous almost surely.
@isnad1 id=eventual.5h13v.s10.ca3a0399811c from=translated src=- shape=d9961f14 vocab=06f9d645
-/
theorem TendstoInDistribution.ae_structuredSupportProcess_of_supportDifferences
    {I Ω' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Ω'} {mu' : Measure Ω'}
    [IsProbabilityMeasure mu']
    [MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Omega i → Set E) (L : Set E)
    (Z : Ω' → C(Metric.closedBall (0 : E) 1, ℝ))
    (hKcompact : ∀ i ω, IsCompact (K i ω))
    (hKne : ∀ i ω, (K i ω).Nonempty)
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    {l : Filter I} [l.NeBot]
    (hprocess : TendstoInDistribution
      (fun i ω ↦ scaledSupportDifferenceContinuousMap
        (c i) (K i ω) L (hKcompact i ω) hLcompact
          (hKne i ω) hLne)
      l Z mu mu') :
    ∀ᵐ ω ∂mu',
      Z ω (closedUnitBallZero (E := E)) = 0 ∧
        PositivelyHomogeneousOnClosedUnitBall (Z ω) := by
  exact RandomSetTheory.TendstoInDistribution.ae_mem_closed_of_forall_mem
    hprocess
    isClosed_structuredSupportProcessSet
    (fun i ω ↦ scaledSupportDifferenceContinuousMap_mem_structured
      (c i) (K i ω) L (hKcompact i ω) hLcompact
        (hKne i ω) hLne)

/-- Sphere form of the pointwise random-set continuous-mapping theorem with
no separate structural assumptions on the limiting process.  Closedness and
Portmanteau derive those assumptions almost surely from the approximating
support-difference paths themselves.
@isnad1 id=and.8h13v.s10.149b68fbc50a from=translated src=- shape=bef1be06 vocab=2ce1883f
-/
theorem pointwiseRandomSetCLT_of_supportProcess_unitSphere_of_weakLimit
    [Nontrivial E]
    {I Ω' : Type*} {Omega : I → Type*}
    {mOmega : ∀ i, MeasurableSpace (Omega i)}
    {mu : ∀ i, Measure (Omega i)} [∀ i, IsProbabilityMeasure (mu i)]
    {mOmega' : MeasurableSpace Ω'} {mu' : Measure Ω'}
    [IsProbabilityMeasure mu']
    [MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    (c : I → ℝ) (K : (i : I) → Omega i → Set E) (L : Set E)
    (Z : Ω' → C(Metric.closedBall (0 : E) 1, ℝ))
    (hc : ∀ i, 0 ≤ c i)
    (hKcompact : ∀ i ω, IsCompact (K i ω))
    (hKne : ∀ i ω, (K i ω).Nonempty)
    (hKconv : ∀ i ω, Convex ℝ (K i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty)
    (hLconv : Convex ℝ L)
    {l : Filter I} [l.NeBot]
    (hprocess : TendstoInDistribution
      (fun i ω ↦ scaledSupportDifferenceContinuousMap
        (c i) (K i ω) L (hKcompact i ω) hLcompact
          (hKne i ω) hLne)
      l Z mu mu') :
    TendstoInDistribution
        (fun i ω ↦ |c i| * hausdorffDist (K i ω) L)
        l (fun ω ↦ unitSphereSupAbs (Z ω)) mu mu' ∧
      TendstoInDistribution
        (fun i ω ↦ c i * directedHausdorffDist (K i ω) L)
        l (fun ω ↦ unitSphereSupPositivePart (Z ω)) mu mu' ∧
      TendstoInDistribution
        (fun i ω ↦ c i * directedHausdorffDist L (K i ω))
        l (fun ω ↦ unitSphereSupNegativePart (Z ω)) mu mu' := by
  have hstructure : ∀ᵐ ω ∂mu',
      Z ω (closedUnitBallZero (E := E)) = 0 ∧
        PositivelyHomogeneousOnClosedUnitBall (Z ω) :=
    RandomSetTheory.TendstoInDistribution.ae_structuredSupportProcess_of_supportDifferences
      c K L Z hKcompact hKne hLcompact hLne hprocess
  obtain ⟨hsymmetric, hforward, hreverse⟩ :=
    pointwiseRandomSetCLT_of_supportProcess
      c K L Z hc hKcompact hKne hKconv hLcompact hLne hLconv hprocess
  refine ⟨?_, ?_, ?_⟩
  · apply hsymmetric.congr
    · exact fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl
    · filter_upwards [hstructure] with ω hω
      exact norm_eq_unitSphereSupAbs (Z ω) hω.1 hω.2
  · apply hforward.congr
    · exact fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl
    · filter_upwards [hstructure] with ω hω
      exact continuousSup_eq_unitSphereSupPositivePart (Z ω) hω.1 hω.2
  · apply hreverse.congr
    · exact fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl
    · filter_upwards [hstructure] with ω hω
      exact continuousSup_neg_eq_unitSphereSupNegativePart (Z ω) hω.1 hω.2

end RandomSetTheory
