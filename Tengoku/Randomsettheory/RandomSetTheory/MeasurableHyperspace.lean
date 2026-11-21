/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CapacityFunctional
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableHausdorff
import Tengoku.Randomsettheory.RandomSetTheory.RadstromEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Effros correspondences as measurable hyperspace-valued maps

For a second-countable metric space `X`, a nonempty compact-valued Effros
correspondence can be bundled as a measurable map with values in
`TopologicalSpace.NonemptyCompacts X`, endowed with its Borel sigma-algebra.
The topology on this hyperspace is the Vietoris topology; Mathlib's metric on
it is exactly the Hausdorff metric.

The nontrivial direction is the upper Vietoris event `{K | K ⊆ U}`.  Its
complement is the event that `K` hits the closed set `Uᶜ`.  For compact-valued
correspondences, closed hitting events are countable intersections of open
hitting events, and hence are Effros measurable.  A countable basis of `X`
then induces a countable Vietoris basis on `NonemptyCompacts X`.

No measurable structure is installed globally on `NonemptyCompacts X` in
this file.  This is deliberate: Mathlib leaves the measurable structure of a
general topological type to the user.  The theorems assume an existing
`MeasurableSpace` and `BorelSpace` instance; callers can obtain the canonical
choice locally with `borelize (NonemptyCompacts X)`.

For finite-dimensional real inner-product spaces we also bundle convex
values in `CompactConvexSet E` and prove measurability after the Rådström
support-function embedding.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

variable {Ω X : Type*}

/-! ## Closed hitting events for compact-valued correspondences -/

/-- A compact set hits a closed set iff it hits every positive rational-scale
open thickening of that closed set.
@isnad1 id=eq.2h4v.s6.687ef0072043 from=translated src=- shape=7a149a84 vocab=2b60b513
-/
theorem hitEvent_closed_eq_iInter_thickening_of_compact_values
    [MetricSpace X] {S : Ω → Set X} (hScompact : ∀ ω, IsCompact (S ω))
    {F : Set X} (hF : IsClosed F) :
    hitEvent S F =
      ⋂ n : ℕ, hitEvent S (Metric.thickening (1 / (n + 1 : ℝ)) F) := by
  ext ω
  simp only [Set.mem_iInter, mem_hitEvent]
  constructor
  · rintro ⟨x, hxS, hxF⟩ n
    refine ⟨x, hxS, ?_⟩
    exact Metric.self_subset_thickening
      (by positivity : 0 < 1 / (n + 1 : ℝ)) F hxF
  · intro hhit
    by_contra hnot
    have hdisj : Disjoint (S ω) F := by
      rw [Set.disjoint_left]
      intro x hxS hxF
      exact hnot ⟨x, hxS, hxF⟩
    obtain ⟨δ, hδ, hthick⟩ :=
      hdisj.exists_thickenings (hScompact ω) hF
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    rcases hhit n with ⟨x, hxS, hxF⟩
    exact Set.disjoint_left.mp hthick
      (Metric.self_subset_thickening hδ (S ω) hxS)
      (Metric.thickening_mono hn.le F hxF)

/-- Closed hitting events are measurable for compact-valued Effros
correspondences.
@isnad1 id=measurab.3h4v.s6.6849de417e7d from=translated src=- shape=837300ec vocab=2ac238de
-/
theorem measurableSet_hitEvent_closed_of_compact_values
    [MeasurableSpace Ω] [MetricSpace X] {S : Ω → Set X}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) {F : Set X} (hF : IsClosed F) :
    MeasurableSet (hitEvent S F) := by
  rw [hitEvent_closed_eq_iInter_thickening_of_compact_values hScompact hF]
  exact MeasurableSet.iInter fun n =>
    measurableSet_hitEvent_open hS Metric.isOpen_thickening

/-- For compact-valued Effros correspondences, containment in a deterministic
open set is a measurable event.
@isnad1 id=measurab.3h4v.s6.be32aa99f3a0 from=translated src=- shape=2f7918ff vocab=2141c88a
-/
theorem measurableSet_subset_open_of_effros_of_compact_values
    [MeasurableSpace Ω] [MetricSpace X] {S : Ω → Set X}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) {U : Set X} (hU : IsOpen U) :
    MeasurableSet {ω | S ω ⊆ U} := by
  have hEq : {ω | S ω ⊆ U} = (hitEvent S Uᶜ)ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, mem_hitEvent]
    constructor
    · intro h hhit
      rcases hhit with ⟨x, hxS, hxUc⟩
      exact hxUc (h hxS)
    · intro h x hxS
      by_contra hxU
      exact h ⟨x, hxS, hxU⟩
  rw [hEq]
  exact (measurableSet_hitEvent_closed_of_compact_values
    hS hScompact hU.isClosed_compl).compl

/-! ## Bundling in the Hausdorff/Vietoris hyperspace -/

/-- Bundle pointwise nonempty compact values as a map into Mathlib's
Hausdorff/Vietoris hyperspace.-/
def bundleNonemptyCompacts [TopologicalSpace X] (S : Ω → Set X)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty) :
    Ω → NonemptyCompacts X :=
  fun ω => ⟨⟨S ω, hScompact ω⟩, hSne ω⟩

/--
@isnad1 id=eq.2h4v.s5.16edac5b2ebe from=translated src=- shape=80716365 vocab=d720b12e
-/
@[simp]
theorem coe_bundleNonemptyCompacts [TopologicalSpace X] (S : Ω → Set X)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (ω : Ω) :
    (bundleNonemptyCompacts S hScompact hSne ω : Set X) = S ω :=
  rfl

/-- The inverse image of a basic Vietoris neighborhood is measurable for the
bundled compact-valued Effros correspondence.-/
private theorem measurableSet_preimage_vietorisBasic
    [MeasurableSpace Ω] [MetricSpace X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    {u : Set (Set X)} (huFinite : u.Finite)
    (huOpen : ∀ U ∈ u, IsOpen U) :
    MeasurableSet
      (bundleNonemptyCompacts S hScompact hSne ⁻¹'
        {K : NonemptyCompacts X |
          (K : Set X) ⊆ ⋃₀ u ∧ ∀ U ∈ u, ((K : Set X) ∩ U).Nonempty}) := by
  have hUnionOpen : IsOpen (⋃₀ u) :=
    isOpen_sUnion fun U hU => huOpen U hU
  have hUpper : MeasurableSet {ω | S ω ⊆ ⋃₀ u} :=
    measurableSet_subset_open_of_effros_of_compact_values
      hS hScompact hUnionOpen
  letI := huFinite.to_subtype
  have hLower : MeasurableSet (⋂ U : u, hitEvent S (U : Set X)) :=
    MeasurableSet.iInter fun U =>
      measurableSet_hitEvent_open hS (huOpen U U.property)
  have hEq :
      bundleNonemptyCompacts S hScompact hSne ⁻¹'
          {K : NonemptyCompacts X |
            (K : Set X) ⊆ ⋃₀ u ∧ ∀ U ∈ u, ((K : Set X) ∩ U).Nonempty} =
        {ω | S ω ⊆ ⋃₀ u} ∩ ⋂ U : u, hitEvent S (U : Set X) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, coe_bundleNonemptyCompacts,
      Set.mem_inter_iff, Set.mem_iInter, mem_hitEvent]
    exact and_congr_right fun _ => by
      constructor
      · intro h U
        exact h U U.property
      · intro h U hU
        exact h ⟨U, hU⟩
  rw [hEq]
  exact hUpper.inter hLower

/-- A nonempty compact-valued Effros correspondence is a Borel-measurable
map into `NonemptyCompacts X` equipped with the Vietoris/Hausdorff topology.

The second-countability assumption is exactly what lets us pass from
measurability of finite Vietoris basic events to arbitrary Borel sets using a
countable basis.
@isnad1 id=measurab.3h3v.s6.591a02ee73a2 from=translated src=- shape=69f3708c vocab=552e59d4
-/
theorem measurable_bundleNonemptyCompacts
    [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)] [BorelSpace (NonemptyCompacts X)]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty) :
    Measurable (bundleNonemptyCompacts S hScompact hSne) := by
  obtain ⟨B, hBcountable, _hBempty, hBbasis⟩ :=
    TopologicalSpace.exists_countable_basis X
  let D : Set (Set (Set X)) :=
    {u | u.Finite ∧ u.Nonempty ∧ u ⊆ B}
  let basic : Set (Set X) → Set (NonemptyCompacts X) :=
    fun u => {K | (K : Set X) ⊆ ⋃₀ u ∧
      ∀ U ∈ u, ((K : Set X) ∩ U).Nonempty}
  let C : Set (Set (NonemptyCompacts X)) := basic '' D
  have hDcountable : D.Countable := by
    apply (Set.countable_ofPred_finite_subset hBcountable).mono
    intro u hu
    exact ⟨hu.1, hu.2.2⟩
  have hCcountable : C.Countable := hDcountable.image basic
  have hCbasis : IsTopologicalBasis C := by
    simpa only [C, D, basic] using hBbasis.nonemptyCompacts
  apply measurable_of_isOpen
  intro V hV
  obtain ⟨A, hAC, hVA⟩ := hCbasis.open_eq_sUnion hV
  have hAcountable : A.Countable := hCcountable.mono hAC
  letI := hAcountable.to_subtype
  have hPreimage :
      bundleNonemptyCompacts S hScompact hSne ⁻¹' ⋃₀ A =
        ⋃ W : A,
          bundleNonemptyCompacts S hScompact hSne ⁻¹' (W : Set (NonemptyCompacts X)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_sUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨W, hWA, hωW⟩
      exact ⟨⟨W, hWA⟩, hωW⟩
    · rintro ⟨W, hωW⟩
      exact ⟨W, W.property, hωW⟩
  rw [hVA, hPreimage]
  apply MeasurableSet.iUnion
  intro W
  have hWC : (W : Set (NonemptyCompacts X)) ∈ C := hAC W.property
  rcases hWC with ⟨u, huD, huW⟩
  rw [← huW]
  exact measurableSet_preimage_vietorisBasic hS hScompact hSne
    huD.1 (fun U hU => hBbasis.isOpen (huD.2.2 hU))

/-- Canonical-Borel form of `measurable_bundleNonemptyCompacts`.  It makes no
global measurable-space choice for the hyperspace: the codomain sigma-algebra
is displayed explicitly as `borel (NonemptyCompacts X)`.
@isnad1 id=measurab.3h3v.s6.e7ec5832b62b from=translated src=- shape=c7504f8a vocab=06384727
-/
theorem measurable_bundleNonemptyCompacts_borel
    [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty) :
    @Measurable Ω (NonemptyCompacts X) _ (borel (NonemptyCompacts X))
      (bundleNonemptyCompacts S hScompact hSne) := by
  letI : MeasurableSpace (NonemptyCompacts X) := borel (NonemptyCompacts X)
  haveI : BorelSpace (NonemptyCompacts X) := ⟨rfl⟩
  exact measurable_bundleNonemptyCompacts hS hScompact hSne

/-- Every measurable hyperspace-valued map gives an Effros-measurable
set-valued map by forgetting the bundle.  This direction only uses that open
subsets of the hyperspace are measurable.
@isnad1 id=iseffros.1h3v.s5.41fab4e0442f from=translated src=- shape=3feb85f2 vocab=014974a9
-/
theorem effrosMeasurable_coe_of_measurable_nonemptyCompacts
    [MeasurableSpace Ω] [TopologicalSpace X]
    [MeasurableSpace (NonemptyCompacts X)]
    [OpensMeasurableSpace (NonemptyCompacts X)]
    {K : Ω → NonemptyCompacts X} (hK : Measurable K) :
    RandomSet.IsEffrosMeasurable (fun ω => (K ω : Set X)) := by
  intro U hU
  change MeasurableSet
    (K ⁻¹' {L : NonemptyCompacts X | ((L : Set X) ∩ U).Nonempty})
  exact hK
    (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet

/-- On nonempty compact-valued correspondences in a second-countable metric
space, Effros measurability is equivalent to Borel measurability as a map into
the Hausdorff/Vietoris hyperspace.
@isnad1 id=iff.2h3v.s6.4209b2ea8432 from=translated src=- shape=498a3655 vocab=552e59d4
-/
theorem effrosMeasurable_iff_measurable_bundleNonemptyCompacts
    [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)] [BorelSpace (NonemptyCompacts X)]
    {S : Ω → Set X} (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) :
    RandomSet.IsEffrosMeasurable S ↔
      Measurable (bundleNonemptyCompacts S hScompact hSne) := by
  constructor
  · intro hS
    exact measurable_bundleNonemptyCompacts hS hScompact hSne
  · intro hBundle
    simpa only [coe_bundleNonemptyCompacts] using
      effrosMeasurable_coe_of_measurable_nonemptyCompacts hBundle

/-- Canonical-Borel version of the Effros/hyperspace equivalence.
@isnad1 id=iff.2h3v.s6.c8f2ada6b632 from=translated src=- shape=2d6fbd0e vocab=06384727
-/
theorem effrosMeasurable_iff_measurable_bundleNonemptyCompacts_borel
    [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    {S : Ω → Set X} (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) :
    RandomSet.IsEffrosMeasurable S ↔
      @Measurable Ω (NonemptyCompacts X) _ (borel (NonemptyCompacts X))
        (bundleNonemptyCompacts S hScompact hSne) := by
  letI : MeasurableSpace (NonemptyCompacts X) := borel (NonemptyCompacts X)
  haveI : BorelSpace (NonemptyCompacts X) := ⟨rfl⟩
  exact effrosMeasurable_iff_measurable_bundleNonemptyCompacts hScompact hSne

/-- Hausdorff distance between two compact-valued Effros correspondences is
measurable directly from their hyperspace-valued realizations.  Unlike the
Castaing proof in `MeasurableHausdorff`, this version does not require
completeness or a measurable structure on `X` itself.
@isnad1 id=measurab.6h4v.s7.b1572240e948 from=translated src=- shape=e27e59ed vocab=cd30f571
-/
theorem measurable_hausdorffDist_compact_correspondence_hyperspace
    [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)] [BorelSpace (NonemptyCompacts X)]
    {S T : Ω → Set X}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hScompact : ∀ ω, IsCompact (S ω))
    (hTcompact : ∀ ω, IsCompact (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty) :
    Measurable (fun ω => hausdorffDist (S ω) (T ω)) := by
  have hKS : Measurable (bundleNonemptyCompacts S hScompact hSne) :=
    measurable_bundleNonemptyCompacts hS hScompact hSne
  have hKT : Measurable (bundleNonemptyCompacts T hTcompact hTne) :=
    measurable_bundleNonemptyCompacts hT hTcompact hTne
  have hdist := hKS.dist hKT
  simpa only [Metric.NonemptyCompacts.dist_eq, coe_bundleNonemptyCompacts] using hdist

/-- The capacity functional on an open test set is the probability of the
corresponding lower Vietoris open set under the hyperspace pushforward law.
@isnad1 id=eq.4h5v.s7.5063025eb736 from=translated src=- shape=879dafe5 vocab=3bfe9735
-/
theorem capacityFunctional_eq_map_bundleNonemptyCompacts_hit_open
    [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)] [BorelSpace (NonemptyCompacts X)]
    (μ : Measure Ω) {S : Ω → Set X}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    {U : Set X} (hU : IsOpen U) :
    capacityFunctional μ S U =
      Measure.map (bundleNonemptyCompacts S hScompact hSne) μ
        {K : NonemptyCompacts X | ((K : Set X) ∩ U).Nonempty} := by
  rw [Measure.map_apply
    (measurable_bundleNonemptyCompacts hS hScompact hSne)
    (TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet]
  rfl

/-- Convenience form for the bundled classical random-closed-set object.
@isnad1 id=measurab.2h3v.s7.9eb9b4e8adb6 from=translated src=- shape=586b8a9e vocab=1c707a26
-/
theorem RandomSet.EffrosRandomClosedSet.measurable_bundleNonemptyCompacts
    [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace (NonemptyCompacts X)] [BorelSpace (NonemptyCompacts X)]
    (S : RandomSet.EffrosRandomClosedSet Ω X)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty) :
    Measurable (bundleNonemptyCompacts (fun ω => S ω) hScompact hSne) :=
  RandomSetTheory.measurable_bundleNonemptyCompacts
    S.measurable' hScompact hSne

/-! ## Compact convex values and the Rådström embedding -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Bundle pointwise nonempty compact convex values.-/
def bundleCompactConvexSet (S : Ω → Set E)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω)) : Ω → CompactConvexSet E :=
  fun ω => CompactConvexSet.ofSet (S ω) (hScompact ω) (hSne ω) (hSconvex ω)

/--
@isnad1 id=eq.3h4v.s8.d590527807ba from=translated src=- shape=d94e9aad vocab=d971728d
-/
@[simp]
theorem coe_bundleCompactConvexSet (S : Ω → Set E)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω)) (ω : Ω) :
    (bundleCompactConvexSet S hScompact hSne hSconvex ω : Set E) = S ω :=
  rfl

/-- A compact convex-valued Effros correspondence is measurable as a
`CompactConvexSet E`.  Its measurable structure is the subtype Borel
structure inherited from `NonemptyCompacts E`.
@isnad1 id=measurab.4h3v.s7.240317209882 from=translated src=- shape=5bb194b9 vocab=9b5984b5
-/
theorem measurable_bundleCompactConvexSet
    [MeasurableSpace Ω] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)]
    [MeasurableSpace (CompactConvexSet E)] [BorelSpace (CompactConvexSet E)]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω)) :
    Measurable (bundleCompactConvexSet S hScompact hSne hSconvex) := by
  have hBundle : Measurable (bundleNonemptyCompacts S hScompact hSne) :=
    measurable_bundleNonemptyCompacts hS hScompact hSne
  apply measurable_of_isOpen
  intro V hV
  have hInducing : Topology.IsInducing
      (fun K : CompactConvexSet E => K.1) := by
    change Topology.IsInducing
      (Subtype.val : {K : NonemptyCompacts E // Convex ℝ (K : Set E)} →
        NonemptyCompacts E)
    exact isometry_subtype_coe.isEmbedding.isInducing
  obtain ⟨U, hU, hVU⟩ := hInducing.isOpen_iff.mp hV
  rw [← hVU]
  change MeasurableSet
    (bundleNonemptyCompacts S hScompact hSne ⁻¹' U)
  exact hBundle hU.measurableSet

/-- Canonical-Borel form of compact-convex hyperspace measurability.
@isnad1 id=measurab.4h3v.s7.ac40f6991b33 from=translated src=- shape=54dfd4a2 vocab=cc7ad2c3
-/
theorem measurable_bundleCompactConvexSet_borel
    [MeasurableSpace Ω] [SecondCountableTopology E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω)) :
    @Measurable Ω (CompactConvexSet E) _ (borel (CompactConvexSet E))
      (bundleCompactConvexSet S hScompact hSne hSconvex) := by
  letI : MeasurableSpace (NonemptyCompacts E) := borel (NonemptyCompacts E)
  haveI : BorelSpace (NonemptyCompacts E) := ⟨rfl⟩
  letI : MeasurableSpace (CompactConvexSet E) := borel (CompactConvexSet E)
  haveI : BorelSpace (CompactConvexSet E) := ⟨rfl⟩
  exact measurable_bundleCompactConvexSet
    hS hScompact hSne hSconvex

/-- After the Rådström embedding, a compact convex-valued Effros
correspondence is a measurable random continuous support function.
@isnad1 id=measurab.4h3v.s9.3412499607a5 from=translated src=- shape=974fe65f vocab=302c6e4b
-/
theorem measurable_radstromEmbedding_comp_bundleCompactConvexSet
    [MeasurableSpace Ω] [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)] [BorelSpace (NonemptyCompacts E)]
    [MeasurableSpace (CompactConvexSet E)] [BorelSpace (CompactConvexSet E)]
    [MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    [BorelSpace C(Metric.closedBall (0 : E) 1, ℝ)]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω)) :
    Measurable (fun ω => radstromEmbedding
      (bundleCompactConvexSet S hScompact hSne hSconvex ω)) := by
  exact (isometry_radstromEmbedding (E := E)).continuous.measurable.comp
    (measurable_bundleCompactConvexSet hS hScompact hSne hSconvex)

/-- Canonical-Borel form of measurability after the Rådström embedding.
@isnad1 id=measurab.4h3v.s8.45b9c4ec8150 from=translated src=- shape=95069b06 vocab=3698d0d7
-/
theorem measurable_radstromEmbedding_comp_bundleCompactConvexSet_borel
    [MeasurableSpace Ω] [FiniteDimensional ℝ E] [SecondCountableTopology E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω)) :
    @Measurable Ω C(Metric.closedBall (0 : E) 1, ℝ) _
      (borel C(Metric.closedBall (0 : E) 1, ℝ))
      (fun ω => radstromEmbedding
        (bundleCompactConvexSet S hScompact hSne hSconvex ω)) := by
  letI : MeasurableSpace (NonemptyCompacts E) := borel (NonemptyCompacts E)
  haveI : BorelSpace (NonemptyCompacts E) := ⟨rfl⟩
  letI : MeasurableSpace (CompactConvexSet E) := borel (CompactConvexSet E)
  haveI : BorelSpace (CompactConvexSet E) := ⟨rfl⟩
  letI : MeasurableSpace C(Metric.closedBall (0 : E) 1, ℝ) :=
    borel C(Metric.closedBall (0 : E) 1, ℝ)
  haveI : BorelSpace C(Metric.closedBall (0 : E) 1, ℝ) := ⟨rfl⟩
  exact measurable_radstromEmbedding_comp_bundleCompactConvexSet
    hS hScompact hSne hSconvex

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
