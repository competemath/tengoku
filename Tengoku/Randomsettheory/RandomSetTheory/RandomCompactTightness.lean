/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableHyperspace
import Tengoku.Randomsettheory.RandomSetTheory.BlaschkeSelection
import Tengoku.Seed.MeasureTheory.Measure.Tight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compact support and tightness of uniformly bounded random compact convex sets

Blaschke's theorem makes the nonempty compact convex subsets of a fixed
compact set into a compact family for the Hausdorff metric.  This file first
transfers that statement from `NonemptyCompacts E` to the bundled type
`CompactConvexSet E` itself.

It then applies the measurable hyperspace bundling of an Effros
correspondence.  If all values are nonempty, compact, convex, and contained
in one deterministic compact set, then both natural pushforward laws are
concentrated on explicit compact Blaschke families.  Consequently each such
law is tight.

No measurable-space instance is installed here.  The law statements assume
Borel measurable structures already chosen on the relevant hyperspaces;
callers may make the canonical choice locally with `borelize` or `letI`.
The tightness proved here concerns the law of one uniformly bounded random
compact set.  It is not a process-level tightness or functional-CLT theorem.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace Filter
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ## Blaschke compactness in `CompactConvexSet` -/

/-- Compact convex sets contained in a deterministic set `C`.-/
def compactConvexSubsets (C : Set E) : Set (CompactConvexSet E) :=
  {K | (K : Set E) ⊆ C}

omit [FiniteDimensional ℝ E] in
@[simp]
theorem mem_compactConvexSubsets {C : Set E} {K : CompactConvexSet E} :
    K ∈ compactConvexSubsets C ↔ (K : Set E) ⊆ C :=
  Iff.rfl

/-- **Blaschke compactness directly in `CompactConvexSet`.**  The compact
convex sets contained in a fixed compact set form a compact family in the
Hausdorff metric.-/
theorem isCompact_compactConvexSubsets_of_isCompact
    {C : Set E} (hC : IsCompact C) :
    IsCompact (compactConvexSubsets C) := by
  let val : CompactConvexSet E → NonemptyCompacts E := fun K => K.1
  have hval : Isometry val := by
    exact isometry_subtype_coe
  have himage :
      val '' compactConvexSubsets C =
        {K : NonemptyCompacts E |
          (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)} := by
    ext K
    constructor
    · rintro ⟨L, hLC, rfl⟩
      exact ⟨hLC, L.convex⟩
    · rintro ⟨hKC, hKconv⟩
      exact ⟨⟨K, hKconv⟩, hKC, rfl⟩
  rw [hval.isEmbedding.isCompact_iff, himage]
  exact isCompact_nonemptyCompactConvex_subsets_of_isCompact hC

/-- Radius-bounded Blaschke compactness in `CompactConvexSet`.-/
theorem isCompact_compactConvexSubsets_closedBall (R : ℝ) :
    IsCompact (compactConvexSubsets (Metric.closedBall (0 : E) R)) :=
  isCompact_compactConvexSubsets_of_isCompact
    (isCompact_closedBall (0 : E) R)

/-- Pointwise norm-bound form of Blaschke compactness in
`CompactConvexSet`.-/
theorem isCompact_compactConvexSet_of_norm_le (R : ℝ) :
    IsCompact {K : CompactConvexSet E |
      ∀ x ∈ (K : Set E), ‖x‖ ≤ R} := by
  simpa only [compactConvexSubsets, Set.mem_ofPred_eq, Set.subset_def,
    Metric.mem_closedBall, dist_zero_right] using
    isCompact_compactConvexSubsets_closedBall (E := E) R

/-- Sequential Blaschke selection entirely inside `CompactConvexSet`.-/
theorem exists_tendsto_subseq_compactConvexSet_of_subsets
    {C : Set E} (hC : IsCompact C) (K : ℕ → CompactConvexSet E)
    (hsubset : ∀ n, (K n : Set E) ⊆ C) :
    ∃ L : CompactConvexSet E, (L : Set E) ⊆ C ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto (fun n => K (phi n)) atTop (nhds L) := by
  have hA : IsCompact (compactConvexSubsets C) :=
    isCompact_compactConvexSubsets_of_isCompact hC
  have hK : ∀ n, K n ∈ compactConvexSubsets C := hsubset
  obtain ⟨L, hL, phi, hphi, hlim⟩ := hA.isSeqCompact hK
  exact ⟨L, hL, phi, hphi, hlim⟩

/-- Uniformly bounded sequential Blaschke selection in
`CompactConvexSet`.-/
theorem exists_tendsto_subseq_uniformlyBounded_compactConvexSet
    (K : ℕ → CompactConvexSet E) (R : ℝ)
    (hbound : ∀ n, ∀ x ∈ (K n : Set E), ‖x‖ ≤ R) :
    ∃ L : CompactConvexSet E,
      (∀ x ∈ (L : Set E), ‖x‖ ≤ R) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto (fun n => K (phi n)) atTop (nhds L) := by
  have hsubset : ∀ n, (K n : Set E) ⊆
      Metric.closedBall (0 : E) R := by
    intro n x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hbound n x hx
  obtain ⟨L, hL, phi, hphi, hlim⟩ :=
    exists_tendsto_subseq_compactConvexSet_of_subsets
      (E := E) (isCompact_closedBall (0 : E) R) K hsubset
  refine ⟨L, ?_, phi, hphi, hlim⟩
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hL hx

/-! ## Pointwise inclusion in the compact Blaschke families -/

omit [FiniteDimensional ℝ E] in
/-- The hyperspace bundling of a compact convex correspondence lies in the
Blaschke family generated by every deterministic containing set.-/
theorem bundleNonemptyCompacts_mem_blaschkeFamily
    {S : Ω → Set E} (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hSconvex : ∀ ω, Convex ℝ (S ω))
    {C : Set E} (hsubset : ∀ ω, S ω ⊆ C) (ω : Ω) :
    bundleNonemptyCompacts S hScompact hSne ω ∈
      {K : NonemptyCompacts E |
        (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)} := by
  exact ⟨hsubset ω, hSconvex ω⟩

omit [FiniteDimensional ℝ E] in
/-- The compact-convex bundling lies pointwise in the corresponding compact
family in `CompactConvexSet`.-/
theorem bundleCompactConvexSet_mem_compactConvexSubsets
    {S : Ω → Set E} (hScompact : ∀ ω, IsCompact (S ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hSconvex : ∀ ω, Convex ℝ (S ω))
    {C : Set E} (hsubset : ∀ ω, S ω ⊆ C) (ω : Ω) :
    bundleCompactConvexSet S hScompact hSne hSconvex ω ∈
      compactConvexSubsets C := by
  exact hsubset ω

/-! ## Compact support of the pushforward laws -/

/-- The hyperspace law of a uniformly contained compact convex
correspondence gives zero mass to the complement of its explicit compact
Blaschke family.-/
theorem map_bundleNonemptyCompacts_compl_blaschkeFamily_eq_zero
    [MeasurableSpace Ω] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)]
    [BorelSpace (NonemptyCompacts E)]
    (μ : Measure Ω) {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω))
    {C : Set E} (hC : IsCompact C) (hsubset : ∀ ω, S ω ⊆ C) :
    Measure.map (bundleNonemptyCompacts S hScompact hSne) μ
        ({K : NonemptyCompacts E |
          (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)}ᶜ) = 0 := by
  let f := bundleNonemptyCompacts S hScompact hSne
  let A : Set (NonemptyCompacts E) :=
    {K | (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)}
  have hf : Measurable f :=
    measurable_bundleNonemptyCompacts hS hScompact hSne
  have hA : IsCompact A := by
    simpa only [A] using
      isCompact_nonemptyCompactConvex_subsets_of_isCompact (E := E) hC
  have hpre : f ⁻¹' Aᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hω (bundleNonemptyCompacts_mem_blaschkeFamily
      hScompact hSne hSconvex hsubset ω)
  rw [Measure.map_apply hf hA.isClosed.measurableSet.compl, hpre,
    measure_empty]

/-- The law of the `CompactConvexSet` bundling is carried by the compact
family of all values contained in `C`.-/
theorem map_bundleCompactConvexSet_compl_compactConvexSubsets_eq_zero
    [MeasurableSpace Ω] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)]
    [BorelSpace (NonemptyCompacts E)]
    [MeasurableSpace (CompactConvexSet E)]
    [BorelSpace (CompactConvexSet E)]
    (μ : Measure Ω) {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω))
    {C : Set E} (hC : IsCompact C) (hsubset : ∀ ω, S ω ⊆ C) :
    Measure.map
        (bundleCompactConvexSet S hScompact hSne hSconvex) μ
        (compactConvexSubsets C)ᶜ = 0 := by
  let f := bundleCompactConvexSet S hScompact hSne hSconvex
  have hf : Measurable f :=
    measurable_bundleCompactConvexSet
      hS hScompact hSne hSconvex
  have hA : IsCompact (compactConvexSubsets C) :=
    isCompact_compactConvexSubsets_of_isCompact hC
  have hpre : f ⁻¹' (compactConvexSubsets C)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hω (bundleCompactConvexSet_mem_compactConvexSubsets
      hScompact hSne hSconvex hsubset ω)
  rw [Measure.map_apply hf hA.isClosed.measurableSet.compl, hpre,
    measure_empty]

/-- Closed-ball specialization: the compact-convex law is carried by the
compact family of sets whose points all have norm at most `R`.-/
theorem map_bundleCompactConvexSet_compl_normBounded_eq_zero
    [MeasurableSpace Ω] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)]
    [BorelSpace (NonemptyCompacts E)]
    [MeasurableSpace (CompactConvexSet E)]
    [BorelSpace (CompactConvexSet E)]
    (μ : Measure Ω) {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω)) (R : ℝ)
    (hbound : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ R) :
    Measure.map
        (bundleCompactConvexSet S hScompact hSne hSconvex) μ
        {K : CompactConvexSet E |
          ∀ x ∈ (K : Set E), ‖x‖ ≤ R}ᶜ = 0 := by
  have hsubset : ∀ ω, S ω ⊆ Metric.closedBall (0 : E) R := by
    intro ω x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hbound ω x hx
  simpa only [compactConvexSubsets, Set.mem_ofPred_eq, Set.subset_def,
    Metric.mem_closedBall, dist_zero_right] using
    map_bundleCompactConvexSet_compl_compactConvexSubsets_eq_zero
      μ hS hScompact hSne hSconvex
      (isCompact_closedBall (0 : E) R) hsubset

/-! ## Tightness of the laws -/

/-- Compact support on the Blaschke family implies tightness of the
hyperspace law.-/
theorem isTightMeasureSet_singleton_map_bundleNonemptyCompacts
    [MeasurableSpace Ω] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)]
    [BorelSpace (NonemptyCompacts E)]
    (μ : Measure Ω) {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω))
    {C : Set E} (hC : IsCompact C) (hsubset : ∀ ω, S ω ⊆ C) :
    IsTightMeasureSet
      {Measure.map (bundleNonemptyCompacts S hScompact hSne) μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let A : Set (NonemptyCompacts E) :=
    {K | (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)}
  have hA : IsCompact A := by
    simpa only [A] using
      isCompact_nonemptyCompactConvex_subsets_of_isCompact (E := E) hC
  refine ⟨A, hA, ?_⟩
  intro ν hν
  have hνeq : ν = Measure.map
      (bundleNonemptyCompacts S hScompact hSne) μ := by
    simpa only [Set.mem_singleton_iff] using hν
  rw [hνeq]
  calc
    (Measure.map (bundleNonemptyCompacts S hScompact hSne) μ) Aᶜ = 0 := by
      simpa only [A] using
        map_bundleNonemptyCompacts_compl_blaschkeFamily_eq_zero
          μ hS hScompact hSne hSconvex hC hsubset
    _ ≤ ε := bot_le

/-- Compact support implies tightness of the law on
`CompactConvexSet E`.-/
theorem isTightMeasureSet_singleton_map_bundleCompactConvexSet
    [MeasurableSpace Ω] [SecondCountableTopology E]
    [MeasurableSpace (NonemptyCompacts E)]
    [BorelSpace (NonemptyCompacts E)]
    [MeasurableSpace (CompactConvexSet E)]
    [BorelSpace (CompactConvexSet E)]
    (μ : Measure Ω) {S : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hScompact : ∀ ω, IsCompact (S ω)) (hSne : ∀ ω, (S ω).Nonempty)
    (hSconvex : ∀ ω, Convex ℝ (S ω))
    {C : Set E} (hC : IsCompact C) (hsubset : ∀ ω, S ω ⊆ C) :
    IsTightMeasureSet
      {Measure.map
        (bundleCompactConvexSet S hScompact hSne hSconvex) μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  refine ⟨compactConvexSubsets C,
    isCompact_compactConvexSubsets_of_isCompact hC, ?_⟩
  intro ν hν
  have hνeq : ν = Measure.map
      (bundleCompactConvexSet S hScompact hSne hSconvex) μ := by
    simpa only [Set.mem_singleton_iff] using hν
  rw [hνeq]
  exact
    (map_bundleCompactConvexSet_compl_compactConvexSubsets_eq_zero
      μ hS hScompact hSne hSconvex hC hsubset).le.trans bot_le

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
