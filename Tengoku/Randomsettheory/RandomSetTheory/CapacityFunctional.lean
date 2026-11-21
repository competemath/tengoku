/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hitting events and the capacity functional

For a set-valued map `S : Ω → Set X` and a deterministic test set `K`, the
**hitting event** is

`{ω | (S ω ∩ K).Nonempty}`.

Its measure is the hitting, or capacity, functional of `S`.  This module
develops the measure-theoretic algebra of that functional without putting a
measurable hyperspace structure on closed subsets of `X`.

The main measurability facts are:

* open test sets are exactly the events controlled by Effros measurability;
* compact test sets are measurable for closed-valued Effros correspondences
  in a metric space.  The latter is proved by writing the compact hitting
  event as a decreasing countable intersection of open-neighbourhood hitting
  events.

The module also proves normalization, monotonicity, countable and finite
subadditivity, two-alternation (submodularity), almost-sure invariance, and
continuity from below and from above on decreasing compact tests.

## References

* Matheron, G. (1975), *Random Sets and Integral Geometry*.
* Molchanov, I. (2005), *Theory of Random Sets*.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

noncomputable section

namespace RandomSetTheory

variable {Ω X : Type*}

/-! ## Events -/

/-- The event on which the correspondence `S` hits the deterministic set `K`.-/
def hitEvent (S : Ω → Set X) (K : Set X) : Set Ω :=
  {ω | (S ω ∩ K).Nonempty}

/-- The event on which the correspondence `S` avoids the deterministic set `K`.-/
def avoidEvent (S : Ω → Set X) (K : Set X) : Set Ω :=
  {ω | ¬(S ω ∩ K).Nonempty}

@[simp] theorem mem_hitEvent {S : Ω → Set X} {K : Set X} {ω : Ω} :
    ω ∈ hitEvent S K ↔ (S ω ∩ K).Nonempty :=
  Iff.rfl

@[simp] theorem mem_avoidEvent {S : Ω → Set X} {K : Set X} {ω : Ω} :
    ω ∈ avoidEvent S K ↔ ¬(S ω ∩ K).Nonempty :=
  Iff.rfl

theorem avoidEvent_eq_compl (S : Ω → Set X) (K : Set X) :
    avoidEvent S K = (hitEvent S K)ᶜ :=
  rfl

@[simp] theorem hitEvent_empty (S : Ω → Set X) :
    hitEvent S ∅ = ∅ := by
  ext ω
  simp [hitEvent]

@[simp] theorem avoidEvent_empty (S : Ω → Set X) :
    avoidEvent S ∅ = Set.univ := by
  rw [avoidEvent_eq_compl, hitEvent_empty, compl_empty]

theorem hitEvent_univ (S : Ω → Set X) :
    hitEvent S Set.univ = {ω | (S ω).Nonempty} := by
  ext ω
  simp [hitEvent]

theorem avoidEvent_univ (S : Ω → Set X) :
    avoidEvent S Set.univ = {ω | ¬(S ω).Nonempty} := by
  ext ω
  simp [avoidEvent]

theorem hitEvent_union (S : Ω → Set X) (K L : Set X) :
    hitEvent S (K ∪ L) = hitEvent S K ∪ hitEvent S L := by
  ext ω
  simp only [mem_hitEvent, Set.mem_union]
  constructor
  · rintro ⟨x, hxS, hxK | hxL⟩
    · exact Or.inl ⟨x, hxS, hxK⟩
    · exact Or.inr ⟨x, hxS, hxL⟩
  · rintro (⟨x, hxS, hxK⟩ | ⟨x, hxS, hxL⟩)
    · exact ⟨x, hxS, Or.inl hxK⟩
    · exact ⟨x, hxS, Or.inr hxL⟩

theorem avoidEvent_union (S : Ω → Set X) (K L : Set X) :
    avoidEvent S (K ∪ L) = avoidEvent S K ∩ avoidEvent S L := by
  simp only [avoidEvent_eq_compl, hitEvent_union, compl_union]

theorem hitEvent_iUnion {ι : Sort*} (S : Ω → Set X) (K : ι → Set X) :
    hitEvent S (⋃ i, K i) = ⋃ i, hitEvent S (K i) := by
  ext ω
  constructor
  · rintro ⟨x, hxS, hxK⟩
    rcases Set.mem_iUnion.1 hxK with ⟨i, hxi⟩
    exact Set.mem_iUnion.2 ⟨i, ⟨x, hxS, hxi⟩⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨i, x, hxS, hxi⟩
    exact ⟨x, hxS, Set.mem_iUnion.2 ⟨i, hxi⟩⟩

theorem avoidEvent_iUnion {ι : Type*} (S : Ω → Set X) (K : ι → Set X) :
    avoidEvent S (⋃ i, K i) = ⋂ i, avoidEvent S (K i) := by
  simp only [avoidEvent_eq_compl, hitEvent_iUnion, compl_iUnion]

theorem hitEvent_mono {S : Ω → Set X} : Monotone (hitEvent S) := by
  intro K L hKL ω
  rintro ⟨x, hxS, hxK⟩
  exact ⟨x, hxS, hKL hxK⟩

theorem avoidEvent_antitone {S : Ω → Set X} : Antitone (avoidEvent S) := by
  intro K L hKL
  rw [avoidEvent_eq_compl, avoidEvent_eq_compl]
  exact compl_subset_compl.mpr (hitEvent_mono hKL)

theorem hitEvent_mono_correspondence {S T : Ω → Set X}
    (hST : ∀ ω, S ω ⊆ T ω) (K : Set X) :
    hitEvent S K ⊆ hitEvent T K := by
  intro ω
  rintro ⟨x, hxS, hxK⟩
  exact ⟨x, hST ω hxS, hxK⟩

theorem hitEvent_inter_subset (S : Ω → Set X) (K L : Set X) :
    hitEvent S (K ∩ L) ⊆ hitEvent S K ∩ hitEvent S L := by
  intro ω
  rintro ⟨x, hxS, hxK, hxL⟩
  exact ⟨⟨x, hxS, hxK⟩, ⟨x, hxS, hxL⟩⟩

/-! ## Measurability of hitting and avoidance events -/

variable [MeasurableSpace Ω]

/-- Open hitting events are measurable by the definition of Effros
measurability.-/
theorem measurableSet_hitEvent_open [TopologicalSpace X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    {U : Set X} (hU : IsOpen U) :
    MeasurableSet (hitEvent S U) :=
  hS U hU

theorem measurableSet_avoidEvent_open [TopologicalSpace X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    {U : Set X} (hU : IsOpen U) :
    MeasurableSet (avoidEvent S U) := by
  rw [avoidEvent_eq_compl]
  exact (measurableSet_hitEvent_open hS hU).compl

/-- Membership-measurability gives measurability of hitting every countable
test set.  This complements the Effros/open-set route.-/
theorem measurableSet_hitEvent_countable [TopologicalSpace X]
    (S : RandomSet Ω X) {K : Set X} (hK : K.Countable) :
    MeasurableSet (hitEvent S K) := by
  letI := hK.to_subtype
  have hEq : hitEvent (fun ω => S ω) K =
      ⋃ x : K, {ω | (x : X) ∈ S ω} := by
    ext ω
    simp only [mem_hitEvent, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hxS, hxK⟩
      exact ⟨⟨x, hxK⟩, hxS⟩
    · rintro ⟨⟨x, hxK⟩, hxS⟩
      exact ⟨x, hxS, hxK⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun x =>
    S.measurable' (measurableSet_mem (x : X))

theorem measurableSet_avoidEvent_countable [TopologicalSpace X]
    (S : RandomSet Ω X) {K : Set X} (hK : K.Countable) :
    MeasurableSet (avoidEvent (fun ω => S ω) K) := by
  rw [avoidEvent_eq_compl]
  exact (measurableSet_hitEvent_countable S hK).compl

section CompactMeasurability

variable [MetricSpace X]

omit [MeasurableSpace Ω] in
/-- A closed-valued correspondence hits a compact set exactly when it hits
every open `1/(n+1)`-neighbourhood of that set.  Compactness is essential in
the reverse implication.-/
theorem hitEvent_compact_eq_iInter_thickening
    {S : Ω → Set X} (hSclosed : ∀ ω, IsClosed (S ω))
    {K : Set X} (hK : IsCompact K) :
    hitEvent S K =
      ⋂ n : ℕ, hitEvent S (Metric.thickening (1 / (n + 1 : ℝ)) K) := by
  ext ω
  simp only [Set.mem_iInter, mem_hitEvent]
  constructor
  · rintro ⟨x, hxS, hxK⟩ n
    refine ⟨x, hxS, ?_⟩
    exact Metric.self_subset_thickening (by positivity : 0 < 1 / (n + 1 : ℝ)) K hxK
  · intro hhit
    by_contra hnot
    have hsubset : K ⊆ (S ω)ᶜ := by
      intro x hxK hxS
      exact hnot ⟨x, hxS, hxK⟩
    obtain ⟨δ, hδ, hthick⟩ :=
      hK.exists_thickening_subset_open (hSclosed ω).isOpen_compl hsubset
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    rcases hhit n with ⟨x, hxS, hxthick⟩
    have hxcompl : x ∈ (S ω)ᶜ :=
      hthick (Metric.thickening_mono hn.le K hxthick)
    exact hxcompl hxS

/-- Compact hitting events of a closed-valued Effros correspondence are
measurable.-/
theorem measurableSet_hitEvent_compact
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω)) {K : Set X} (hK : IsCompact K) :
    MeasurableSet (hitEvent S K) := by
  rw [hitEvent_compact_eq_iInter_thickening hSclosed hK]
  exact MeasurableSet.iInter fun n =>
    measurableSet_hitEvent_open hS Metric.isOpen_thickening

theorem measurableSet_avoidEvent_compact
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω)) {K : Set X} (hK : IsCompact K) :
    MeasurableSet (avoidEvent S K) := by
  rw [avoidEvent_eq_compl]
  exact (measurableSet_hitEvent_compact hS hSclosed hK).compl

/-- Convenience form for the bundled classical random-closed-set object.-/
theorem RandomSet.EffrosRandomClosedSet.measurableSet_hitEvent_compact
    (S : RandomSet.EffrosRandomClosedSet Ω X) {K : Set X} (hK : IsCompact K) :
    MeasurableSet (hitEvent (fun ω => S ω) K) :=
  RandomSetTheory.measurableSet_hitEvent_compact S.measurable' S.isClosed' hK

theorem RandomSet.EffrosRandomClosedSet.measurableSet_avoidEvent_compact
    (S : RandomSet.EffrosRandomClosedSet Ω X) {K : Set X} (hK : IsCompact K) :
    MeasurableSet (avoidEvent (fun ω => S ω) K) :=
  RandomSetTheory.measurableSet_avoidEvent_compact S.measurable' S.isClosed' hK

end CompactMeasurability

/-! ## Capacity and avoidance functionals -/

/-- The hitting (capacity) functional of a set-valued map.  Its useful
measure-theoretic identities require the corresponding hitting events to be
measurable; this is automatic for the classes proved above.-/
def capacityFunctional (μ : Measure Ω) (S : Ω → Set X) (K : Set X) : ℝ≥0∞ :=
  μ (hitEvent S K)

/-- Synonym emphasizing the probabilistic hitting interpretation.-/
abbrev hittingFunctional (μ : Measure Ω) (S : Ω → Set X) (K : Set X) : ℝ≥0∞ :=
  capacityFunctional μ S K

/-- The measure of the avoidance event.-/
def avoidanceFunctional (μ : Measure Ω) (S : Ω → Set X) (K : Set X) : ℝ≥0∞ :=
  μ (avoidEvent S K)

@[simp] theorem capacityFunctional_empty (μ : Measure Ω) (S : Ω → Set X) :
    capacityFunctional μ S ∅ = 0 := by
  simp [capacityFunctional]

@[simp] theorem avoidanceFunctional_empty (μ : Measure Ω) (S : Ω → Set X) :
    avoidanceFunctional μ S ∅ = μ Set.univ := by
  simp [avoidanceFunctional]

theorem capacityFunctional_le_measure_univ (μ : Measure Ω)
    (S : Ω → Set X) (K : Set X) :
    capacityFunctional μ S K ≤ μ Set.univ :=
  measure_mono (Set.subset_univ _)

theorem capacityFunctional_mono (μ : Measure Ω) (S : Ω → Set X) :
    Monotone (capacityFunctional μ S) := by
  intro K L hKL
  exact measure_mono (hitEvent_mono hKL)

theorem avoidanceFunctional_antitone (μ : Measure Ω) (S : Ω → Set X) :
    Antitone (avoidanceFunctional μ S) := by
  intro K L hKL
  exact measure_mono (avoidEvent_antitone hKL)

theorem capacityFunctional_mono_correspondence (μ : Measure Ω)
    {S T : Ω → Set X} (hST : ∀ ω, S ω ⊆ T ω) (K : Set X) :
    capacityFunctional μ S K ≤ capacityFunctional μ T K :=
  measure_mono (hitEvent_mono_correspondence hST K)

theorem capacityFunctional_union (μ : Measure Ω) (S : Ω → Set X)
    (K L : Set X) :
    capacityFunctional μ S (K ∪ L) =
      μ (hitEvent S K ∪ hitEvent S L) := by
  rw [capacityFunctional, hitEvent_union]

theorem capacityFunctional_union_le (μ : Measure Ω) (S : Ω → Set X)
    (K L : Set X) :
    capacityFunctional μ S (K ∪ L) ≤
      capacityFunctional μ S K + capacityFunctional μ S L := by
  rw [capacityFunctional, hitEvent_union]
  exact measure_union_le _ _

theorem capacityFunctional_iUnion_le [Countable ι] (μ : Measure Ω)
    (S : Ω → Set X) (K : ι → Set X) :
    capacityFunctional μ S (⋃ i, K i) ≤
      ∑' i, capacityFunctional μ S (K i) := by
  simp only [capacityFunctional, hitEvent_iUnion]
  exact measure_iUnion_le _

theorem capacityFunctional_biUnion_finset_le {ι : Type*} (μ : Measure Ω)
    (S : Ω → Set X) (I : Finset ι) (K : ι → Set X) :
    capacityFunctional μ S (⋃ i ∈ I, K i) ≤
      ∑ i ∈ I, capacityFunctional μ S (K i) := by
  have hEvent : hitEvent S (⋃ i ∈ I, K i) =
      ⋃ i ∈ I, hitEvent S (K i) := by
    rw [hitEvent_iUnion]
    congr 1
    funext i
    rw [hitEvent_iUnion]
  rw [capacityFunctional, hEvent]
  exact measure_biUnion_finset_le I (fun i => hitEvent S (K i))

/-- Two-alternation (submodularity), a characteristic capacity-functional
inequality.-/
theorem capacityFunctional_union_add_inter_le
    (μ : Measure Ω) (S : Ω → Set X) (K L : Set X)
    (hL : MeasurableSet (hitEvent S L)) :
    capacityFunctional μ S (K ∪ L) + capacityFunctional μ S (K ∩ L) ≤
      capacityFunctional μ S K + capacityFunctional μ S L := by
  calc
    capacityFunctional μ S (K ∪ L) + capacityFunctional μ S (K ∩ L) =
        μ (hitEvent S K ∪ hitEvent S L) + μ (hitEvent S (K ∩ L)) := by
          rw [capacityFunctional_union]
          rfl
    _ ≤ μ (hitEvent S K ∪ hitEvent S L) +
        μ (hitEvent S K ∩ hitEvent S L) := by
          exact add_le_add le_rfl
            (measure_mono (μ := μ) (hitEvent_inter_subset S K L))
    _ = capacityFunctional μ S K + capacityFunctional μ S L := by
          simpa only [capacityFunctional] using
            measure_union_add_inter (μ := μ) (hitEvent S K) hL

theorem capacityFunctional_add_avoidance
    (μ : Measure Ω) (S : Ω → Set X) (K : Set X)
    (hK : MeasurableSet (hitEvent S K)) :
    capacityFunctional μ S K + avoidanceFunctional μ S K = μ Set.univ := by
  simpa only [capacityFunctional, avoidanceFunctional, avoidEvent_eq_compl] using
    measure_add_measure_compl (μ := μ) hK

theorem avoidanceFunctional_eq_measure_univ_sub
    (μ : Measure Ω) (S : Ω → Set X) (K : Set X)
    (hK : MeasurableSet (hitEvent S K)) (hfin : μ (hitEvent S K) ≠ ∞) :
    avoidanceFunctional μ S K = μ Set.univ - capacityFunctional μ S K := by
  simpa only [capacityFunctional, avoidanceFunctional, avoidEvent_eq_compl] using
    measure_compl (μ := μ) hK hfin

theorem capacityFunctional_univ_of_ae_nonempty
    (μ : Measure Ω) (S : Ω → Set X) (hne : ∀ᵐ ω ∂μ, (S ω).Nonempty) :
    capacityFunctional μ S Set.univ = μ Set.univ := by
  rw [capacityFunctional, hitEvent_univ]
  apply measure_congr
  filter_upwards [hne] with ω hω
  exact propext (iff_true_intro hω)

theorem capacityFunctional_univ_eq_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → Set X)
    (hne : ∀ᵐ ω ∂μ, (S ω).Nonempty) :
    capacityFunctional μ S Set.univ = 1 := by
  rw [capacityFunctional_univ_of_ae_nonempty μ S hne, measure_univ]

theorem capacityFunctional_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → Set X) (K : Set X) :
    capacityFunctional μ S K ≤ 1 := by
  simpa only [measure_univ] using capacityFunctional_le_measure_univ μ S K

theorem avoidanceFunctional_eq_one_sub
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → Set X) (K : Set X)
    (hK : MeasurableSet (hitEvent S K)) :
    avoidanceFunctional μ S K = 1 - capacityFunctional μ S K := by
  have hfin : μ (hitEvent S K) ≠ ∞ := by
    exact ne_top_of_le_ne_top (by simp)
      (capacityFunctional_le_one μ S K)
  simpa only [measure_univ] using
    avoidanceFunctional_eq_measure_univ_sub μ S K hK hfin

/-! ## Almost-sure invariance -/

theorem hitEvent_ae_eq_of_ae_eq (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    hitEvent S K =ᵐ[μ] hitEvent T K := by
  filter_upwards [hST] with ω hω
  exact congrArg (fun A : Set X => (A ∩ K).Nonempty) hω

theorem avoidEvent_ae_eq_of_ae_eq (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    avoidEvent S K =ᵐ[μ] avoidEvent T K := by
  filter_upwards [hST] with ω hω
  exact congrArg (fun A : Set X => ¬(A ∩ K).Nonempty) hω

theorem capacityFunctional_congr_ae (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    capacityFunctional μ S K = capacityFunctional μ T K := by
  exact measure_congr (hitEvent_ae_eq_of_ae_eq μ hST K)

theorem avoidanceFunctional_congr_ae (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    avoidanceFunctional μ S K = avoidanceFunctional μ T K := by
  exact measure_congr (avoidEvent_ae_eq_of_ae_eq μ hST K)

/-! ## Continuity of the capacity functional -/

/-- Continuity from below on increasing deterministic test sets.  No
measurability hypothesis is needed for this outer-measure identity.-/
theorem capacityFunctional_iUnion_of_monotone
    (μ : Measure Ω) (S : Ω → Set X) {K : ℕ → Set X} (hK : Monotone K) :
    capacityFunctional μ S (⋃ n, K n) =
      ⨆ n, capacityFunctional μ S (K n) := by
  rw [capacityFunctional, hitEvent_iUnion]
  exact (hitEvent_mono.comp hK).measure_iUnion

theorem tendsto_capacityFunctional_iUnion_atTop
    (μ : Measure Ω) (S : Ω → Set X) {K : ℕ → Set X} (hK : Monotone K) :
    Tendsto (fun n => capacityFunctional μ S (K n)) atTop
      (𝓝 (capacityFunctional μ S (⋃ n, K n))) := by
  simpa only [capacityFunctional, hitEvent_iUnion, Function.comp_def] using
    tendsto_measure_iUnion_atTop (μ := μ) (hitEvent_mono.comp hK)

section CompactContinuity

variable [TopologicalSpace X] [T2Space X]

omit [MeasurableSpace Ω] in
/-- Hitting commutes with a decreasing intersection of compact test sets
when the correspondence has closed values.-/
theorem hitEvent_iInter_of_antitone_compact
    {S : Ω → Set X} (hSclosed : ∀ ω, IsClosed (S ω))
    {K : ℕ → Set X} (hKanti : Antitone K)
    (hKcompact : ∀ n, IsCompact (K n)) :
    hitEvent S (⋂ n, K n) = ⋂ n, hitEvent S (K n) := by
  apply Set.Subset.antisymm
  · intro ω
    rintro ⟨x, hxS, hxK⟩
    exact Set.mem_iInter.2 fun n => ⟨x, hxS, Set.mem_iInter.1 hxK n⟩
  · intro ω hω
    have hne : ∀ n, (S ω ∩ K n).Nonempty := fun n => Set.mem_iInter.1 hω n
    have hanti : Antitone (fun n => S ω ∩ K n) := fun i j hij =>
      Set.inter_subset_inter_right _ (hKanti hij)
    have hcompact : ∀ n, IsCompact (S ω ∩ K n) := fun n =>
      (hKcompact n).inter_left (hSclosed ω)
    have hclosed : ∀ n, IsClosed (S ω ∩ K n) := fun n =>
      (hSclosed ω).inter (hKcompact n).isClosed
    rcases IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun n => S ω ∩ K n) hanti.directed_ge hne hcompact hclosed with
      ⟨x, hx⟩
    have hxall : ∀ n, x ∈ S ω ∩ K n := Set.mem_iInter.1 hx
    exact ⟨x, (hxall 0).1, Set.mem_iInter.2 fun n => (hxall n).2⟩

/-- Continuity from above on decreasing compact test sets for a finite
measure.  Event measurability is stated explicitly so the result applies
beyond Effros correspondences as well.-/
theorem capacityFunctional_iInter_of_antitone_compact
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Ω → Set X} (hSclosed : ∀ ω, IsClosed (S ω))
    {K : ℕ → Set X} (hKanti : Antitone K)
    (hKcompact : ∀ n, IsCompact (K n))
    (hKmeas : ∀ n, MeasurableSet (hitEvent S (K n))) :
    capacityFunctional μ S (⋂ n, K n) =
      ⨅ n, capacityFunctional μ S (K n) := by
  rw [capacityFunctional, hitEvent_iInter_of_antitone_compact
    hSclosed hKanti hKcompact]
  exact (hitEvent_mono.comp_antitone hKanti).measure_iInter
    (fun n => (hKmeas n).nullMeasurableSet)
    ⟨0, measure_ne_top μ _⟩

theorem tendsto_capacityFunctional_iInter_atTop
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Ω → Set X} (hSclosed : ∀ ω, IsClosed (S ω))
    {K : ℕ → Set X} (hKanti : Antitone K)
    (hKcompact : ∀ n, IsCompact (K n))
    (hKmeas : ∀ n, MeasurableSet (hitEvent S (K n))) :
    Tendsto (fun n => capacityFunctional μ S (K n)) atTop
      (𝓝 (capacityFunctional μ S (⋂ n, K n))) := by
  simp only [capacityFunctional]
  rw [hitEvent_iInter_of_antitone_compact hSclosed hKanti hKcompact]
  simpa only [Function.comp_def] using
    tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (hKmeas n).nullMeasurableSet)
      (hitEvent_mono.comp_antitone hKanti)
      ⟨0, measure_ne_top μ _⟩

end CompactContinuity

section EffrosCompactContinuity

variable [MetricSpace X]

/-- Effros specialization of continuity from above: compact-hit
measurability is discharged by the theorem proved in this module.-/
theorem capacityFunctional_iInter_compact_of_effros
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω))
    {K : ℕ → Set X} (hKanti : Antitone K)
    (hKcompact : ∀ n, IsCompact (K n)) :
    capacityFunctional μ S (⋂ n, K n) =
      ⨅ n, capacityFunctional μ S (K n) :=
  capacityFunctional_iInter_of_antitone_compact μ hSclosed hKanti hKcompact
    (fun n => measurableSet_hitEvent_compact hS hSclosed (hKcompact n))

theorem tendsto_capacityFunctional_iInter_compact_of_effros
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω))
    {K : ℕ → Set X} (hKanti : Antitone K)
    (hKcompact : ∀ n, IsCompact (K n)) :
    Tendsto (fun n => capacityFunctional μ S (K n)) atTop
      (𝓝 (capacityFunctional μ S (⋂ n, K n))) :=
  tendsto_capacityFunctional_iInter_atTop μ hSclosed hKanti hKcompact
    (fun n => measurableSet_hitEvent_compact hS hSclosed (hKcompact n))

end EffrosCompactContinuity

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
