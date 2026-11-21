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

/--
@isnad1 id=iff.0h5v.s5.9dcbcbab2da3 from=translated src=- shape=bee4b8c6 vocab=996ff445
-/
@[simp] theorem mem_hitEvent {S : Ω → Set X} {K : Set X} {ω : Ω} :
    ω ∈ hitEvent S K ↔ (S ω ∩ K).Nonempty :=
  Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.85a9c0cb66eb from=translated src=- shape=8abb245c vocab=667ade8a
-/
@[simp] theorem mem_avoidEvent {S : Ω → Set X} {K : Set X} {ω : Ω} :
    ω ∈ avoidEvent S K ↔ ¬(S ω ∩ K).Nonempty :=
  Iff.rfl

/--
@isnad1 id=eq.0h4v.s4.0c7d52aa3017 from=translated src=- shape=0c58e0aa vocab=0270a8f7
-/
theorem avoidEvent_eq_compl (S : Ω → Set X) (K : Set X) :
    avoidEvent S K = (hitEvent S K)ᶜ :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.8aa1a92ff66e from=translated src=- shape=ec0367c5 vocab=de84a178
-/
@[simp] theorem hitEvent_empty (S : Ω → Set X) :
    hitEvent S ∅ = ∅ := by
  ext ω
  simp [hitEvent]

/--
@isnad1 id=eq.0h3v.s4.d5a9485d2b7c from=translated src=- shape=6d66c8c8 vocab=0d2555e8
-/
@[simp] theorem avoidEvent_empty (S : Ω → Set X) :
    avoidEvent S ∅ = Set.univ := by
  rw [avoidEvent_eq_compl, hitEvent_empty, compl_empty]

/--
@isnad1 id=eq.0h3v.s4.677c51f3e6f4 from=translated src=- shape=f8a97d31 vocab=3b3c9249
-/
theorem hitEvent_univ (S : Ω → Set X) :
    hitEvent S Set.univ = {ω | (S ω).Nonempty} := by
  ext ω
  simp [hitEvent]

/--
@isnad1 id=eq.0h3v.s4.d4de0df08bba from=translated src=- shape=5072b2b0 vocab=fbdccf89
-/
theorem avoidEvent_univ (S : Ω → Set X) :
    avoidEvent S Set.univ = {ω | ¬(S ω).Nonempty} := by
  ext ω
  simp [avoidEvent]

/--
@isnad1 id=eq.0h5v.s5.d51ddf4359c1 from=translated src=- shape=382bcc08 vocab=4be730c0
-/
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

/--
@isnad1 id=eq.0h5v.s5.219c6cc20143 from=translated src=- shape=382bcc08 vocab=8c48ecef
-/
theorem avoidEvent_union (S : Ω → Set X) (K L : Set X) :
    avoidEvent S (K ∪ L) = avoidEvent S K ∩ avoidEvent S L := by
  simp only [avoidEvent_eq_compl, hitEvent_union, compl_union]

/--
@isnad1 id=eq.0h5v.s5.1b96d28681b3 from=translated src=- shape=ed90da23 vocab=4212faa6
-/
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

/--
@isnad1 id=eq.0h5v.s5.b88525a8f8e4 from=translated src=- shape=3d7fe9a7 vocab=bece221b
-/
theorem avoidEvent_iUnion {ι : Type*} (S : Ω → Set X) (K : ι → Set X) :
    avoidEvent S (⋃ i, K i) = ⋂ i, avoidEvent S (K i) := by
  simp only [avoidEvent_eq_compl, hitEvent_iUnion, compl_iUnion]

/--
@isnad1 id=monotone.0h3v.s5.4bb6677d2738 from=translated src=- shape=865081ae vocab=173b3a69
-/
theorem hitEvent_mono {S : Ω → Set X} : Monotone (hitEvent S) := by
  intro K L hKL ω
  rintro ⟨x, hxS, hxK⟩
  exact ⟨x, hxS, hKL hxK⟩

/--
@isnad1 id=antitone.0h3v.s5.feb4b3df9215 from=translated src=- shape=865081ae vocab=92c4058e
-/
theorem avoidEvent_antitone {S : Ω → Set X} : Antitone (avoidEvent S) := by
  intro K L hKL
  rw [avoidEvent_eq_compl, avoidEvent_eq_compl]
  exact compl_subset_compl.mpr (hitEvent_mono hKL)

/--
@isnad1 id=le.1h5v.s5.82c2e0a0edeb from=translated src=- shape=051081dd vocab=e225d77a
-/
theorem hitEvent_mono_correspondence {S T : Ω → Set X}
    (hST : ∀ ω, S ω ⊆ T ω) (K : Set X) :
    hitEvent S K ⊆ hitEvent T K := by
  intro ω
  rintro ⟨x, hxS, hxK⟩
  exact ⟨x, hST ω hxS, hxK⟩

/--
@isnad1 id=le.0h5v.s5.5623eff371d5 from=translated src=- shape=382bcc08 vocab=d8d4596c
-/
theorem hitEvent_inter_subset (S : Ω → Set X) (K L : Set X) :
    hitEvent S (K ∩ L) ⊆ hitEvent S K ∩ hitEvent S L := by
  intro ω
  rintro ⟨x, hxS, hxK, hxL⟩
  exact ⟨⟨x, hxS, hxK⟩, ⟨x, hxS, hxL⟩⟩

/-! ## Measurability of hitting and avoidance events -/

variable [MeasurableSpace Ω]

/-- Open hitting events are measurable by the definition of Effros
measurability.
@isnad1 id=measurab.2h4v.s5.b0a0cfdbc056 from=translated src=- shape=58f60e05 vocab=5cf65f2f
-/
theorem measurableSet_hitEvent_open [TopologicalSpace X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    {U : Set X} (hU : IsOpen U) :
    MeasurableSet (hitEvent S U) :=
  hS U hU

/--
@isnad1 id=measurab.2h4v.s5.2c53c24d23fe from=translated src=- shape=58f60e05 vocab=791a0065
-/
theorem measurableSet_avoidEvent_open [TopologicalSpace X]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    {U : Set X} (hU : IsOpen U) :
    MeasurableSet (avoidEvent S U) := by
  rw [avoidEvent_eq_compl]
  exact (measurableSet_hitEvent_open hS hU).compl

/-- Membership-measurability gives measurability of hitting every countable
test set.  This complements the Effros/open-set route.
@isnad1 id=measurab.1h4v.s5.8ad4b11a4c47 from=translated src=- shape=7c0e1e31 vocab=86c9ad2b
-/
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

/--
@isnad1 id=measurab.1h4v.s5.17236c739df1 from=translated src=- shape=3b3d4c2e vocab=578fb62d
-/
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
the reverse implication.
@isnad1 id=eq.2h4v.s6.ca0e98e3de2d from=translated src=- shape=7a149a84 vocab=2b60b513
-/
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
measurable.
@isnad1 id=measurab.3h4v.s6.f618fc67d83a from=translated src=- shape=837300ec vocab=2ac238de
-/
theorem measurableSet_hitEvent_compact
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω)) {K : Set X} (hK : IsCompact K) :
    MeasurableSet (hitEvent S K) := by
  rw [hitEvent_compact_eq_iInter_thickening hSclosed hK]
  exact MeasurableSet.iInter fun n =>
    measurableSet_hitEvent_open hS Metric.isOpen_thickening

/--
@isnad1 id=measurab.3h4v.s6.1843d04cd2fb from=translated src=- shape=837300ec vocab=881b514a
-/
theorem measurableSet_avoidEvent_compact
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hSclosed : ∀ ω, IsClosed (S ω)) {K : Set X} (hK : IsCompact K) :
    MeasurableSet (avoidEvent S K) := by
  rw [avoidEvent_eq_compl]
  exact (measurableSet_hitEvent_compact hS hSclosed hK).compl

/-- Convenience form for the bundled classical random-closed-set object.
@isnad1 id=measurab.1h4v.s5.35db28160a09 from=translated src=- shape=3b3d4c2e vocab=e4b96c85
-/
theorem RandomSet.EffrosRandomClosedSet.measurableSet_hitEvent_compact
    (S : RandomSet.EffrosRandomClosedSet Ω X) {K : Set X} (hK : IsCompact K) :
    MeasurableSet (hitEvent (fun ω => S ω) K) :=
  RandomSetTheory.measurableSet_hitEvent_compact S.measurable' S.isClosed' hK

/--
@isnad1 id=measurab.1h4v.s5.b89d4602f381 from=translated src=- shape=3b3d4c2e vocab=6d765afc
-/
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

/--
@isnad1 id=eq.0h4v.s5.9ac4e7174ccd from=translated src=- shape=9eeacb25 vocab=b7ca8195
-/
@[simp] theorem capacityFunctional_empty (μ : Measure Ω) (S : Ω → Set X) :
    capacityFunctional μ S ∅ = 0 := by
  simp [capacityFunctional]

/--
@isnad1 id=eq.0h4v.s5.a6820bd666ce from=translated src=- shape=22dd2ac4 vocab=43230d77
-/
@[simp] theorem avoidanceFunctional_empty (μ : Measure Ω) (S : Ω → Set X) :
    avoidanceFunctional μ S ∅ = μ Set.univ := by
  simp [avoidanceFunctional]

/--
@isnad1 id=le.0h5v.s5.770e903057e1 from=translated src=- shape=36b32f2a vocab=5a0862bf
-/
theorem capacityFunctional_le_measure_univ (μ : Measure Ω)
    (S : Ω → Set X) (K : Set X) :
    capacityFunctional μ S K ≤ μ Set.univ :=
  measure_mono (Set.subset_univ _)

/--
@isnad1 id=monotone.0h4v.s5.543102ae10b9 from=translated src=- shape=d75c29fa vocab=bfac8931
-/
theorem capacityFunctional_mono (μ : Measure Ω) (S : Ω → Set X) :
    Monotone (capacityFunctional μ S) := by
  intro K L hKL
  exact measure_mono (hitEvent_mono hKL)

/--
@isnad1 id=antitone.0h4v.s5.f0e0d7208b6f from=translated src=- shape=d75c29fa vocab=653a51ee
-/
theorem avoidanceFunctional_antitone (μ : Measure Ω) (S : Ω → Set X) :
    Antitone (avoidanceFunctional μ S) := by
  intro K L hKL
  exact measure_mono (avoidEvent_antitone hKL)

/--
@isnad1 id=le.1h6v.s5.4668c1644a6a from=translated src=- shape=f6358b56 vocab=a548dfa9
-/
theorem capacityFunctional_mono_correspondence (μ : Measure Ω)
    {S T : Ω → Set X} (hST : ∀ ω, S ω ⊆ T ω) (K : Set X) :
    capacityFunctional μ S K ≤ capacityFunctional μ T K :=
  measure_mono (hitEvent_mono_correspondence hST K)

/--
@isnad1 id=eq.0h6v.s6.b6679e1fd39d from=translated src=- shape=c40c6e70 vocab=d43623ba
-/
theorem capacityFunctional_union (μ : Measure Ω) (S : Ω → Set X)
    (K L : Set X) :
    capacityFunctional μ S (K ∪ L) =
      μ (hitEvent S K ∪ hitEvent S L) := by
  rw [capacityFunctional, hitEvent_union]

/--
@isnad1 id=le.0h6v.s5.6a8d77de2c21 from=translated src=- shape=54464729 vocab=92a3971a
-/
theorem capacityFunctional_union_le (μ : Measure Ω) (S : Ω → Set X)
    (K L : Set X) :
    capacityFunctional μ S (K ∪ L) ≤
      capacityFunctional μ S K + capacityFunctional μ S L := by
  rw [capacityFunctional, hitEvent_union]
  exact measure_union_le _ _

/--
@isnad1 id=le.0h6v.s5.606999ac3173 from=translated src=- shape=9a581371 vocab=0e55c5ce
-/
theorem capacityFunctional_iUnion_le [Countable ι] (μ : Measure Ω)
    (S : Ω → Set X) (K : ι → Set X) :
    capacityFunctional μ S (⋃ i, K i) ≤
      ∑' i, capacityFunctional μ S (K i) := by
  simp only [capacityFunctional, hitEvent_iUnion]
  exact measure_iUnion_le _

/--
@isnad1 id=le.0h7v.s6.75790f375444 from=translated src=- shape=77feafdf vocab=b152e37a
-/
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
inequality.
@isnad1 id=le.1h6v.s6.d405512bf426 from=translated src=- shape=0db966c5 vocab=285236c4
-/
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

/--
@isnad1 id=eq.1h5v.s6.f058d5c0e33c from=translated src=- shape=c3a6ba71 vocab=31479d86
-/
theorem capacityFunctional_add_avoidance
    (μ : Measure Ω) (S : Ω → Set X) (K : Set X)
    (hK : MeasurableSet (hitEvent S K)) :
    capacityFunctional μ S K + avoidanceFunctional μ S K = μ Set.univ := by
  simpa only [capacityFunctional, avoidanceFunctional, avoidEvent_eq_compl] using
    measure_add_measure_compl (μ := μ) hK

/--
@isnad1 id=eq.2h5v.s6.c60c27f8ff24 from=translated src=- shape=9228150a vocab=f8012082
-/
theorem avoidanceFunctional_eq_measure_univ_sub
    (μ : Measure Ω) (S : Ω → Set X) (K : Set X)
    (hK : MeasurableSet (hitEvent S K)) (hfin : μ (hitEvent S K) ≠ ∞) :
    avoidanceFunctional μ S K = μ Set.univ - capacityFunctional μ S K := by
  simpa only [capacityFunctional, avoidanceFunctional, avoidEvent_eq_compl] using
    measure_compl (μ := μ) hK hfin

/--
@isnad1 id=eq.1h4v.s5.ca3cffee665d from=translated src=- shape=e892a750 vocab=80c653da
-/
theorem capacityFunctional_univ_of_ae_nonempty
    (μ : Measure Ω) (S : Ω → Set X) (hne : ∀ᵐ ω ∂μ, (S ω).Nonempty) :
    capacityFunctional μ S Set.univ = μ Set.univ := by
  rw [capacityFunctional, hitEvent_univ]
  apply measure_congr
  filter_upwards [hne] with ω hω
  exact propext (iff_true_intro hω)

/--
@isnad1 id=eq.1h4v.s5.d0e56e4d19a0 from=translated src=- shape=3e447dde vocab=18fca3e0
-/
theorem capacityFunctional_univ_eq_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → Set X)
    (hne : ∀ᵐ ω ∂μ, (S ω).Nonempty) :
    capacityFunctional μ S Set.univ = 1 := by
  rw [capacityFunctional_univ_of_ae_nonempty μ S hne, measure_univ]

/--
@isnad1 id=le.0h5v.s5.fcb7e02847c7 from=translated src=- shape=4b97bb70 vocab=c672ac50
-/
theorem capacityFunctional_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → Set X) (K : Set X) :
    capacityFunctional μ S K ≤ 1 := by
  simpa only [measure_univ] using capacityFunctional_le_measure_univ μ S K

/--
@isnad1 id=eq.1h5v.s5.35a94d312e7c from=translated src=- shape=8b5f797e vocab=c63ab81e
-/
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

/--
@isnad1 id=eventual.1h6v.s6.c6d17edaf2b3 from=translated src=- shape=b9fd1232 vocab=2cfa8cce
-/
theorem hitEvent_ae_eq_of_ae_eq (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    hitEvent S K =ᵐ[μ] hitEvent T K := by
  filter_upwards [hST] with ω hω
  exact congrArg (fun A : Set X => (A ∩ K).Nonempty) hω

/--
@isnad1 id=eventual.1h6v.s6.833e8427dc69 from=translated src=- shape=b9fd1232 vocab=cef58943
-/
theorem avoidEvent_ae_eq_of_ae_eq (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    avoidEvent S K =ᵐ[μ] avoidEvent T K := by
  filter_upwards [hST] with ω hω
  exact congrArg (fun A : Set X => ¬(A ∩ K).Nonempty) hω

/--
@isnad1 id=eq.1h6v.s5.af2d7d88e030 from=translated src=- shape=ca83b576 vocab=220b6fec
-/
theorem capacityFunctional_congr_ae (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    capacityFunctional μ S K = capacityFunctional μ T K := by
  exact measure_congr (hitEvent_ae_eq_of_ae_eq μ hST K)

/--
@isnad1 id=eq.1h6v.s5.056455848b58 from=translated src=- shape=ca83b576 vocab=4e73de2b
-/
theorem avoidanceFunctional_congr_ae (μ : Measure Ω) {S T : Ω → Set X}
    (hST : S =ᵐ[μ] T) (K : Set X) :
    avoidanceFunctional μ S K = avoidanceFunctional μ T K := by
  exact measure_congr (avoidEvent_ae_eq_of_ae_eq μ hST K)

/-! ## Continuity of the capacity functional -/

/-- Continuity from below on increasing deterministic test sets.  No
measurability hypothesis is needed for this outer-measure identity.
@isnad1 id=eq.1h5v.s6.7db328eedbf1 from=translated src=- shape=08bbc0b5 vocab=59bc61f9
-/
theorem capacityFunctional_iUnion_of_monotone
    (μ : Measure Ω) (S : Ω → Set X) {K : ℕ → Set X} (hK : Monotone K) :
    capacityFunctional μ S (⋃ n, K n) =
      ⨆ n, capacityFunctional μ S (K n) := by
  rw [capacityFunctional, hitEvent_iUnion]
  exact (hitEvent_mono.comp hK).measure_iUnion

/--
@isnad1 id=tendsto.1h5v.s6.c9b29773ea13 from=translated src=- shape=dc8e080c vocab=2c760af2
-/
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
when the correspondence has closed values.
@isnad1 id=eq.3h4v.s6.60f198fe1ae9 from=translated src=- shape=1eecd3c0 vocab=5f336a8d
-/
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
beyond Effros correspondences as well.
@isnad1 id=eq.4h5v.s7.b06987e21c9d from=translated src=- shape=28b32b79 vocab=23d9a3f3
-/
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

/--
@isnad1 id=tendsto.4h5v.s6.8330d0a6a721 from=translated src=- shape=269d3676 vocab=104736f8
-/
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
measurability is discharged by the theorem proved in this module.
@isnad1 id=eq.4h5v.s7.d89c36503341 from=translated src=- shape=ee80f4e0 vocab=ee7169ed
-/
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

/--
@isnad1 id=tendsto.4h5v.s7.0059e13e2700 from=translated src=- shape=8102a0a2 vocab=e0345a87
-/
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
