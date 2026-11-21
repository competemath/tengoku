/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.LyapunovAtomless

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact measurable divisibility

This module isolates the exact scalar hypothesis used by finite-action
purification.  `HasExactDivisibility μ` says that every measurable set can
be cut measurably in any prescribed real proportion.

This file first develops the abstract property and elementary transport
lemmas.  The converse implication from finite `IsAtomlessMeasure` is proved,
without any standard-Borel assumption, in the extension module
`AtomlessDivisibility` via Sierpiński's theorem.  Here we also retain the
independent real-line bridges:

* finite atomless Borel measures on `ℝ` satisfy exact divisibility, by the CDF
  theorem in `LyapunovAtomless`;
* exact divisibility is invariant under measurable equivalences;
* a finite `IsAtomlessMeasure` base measurably equivalent to `ℝ` is exactly
  divisible, because atomlessness transports to the real line.

The final theorem constructs a finite measurable partition with prescribed
masses on every exactly divisible finite measure space.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RandomSetTheory

variable {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Every measurable set admits a measurable subset carrying any prescribed
fraction of its `measureReal` mass.  Applications in this module assume that
the measure is finite, so `measureReal` loses no information.-/
def HasExactDivisibility (μ : Measure Ω) : Prop :=
  ∀ (s : Set Ω), MeasurableSet s →
    ∀ {a : ℝ}, 0 ≤ a → a ≤ 1 →
      ∃ A : Set Ω, A ⊆ s ∧ MeasurableSet A ∧
        μ.real A = a * μ.real s

/-- Exact divisibility is stronger than the project's nonatomicity
property for finite measures.
@isnad1 id=isatomle.1h2v.s4.f14104477d3e from=translated src=- shape=d047bb62 vocab=b61a6e33
-/
theorem HasExactDivisibility.isAtomlessMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : HasExactDivisibility μ) :
    IsAtomlessMeasure μ := by
  intro s hs hspos
  obtain ⟨A, hAs, hA, hmeasure⟩ :=
    hμ s hs (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨A, hAs, hA, ?_, ?_⟩
  · apply (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ A)).mp
    change 0 < μ.real A
    rw [hmeasure]
    have hsreal : 0 < μ.real s :=
      ENNReal.toReal_pos hspos.ne' (measure_ne_top μ s)
    positivity
  · apply (ENNReal.toReal_lt_toReal (measure_ne_top μ A)
      (measure_ne_top μ s)).mp
    change μ.real A < μ.real s
    rw [hmeasure]
    have hsreal : 0 < μ.real s :=
      ENNReal.toReal_pos hspos.ne' (measure_ne_top μ s)
    linarith

/-- Restriction to a measurable set preserves exact divisibility.
@isnad1 id=hasexact.2h3v.s4.eeabe8ad3669 from=translated src=- shape=a6a6750d vocab=db7ace3f
-/
theorem HasExactDivisibility.restrict
    {μ : Measure Ω} (hμ : HasExactDivisibility μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    HasExactDivisibility (μ.restrict s) := by
  intro B hB a ha0 ha1
  obtain ⟨A, hABs, hA, hmeasure⟩ := hμ (B ∩ s) (hB.inter hs) ha0 ha1
  have hAs : A ⊆ s := hABs.trans inter_subset_right
  refine ⟨A, hABs.trans inter_subset_left, hA, ?_⟩
  rw [measureReal_restrict_apply hA, measureReal_restrict_apply hB,
    inter_eq_self_of_subset_left hAs]
  exact hmeasure

/-- `measureReal` of a measurable set under the pushforward by a measurable
equivalence.
@isnad1 id=eq.1h5v.s6.fd3c3497be14 from=translated src=- shape=d7b8d53d vocab=5b5b1513
-/
theorem measureReal_map_measurableEquiv_apply
    (μ : Measure Ω) (e : Ω ≃ᵐ Ω') {s : Set Ω'} (hs : MeasurableSet s) :
    (Measure.map e μ).real s = μ.real (e ⁻¹' s) := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable e.measurable.aemeasurable hs]

/-- `measureReal` is unchanged when a measurable set is transported through
a measurable equivalence.
@isnad1 id=eq.1h5v.s6.169df0878c25 from=translated src=- shape=2297fde1 vocab=7f1607cd
-/
theorem measureReal_map_measurableEquiv_image
    (μ : Measure Ω) (e : Ω ≃ᵐ Ω') {s : Set Ω} (hs : MeasurableSet s) :
    (Measure.map e μ).real (e '' s) = μ.real s := by
  rw [measureReal_map_measurableEquiv_apply μ e ((e.measurableSet_image).2 hs),
    Set.preimage_image_eq _ e.injective]

/-- Exact divisibility transports forward through a measurable equivalence.
@isnad1 id=hasexact.1h4v.s5.6478772a1738 from=translated src=- shape=091e9c9b vocab=5c9869c3
-/
theorem HasExactDivisibility.map_measurableEquiv
    {μ : Measure Ω} (hμ : HasExactDivisibility μ) (e : Ω ≃ᵐ Ω') :
    HasExactDivisibility (Measure.map e μ) := by
  intro s hs a ha0 ha1
  obtain ⟨A, hAs, hA, hmeasure⟩ := hμ (e ⁻¹' s) (e.measurable hs) ha0 ha1
  refine ⟨e '' A, ?_, (e.measurableSet_image).2 hA, ?_⟩
  · intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    exact hAs hxA
  · rw [measureReal_map_measurableEquiv_image μ e hA,
      measureReal_map_measurableEquiv_apply μ e hs, hmeasure]

/-- Exact divisibility is invariant under measurable equivalences.
@isnad1 id=iff.0h4v.s5.168b016f1664 from=translated src=- shape=f09ec903 vocab=5c9869c3
-/
theorem hasExactDivisibility_map_measurableEquiv_iff
    (μ : Measure Ω) (e : Ω ≃ᵐ Ω') :
    HasExactDivisibility (Measure.map e μ) ↔ HasExactDivisibility μ := by
  constructor
  · intro hmap s hs a ha0 ha1
    obtain ⟨B, hBes, hB, hmeasure⟩ :=
      hmap (e '' s) ((e.measurableSet_image).2 hs) ha0 ha1
    refine ⟨e ⁻¹' B, ?_, e.measurable hB, ?_⟩
    · intro x hx
      have hex : e x ∈ e '' s := hBes hx
      rcases hex with ⟨y, hy, hey⟩
      exact (e.injective hey).symm ▸ hy
    · have hpre : μ.real (e ⁻¹' B) = (Measure.map e μ).real B :=
        (measureReal_map_measurableEquiv_apply μ e hB).symm
      rw [hpre, hmeasure, measureReal_map_measurableEquiv_image μ e hs]
  · exact fun hμ ↦ hμ.map_measurableEquiv e

/-- Genuine atomlessness transports through measurable equivalences.
@isnad1 id=isatomle.1h4v.s5.7ce740566509 from=translated src=- shape=091e9c9b vocab=0c205118
-/
theorem IsAtomlessMeasure.map_measurableEquiv
    {μ : Measure Ω} (hμ : IsAtomlessMeasure μ) (e : Ω ≃ᵐ Ω') :
    IsAtomlessMeasure (Measure.map e μ) := by
  intro s hs hspos
  have hspos' : 0 < μ (e ⁻¹' s) := by
    simpa [Measure.map_apply_of_aemeasurable e.measurable.aemeasurable hs]
      using hspos
  obtain ⟨A, hAs, hA, hApos, hAlt⟩ := hμ (e ⁻¹' s) (e.measurable hs) hspos'
  refine ⟨e '' A, ?_, (e.measurableSet_image).2 hA, ?_, ?_⟩
  · intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    exact hAs hxA
  · simpa [Measure.map_apply_of_aemeasurable e.measurable.aemeasurable
      ((e.measurableSet_image).2 hA), Set.preimage_image_eq _ e.injective]
      using hApos
  · simpa [Measure.map_apply_of_aemeasurable e.measurable.aemeasurable
      ((e.measurableSet_image).2 hA),
      Measure.map_apply_of_aemeasurable e.measurable.aemeasurable hs,
      Set.preimage_image_eq _ e.injective] using hAlt

/-- The exact divisibility theorem already proved for finite Borel measures
on the real line, packaged in the abstract interface.
@isnad1 id=hasexact.0h1v.s4.044b833c7874 from=translated src=- shape=3305e152 vocab=f38fc781
-/
theorem hasExactDivisibility_real_of_nullSingletonClass
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    HasExactDivisibility μ := by
  intro s hs a ha0 ha1
  exact exists_measurable_subset_measureReal_eq_mul μ hs ha0 ha1

/-- A finite measure transported to a point-mass-free real Borel measure is
exactly divisible.
@isnad1 id=hasexact.0h3v.s5.e4863bc9dc81 from=translated src=- shape=827ddd80 vocab=57d20ebc
-/
theorem hasExactDivisibility_of_measurableEquiv_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (e : Ω ≃ᵐ ℝ)
    [NullSingletonClass (Measure.map e μ)] :
    HasExactDivisibility μ := by
  exact (hasExactDivisibility_map_measurableEquiv_iff μ e).mp
    (hasExactDivisibility_real_of_nullSingletonClass (Measure.map e μ))

/-- Honest bridge from the project's nonatomicity property: finite
atomlessness implies exact divisibility here only with the additional
assumption that the measurable base is equivalent to the real Borel line.
@isnad1 id=hasexact.1h3v.s4.1bd9bf294598 from=translated src=- shape=a59103dc vocab=94023022
-/
theorem hasExactDivisibility_of_atomless_measurableEquiv_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : IsAtomlessMeasure μ)
    (e : Ω ≃ᵐ ℝ) :
    HasExactDivisibility μ := by
  have hmapAtomless : IsAtomlessMeasure (Measure.map e μ) :=
    hμ.map_measurableEquiv e
  letI : NullSingletonClass (Measure.map e μ) :=
    hmapAtomless.toNullSingletonClass
  exact hasExactDivisibility_of_measurableEquiv_real μ e

/-! ## Exact finite measurable partitions -/

/-- A finite family of measurable sets which partitions `B`.-/
def IsMeasurableFinpartition (s : Finset ι)
    (B : Set Ω) (A : ι → Set Ω) : Prop :=
  (∀ i ∈ s, MeasurableSet (A i)) ∧
    (∀ i ∈ s, A i ⊆ B) ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) ∧
    (⋃ i ∈ s, A i) = B

/-- Exact finite measurable partition of a measurable set with prescribed
nonnegative masses on any exactly divisible finite measure space.
@isnad1 id=ex.4h6v.s7.fbc2d4623330 from=translated src=- shape=01c6a7e8 vocab=ed86059b
-/
theorem HasExactDivisibility.exists_isMeasurableFinpartition_measureReal_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : HasExactDivisibility μ)
    (s : Finset ι) (B : Set Ω) (hB : MeasurableSet B)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1) :
    ∃ A : ι → Set Ω, IsMeasurableFinpartition s B A ∧
      ∀ i ∈ s, μ.real (A i) = w i * μ.real B := by
  classical
  induction s using Finset.induction_on generalizing B w with
  | empty => simp at hsum
  | @insert a s ha ih =>
      let r : ℝ := ∑ i ∈ s, w i
      have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self a s)
      have hwr : ∀ i ∈ s, 0 ≤ w i := fun i hi ↦
        hw i (Finset.mem_insert_of_mem hi)
      have hr : 0 ≤ r := Finset.sum_nonneg hwr
      have hsum' : w a + r = 1 := by
        simpa [r, Finset.sum_insert ha] using hsum
      have hwa_le : w a ≤ 1 := by linarith
      by_cases hr0 : r = 0
      · have hwa1 : w a = 1 := by linarith
        have hwzero : ∀ i ∈ s, w i = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hwr).mp (by simpa [r] using hr0)
        let A : ι → Set Ω := fun i ↦ if i = a then B else ∅
        refine ⟨A, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · intro i hi
            by_cases hia : i = a
            · simp [A, hia, hB]
            · simp [A, hia]
          · intro i hi
            by_cases hia : i = a
            · simp [A, hia]
            · change (if i = a then B else ∅) ⊆ B
              simp [hia]
          · intro i hi j hj hij
            by_cases hia : i = a
            · by_cases hja : j = a
              · exact (hij (hia.trans hja.symm)).elim
              · simp [A, hia, hja]
            · simp [A, hia]
          · rw [Finset.set_biUnion_insert]
            simp only [A, ite_eq_left]
            have hrest : (⋃ i ∈ s, A i) = ∅ := by
              ext x
              simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
              rintro ⟨i, hi, hxi⟩
              have hia : i ≠ a := fun hEq ↦ ha (hEq ▸ hi)
              simp [A, hia] at hxi
            rw [hrest, union_empty]
        · intro i hi
          by_cases hia : i = a
          · subst i
            simp [A, hwa1]
          · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
            simp [A, hia, hwzero i his]
      · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
        obtain ⟨Aa, hAaB, hAa, hAaMeasure⟩ := hμ B hB hwa hwa_le
        let C : Set Ω := B \ Aa
        have hC : MeasurableSet C := hB.diff hAa
        have hCMeasure : μ.real C = r * μ.real B := by
          rw [show C = B \ Aa from rfl, measureReal_sdiff hAaB hAa, hAaMeasure]
          have hrEq : 1 - w a = r := by linarith [hsum']
          rw [← hrEq]
          ring
        let w' : ι → ℝ := fun i ↦ w i / r
        have hw' : ∀ i ∈ s, 0 ≤ w' i := by
          intro i hi
          exact div_nonneg (hwr i hi) (le_of_lt hrpos)
        have hsumw' : ∑ i ∈ s, w' i = 1 := by
          rw [← Finset.sum_div]
          simp only [r]
          exact div_self hr0
        obtain ⟨Ar, hArPart, hArMeasure⟩ := ih C hC w' hw' hsumw'
        rcases hArPart with ⟨hArMeas, hArSub, hArDisj, hArUnion⟩
        let A : ι → Set Ω := fun i ↦ if i = a then Aa else Ar i
        refine ⟨A, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · intro i hi
            by_cases hia : i = a
            · simpa [A, hia] using hAa
            · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
              simpa [A, hia] using (hArMeas i his)
          · intro i hi
            by_cases hia : i = a
            · simpa [A, hia] using hAaB
            · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
              simpa [A, hia] using (hArSub i his).trans Set.sdiff_subset
          · intro i hi j hj hij
            by_cases hia : i = a
            · by_cases hja : j = a
              · exact (hij (hia.trans hja.symm)).elim
              · subst i
                have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
                rw [show A a = Aa by simp [A], show A j = Ar j by simp [A, hja]]
                rw [Set.disjoint_left]
                intro x hxAa hxAr
                exact (hArSub j hjs hxAr).2 hxAa
            · by_cases hja : j = a
              · subst j
                have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
                rw [show A i = Ar i by simp [A, hia], show A a = Aa by simp [A]]
                rw [Set.disjoint_left]
                intro x hxAr hxAa
                exact (hArSub i his hxAr).2 hxAa
              · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
                have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
                simpa [A, hia, hja] using hArDisj i his j hjs hij
          · rw [Finset.set_biUnion_insert]
            simp only [A, ite_eq_left]
            have hrest : (⋃ i ∈ s, A i) = C := by
              calc
                (⋃ i ∈ s, A i) = ⋃ i ∈ s, Ar i := by
                  apply iUnion_congr
                  intro i
                  apply iUnion_congr
                  intro hi
                  have hia : i ≠ a := fun hEq ↦ ha (hEq ▸ hi)
                  simp [A, hia]
                _ = C := hArUnion
            rw [hrest]
            exact Set.union_sdiff_cancel hAaB
        · intro i hi
          by_cases hia : i = a
          · subst i
            simpa [A] using hAaMeasure
          · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
            rw [show A i = Ar i by simp [A, hia], hArMeasure i his, hCMeasure]
            simp only [w']
            field_simp

end RandomSetTheory
