/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation
import Tengoku.Randomsettheory.RandomSetTheory.SupportFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aumann expectations of finite-range correspondences

This file proves a closedness theorem on an arbitrary finite measure space,
rather than requiring the sample space itself to be finite.  A measurable
finite-regime correspondence has the form `ω ↦ K (p ω)`, where the regime
cells `{ω | p ω = i}` are measurable and the finitely many values `K i` are
nonempty closed convex sets.

Its Aumann expectation is exactly the weighted Minkowski sum

`∑ i, μ.real {ω | p ω = i} • K i`.

For compact values this gives compactness, hence closedness, before taking
any closure.  Null regime cells cause no problem: their contribution is the
singleton `{0}` because the corresponding value is assumed nonempty.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory Set
open scoped Pointwise BigOperators

noncomputable section

namespace RandomSetTheory

variable {Ω E ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The measurable cell associated with a regime.-/
def regimeCell (p : Ω → ι) (i : ι) : Set Ω := {ω | p ω = i}

/-- A correspondence taking one of finitely many prescribed values.-/
def finiteRegimeCorrespondence (p : Ω → ι) (K : ι → Set E) : Ω → Set E :=
  fun ω => K (p ω)

omit [MeasurableSpace Ω] in
/--
@isnad1 id=iff.0h5v.s4.5ff6cc8c7f7a from=translated src=- shape=f2e103e7 vocab=611f99f4
-/
@[simp]
theorem mem_regimeCell {p : Ω → ι} {i : ι} {ω : Ω} :
    ω ∈ regimeCell p i ↔ p ω = i :=
  Iff.rfl

omit [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] in
/--
@isnad1 id=eq.0h6v.s5.bec6b1c9a61d from=translated src=- shape=991f45ba vocab=f6d88711
-/
@[simp]
theorem finiteRegimeCorrespondence_apply (p : Ω → ι) (K : ι → Set E)
    (ω : Ω) : finiteRegimeCorrespondence p K ω = K (p ω) :=
  rfl

/-- The indicators of all regime cells form a finite partition of unity:
exactly the summand indexed by `p ω` survives.
@isnad1 id=eq.0h6v.s6.c700e0573cd1 from=translated src=- shape=b3fa4faa vocab=5747a285
-/
theorem sum_regimeCell_indicator [Fintype ι]
    (p : Ω → ι) (g : ι → Ω → E) (ω : Ω) :
    ∑ i, (regimeCell p i).indicator (g i) ω = g (p ω) ω := by
  classical
  rw [Finset.sum_eq_single (p ω)]
  · exact Set.indicator_of_mem (M := E)
      (s := regimeCell p (p ω)) (a := ω) rfl (g (p ω))
  · intro i _ hi
    exact Set.indicator_of_notMem
      (fun hmem : ω ∈ regimeCell p i => hi hmem.symm) (g i)
  · simp

/-- Finite measurable regime cells automatically give Effros measurability.
No closedness assumption on the finitely many values is needed for this
hitting-event statement.
@isnad1 id=iseffros.1h5v.s6.2d6c55c1e4e8 from=translated src=- shape=70f34474 vocab=90e358b2
-/
theorem effrosMeasurable_finiteRegimeCorrespondence
    [Fintype ι] [TopologicalSpace E]
    {p : Ω → ι} {K : ι → Set E}
    (hcell : ∀ i, MeasurableSet (regimeCell p i)) :
    RandomSet.IsEffrosMeasurable (finiteRegimeCorrespondence p K) := by
  classical
  intro U _hU
  have heq :
      {ω | (finiteRegimeCorrespondence p K ω ∩ U).Nonempty} =
        ⋃ i : ι, if (K i ∩ U).Nonempty then regimeCell p i else ∅ := by
    ext ω
    simp only [finiteRegimeCorrespondence_apply, mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hω
      refine ⟨p ω, ?_⟩
      rw [ite_eq_left hω]
      exact rfl
    · rintro ⟨i, hi⟩
      by_cases hKi : (K i ∩ U).Nonempty
      · rw [ite_eq_left hKi] at hi
        rw [mem_regimeCell] at hi
        rwa [hi]
      · rw [ite_eq_right hKi] at hi
        have : False := by simpa using hi
        exact this.elim
  rw [heq]
  exact MeasurableSet.iUnion fun i => by
    by_cases hi : (K i ∩ U).Nonempty
    · simpa [hi] using hcell i
    · simp only [hi, ite_false, MeasurableSet.empty]

/-- The integral over a measurable cell of a selection of a nonempty closed
convex set belongs to the measure of that cell times the set.  This is the
unnormalized finite-measure form of `Convex.set_average_mem`.
@isnad1 id=mem.5h6v.s8.959f01367dcc from=translated src=- shape=f20da2a3 vocab=486dadd5
-/
theorem setIntegral_mem_measureReal_smul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {A : Set Ω}
    {K : Set E} (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKne : K.Nonempty) {f : Ω → E}
    (hf : Integrable f μ)
    (hfK : ∀ᵐ ω ∂μ.restrict A, f ω ∈ K) :
    (∫ ω in A, f ω ∂μ) ∈ μ.real A • K := by
  by_cases hA0 : μ A = 0
  · obtain ⟨k, hk⟩ := hKne
    have hzeroMem : (0 : ℝ) • k ∈ (0 : ℝ) • K :=
      Set.smul_mem_smul_set hk
    have hintZero : (∫ ω in A, f ω ∂μ) = 0 := by
      rw [Measure.restrict_eq_zero.mpr hA0, integral_zero_measure]
    simpa [hintZero, measureReal_def, hA0] using hzeroMem
  · have havg : (⨍ ω in A, f ω ∂μ) ∈ K :=
      hKconv.set_average_mem hKclosed hA0 (measure_ne_top μ A) hfK hf.integrableOn
    have hscaled : μ.real A • (⨍ ω in A, f ω ∂μ) ∈ μ.real A • K :=
      Set.smul_mem_smul_set havg
    have hscaleEq :
        μ.real A • (⨍ ω in A, f ω ∂μ) = ∫ ω in A, f ω ∂μ := by
      simpa only [measureReal_restrict_apply_univ] using
        (measure_smul_average (μ.restrict A) f)
    rwa [hscaleEq] at hscaled

/-- Exact Aumann formula for a finite-range closed convex correspondence on
an arbitrary finite measure space.
@isnad1 id=eq.4h6v.s8.8bf74ff02428 from=translated src=- shape=f47fc6c3 vocab=69c6ded0
-/
theorem aumannExpectation_finiteRegimeCorrespondence
    [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : Ω → ι} {K : ι → Set E}
    (hcell : ∀ i, MeasurableSet (regimeCell p i))
    (hKconv : ∀ i, Convex ℝ (K i))
    (hKclosed : ∀ i, IsClosed (K i))
    (hKne : ∀ i, (K i).Nonempty) :
    aumannExpectation μ (finiteRegimeCorrespondence p K) =
      ∑ i, μ.real (regimeCell p i) • K i := by
  classical
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hfKi : ∀ i, ∀ᵐ ω ∂μ.restrict (regimeCell p i), f ω ∈ K i := by
      intro i
      rw [ae_restrict_iff' (hcell i)]
      filter_upwards [hf.2] with ω hsel hωi
      rw [finiteRegimeCorrespondence_apply] at hsel
      rw [mem_regimeCell] at hωi
      rwa [hωi] at hsel
    have hpiece : ∀ i, (∫ ω in regimeCell p i, f ω ∂μ) ∈
        μ.real (regimeCell p i) • K i := by
      intro i
      exact setIntegral_mem_measureReal_smul (hKconv i)
        (hKclosed i) (hKne i) hf.1 (hfKi i)
    have hdecomp :
        (∫ ω, f ω ∂μ) = ∑ i, ∫ ω in regimeCell p i, f ω ∂μ := by
      calc
        (∫ ω, f ω ∂μ) =
            ∫ ω, ∑ i, (regimeCell p i).indicator f ω ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with ω
              simpa using
                (sum_regimeCell_indicator p (fun _ => f) ω).symm
        _ = ∑ i, ∫ ω, (regimeCell p i).indicator f ω ∂μ :=
          integral_finsetSum Finset.univ fun i _ => hf.1.indicator (hcell i)
        _ = ∑ i, ∫ ω in regimeCell p i, f ω ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_indicator (hcell i)
    rw [hdecomp]
    exact Set.finsetSum_mem_finsetSum Finset.univ
      (fun i => μ.real (regimeCell p i) • K i)
      (fun i => ∫ ω in regimeCell p i, f ω ∂μ)
      (fun i _ => hpiece i)
  · rw [Set.mem_fintype_sum]
    rintro ⟨y, hy, hySum⟩
    have hex : ∀ i, ∃ k ∈ K i, μ.real (regimeCell p i) • k = y i := by
      intro i
      exact Set.mem_smul_set.mp (hy i)
    choose k hkK hky using hex
    let f : Ω → E := fun ω =>
      ∑ i, (regimeCell p i).indicator (fun _ => k i) ω
    have hfInt : Integrable f μ := by
      dsimp only [f]
      exact integrable_finsetSum Finset.univ fun i _ =>
        (integrable_const (k i)).indicator (hcell i)
    have hfSel : ∀ ω, f ω ∈ finiteRegimeCorrespondence p K ω := by
      intro ω
      have hfEq : f ω = k (p ω) := by
        exact sum_regimeCell_indicator p (fun i _ => k i) ω
      rw [finiteRegimeCorrespondence_apply, hfEq]
      exact hkK (p ω)
    refine ⟨f, ⟨hfInt, Filter.Eventually.of_forall hfSel⟩, ?_⟩
    calc
      (∫ ω, f ω ∂μ) =
          ∑ i, ∫ ω, (regimeCell p i).indicator (fun _ => k i) ω ∂μ := by
            dsimp only [f]
            exact integral_finsetSum Finset.univ fun i _ =>
              (integrable_const (k i)).indicator (hcell i)
      _ = ∑ i, μ.real (regimeCell p i) • k i := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_indicator_const (k i) (hcell i)
      _ = ∑ i, y i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hky i
      _ = x := hySum

/-- Compactness of the Aumann expectation for compact convex finite-range
correspondences on an arbitrary finite measure space.
@isnad1 id=iscompac.4h6v.s7.6fee7a0dc54e from=translated src=- shape=5b1e855a vocab=fcee6d10
-/
theorem aumannExpectation_isCompact_of_finiteRegime
    [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : Ω → ι} {K : ι → Set E}
    (hcell : ∀ i, MeasurableSet (regimeCell p i))
    (hKcompact : ∀ i, IsCompact (K i))
    (hKconv : ∀ i, Convex ℝ (K i))
    (hKne : ∀ i, (K i).Nonempty) :
    IsCompact (aumannExpectation μ (finiteRegimeCorrespondence p K)) := by
  rw [aumannExpectation_finiteRegimeCorrespondence hcell hKconv
    (fun i => (hKcompact i).isClosed) hKne]
  exact isCompact_finset_sum Finset.univ
    (fun i => μ.real (regimeCell p i) • K i)
    (fun i _ => (hKcompact i).smul (μ.real (regimeCell p i)))

/-- Closedness follows immediately from finite-range compactness.
@isnad1 id=isclosed.4h6v.s7.0d392f359b8a from=translated src=- shape=5d3efe0e vocab=fc270b29
-/
theorem aumannExpectation_isClosed_of_finiteRegime
    [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : Ω → ι} {K : ι → Set E}
    (hcell : ∀ i, MeasurableSet (regimeCell p i))
    (hKcompact : ∀ i, IsCompact (K i))
    (hKconv : ∀ i, Convex ℝ (K i))
    (hKne : ∀ i, (K i).Nonempty) :
    IsClosed (aumannExpectation μ (finiteRegimeCorrespondence p K)) :=
  (aumannExpectation_isCompact_of_finiteRegime hcell hKcompact hKconv hKne).isClosed

/-- Consequently the closure wrapper used by the general Aumann theory is
redundant for finite-range compact convex correspondences.
@isnad1 id=eq.4h6v.s7.2dd3fdd83389 from=translated src=- shape=d7431acf vocab=f80c9154
-/
theorem closure_aumannExpectation_eq_of_finiteRegime
    [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : Ω → ι} {K : ι → Set E}
    (hcell : ∀ i, MeasurableSet (regimeCell p i))
    (hKcompact : ∀ i, IsCompact (K i))
    (hKconv : ∀ i, Convex ℝ (K i))
    (hKne : ∀ i, (K i).Nonempty) :
    closure (aumannExpectation μ (finiteRegimeCorrespondence p K)) =
      aumannExpectation μ (finiteRegimeCorrespondence p K) :=
  (aumannExpectation_isClosed_of_finiteRegime hcell hKcompact hKconv hKne).closure_eq

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
