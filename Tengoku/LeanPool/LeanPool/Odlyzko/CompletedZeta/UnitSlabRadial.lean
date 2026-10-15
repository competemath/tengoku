/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.UnitSlabTranslation

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units Set
  dirichletUnitTheorem

namespace NumberField.Odlyzko

open mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- A nonnegative radial half space used in the Odlyzko-bound argument. -/
def nonnegativeRadialHalfSpace :
    Set (mixedEmbedding.realSpace K) :=
  {y | 0 ≤ y w₀}

open Classical in
/-- A negative radial half space used in the Odlyzko-bound argument. -/
def negativeRadialHalfSpace :
    Set (mixedEmbedding.realSpace K) :=
  {y | y w₀ < 0}

open Classical in
/-- A positive radial half space used in the Odlyzko-bound argument. -/
def positiveRadialHalfSpace :
    Set (mixedEmbedding.realSpace K) :=
  {y | 0 < y w₀}

open Classical in
/-- A nonnegative unit fundamental param set used in the Odlyzko-bound argument. -/
def nonnegativeUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  unitFundamentalParamSet K ∩ nonnegativeRadialHalfSpace (K := K)

open Classical in
/-- A negative unit fundamental param set used in the Odlyzko-bound argument. -/
def negativeUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  unitFundamentalParamSet K ∩ negativeRadialHalfSpace (K := K)

open Classical in
/-- A positive unit fundamental param set used in the Odlyzko-bound argument. -/
def positiveUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  unitFundamentalParamSet K ∩ positiveRadialHalfSpace (K := K)

open Classical in
/--
@isnad1 id=measurab.0h1v.s4.1f4c8d8fec47 from=translated src=- shape=da9a72aa vocab=46ce9834
-/
theorem measurableSet_negativeRadialHalfSpace :
    MeasurableSet (negativeRadialHalfSpace (K := K)) :=
  measurableSet_lt (measurable_pi_apply w₀) measurable_const

open Classical in
/--
@isnad1 id=measurab.0h1v.s4.2c6b3863adbf from=translated src=- shape=da9a72aa vocab=2e6870ad
-/
theorem measurableSet_positiveRadialHalfSpace :
    MeasurableSet (positiveRadialHalfSpace (K := K)) :=
  measurableSet_lt measurable_const (measurable_pi_apply w₀)

open Classical in
/--
@isnad1 id=measurab.0h1v.s4.e3fb295faffd from=translated src=- shape=da9a72aa vocab=01ef98ed
-/
theorem measurableSet_negativeUnitFundamentalParamSet :
    MeasurableSet (negativeUnitFundamentalParamSet (K := K)) :=
  measurableSet_unitFundamentalParamSet.inter
    measurableSet_negativeRadialHalfSpace

open Classical in
/--
@isnad1 id=measurab.0h1v.s4.60cf1eb49938 from=translated src=- shape=da9a72aa vocab=5d26fd97
-/
theorem measurableSet_positiveUnitFundamentalParamSet :
    MeasurableSet (positiveUnitFundamentalParamSet (K := K)) :=
  measurableSet_unitFundamentalParamSet.inter
    measurableSet_positiveRadialHalfSpace

open Classical in
/--
@isnad1 id=disjoint.0h1v.s6.77271db85e49 from=translated src=- shape=6746b013 vocab=2d1dbcb5
-/
theorem disjoint_nonnegative_negativeUnitFundamentalParamSet :
    Disjoint (nonnegativeUnitFundamentalParamSet (K := K))
      (negativeUnitFundamentalParamSet (K := K)) := by
  rw [Set.disjoint_left]
  intro y hy hny
  exact (not_lt_of_ge
    (show 0 ≤ y w₀ from hy.2))
    (show y w₀ < 0 from hny.2)

open Classical in
/--
@isnad1 id=eq.0h1v.s5.96ce0bd13bda from=translated src=- shape=858cd761 vocab=5416dff0
-/
theorem union_nonnegative_negativeUnitFundamentalParamSet :
    nonnegativeUnitFundamentalParamSet (K := K) ∪
        negativeUnitFundamentalParamSet (K := K) =
      unitFundamentalParamSet K := by
  ext y
  simp only [nonnegativeUnitFundamentalParamSet,
    negativeUnitFundamentalParamSet, nonnegativeRadialHalfSpace,
    negativeRadialHalfSpace, Set.mem_union, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  grind

open Classical in
/--
@isnad1 id=eq.1h3v.s8.f61b65f17245 from=translated src=- shape=b922fe60 vocab=bbf44444
-/
theorem setIntegral_unitFundamentalParamSet_eq_add_radialHalves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : IntegrableOn f (unitFundamentalParamSet K)) :
    (∫ y in unitFundamentalParamSet K, f y) =
      (∫ y in nonnegativeUnitFundamentalParamSet (K := K), f y) +
        ∫ y in negativeUnitFundamentalParamSet (K := K), f y := by
  rw [← union_nonnegative_negativeUnitFundamentalParamSet (K := K)]
  exact setIntegral_union
    disjoint_nonnegative_negativeUnitFundamentalParamSet
    measurableSet_negativeUnitFundamentalParamSet
    (hf.mono_set Set.inter_subset_left)
    (hf.mono_set Set.inter_subset_left)

open Classical in
/-- A neg unit fundamental param set used in the Odlyzko-bound argument. -/
def negUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  (fun y ↦ -y) ⁻¹' unitFundamentalParamSet K

open Classical in
/--
@isnad1 id=measurab.0h1v.s4.8cc75cd4f9af from=translated src=- shape=da9a72aa vocab=bc792c38
-/
theorem measurableSet_negUnitFundamentalParamSet :
    MeasurableSet (negUnitFundamentalParamSet (K := K)) :=
  measurable_neg measurableSet_unitFundamentalParamSet

open Classical in
/--
@isnad1 id=isaddfun.0h1v.s9.d97670f2daa8 from=translated src=- shape=35b8c568 vocab=d99dc14e
-/
theorem isAddFundamentalDomain_negUnitFundamentalParamSet :
    IsAddFundamentalDomain (unitCoordinateLattice (K := K))
      (negUnitFundamentalParamSet (K := K)) volume := by
  apply IsAddFundamentalDomain.mk'
    measurableSet_negUnitFundamentalParamSet.nullMeasurableSet
  intro x
  obtain ⟨h, hh, huniq⟩ :=
    existsUnique_vadd_mem_unitFundamentalParamSet (K := K) (-x)
  let g : unitCoordinateLattice (K := K) := -h
  refine ⟨g, ?_, ?_⟩
  · change -((g : mixedEmbedding.realSpace K) + x) ∈
      unitFundamentalParamSet K
    simpa [g, add_comm] using hh
  · intro g' hg'
    have hneg :
        ((-g' : unitCoordinateLattice (K := K)) :
            mixedEmbedding.realSpace K) + -x ∈
          unitFundamentalParamSet K := by
      change -((g' : mixedEmbedding.realSpace K) + x) ∈
        unitFundamentalParamSet K at hg'
      simpa only [AddSubgroup.coe_neg, neg_add_rev, add_comm] using hg'
    have heq := huniq (-g') hneg
    simpa [g] using congrArg Neg.neg heq

open Classical in
/--
@isnad1 id=eq.1h3v.s8.2b41e34dfc66 from=translated src=- shape=c83036eb vocab=489e784f
-/
theorem setIntegral_negUnitFundamentalParamSet_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x) :
    (∫ y in negUnitFundamentalParamSet (K := K), f y) =
      ∫ y in unitFundamentalParamSet K, f y :=
  (isAddFundamentalDomain_negUnitFundamentalParamSet (K := K)).setIntegral_eq
    isAddFundamentalDomain_unitFundamentalParamSet hf

open Classical in
/--
@isnad1 id=eq.0h3v.s7.18a332a90bbe from=translated src=- shape=3b4f7824 vocab=c51fa173
-/
theorem setIntegral_positive_comp_neg_eq_negSlab_negative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E) :
    (∫ y in positiveUnitFundamentalParamSet (K := K), f (-y)) =
      ∫ y in negUnitFundamentalParamSet (K := K) ∩
        negativeRadialHalfSpace (K := K), f y := by
  have h := measurableEmbedding_neg.setIntegral_map
    (μ := (volume : Measure (mixedEmbedding.realSpace K))) f
    (negUnitFundamentalParamSet (K := K) ∩
      negativeRadialHalfSpace (K := K))
  rw [Measure.map_neg_eq_self] at h
  have hpreimage :
      (fun y : mixedEmbedding.realSpace K ↦ -y) ⁻¹'
          (negUnitFundamentalParamSet (K := K) ∩
            negativeRadialHalfSpace (K := K)) =
        positiveUnitFundamentalParamSet (K := K) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff,
      negUnitFundamentalParamSet, negativeRadialHalfSpace,
      positiveUnitFundamentalParamSet, positiveRadialHalfSpace,
      Set.mem_ofPred_eq, Pi.neg_apply, neg_neg, neg_lt_zero]
  simp_all

open Classical in
/--
@isnad1 id=eq.1h3v.s8.9851b877234f from=translated src=- shape=85dcedb0 vocab=3055f43c
-/
theorem setIntegral_negative_eq_positive_comp_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x) :
    (∫ y in negativeUnitFundamentalParamSet (K := K), f y) =
      ∫ y in positiveUnitFundamentalParamSet (K := K), f (-y) := by
  let F := (negativeRadialHalfSpace (K := K)).indicator f
  have hF : ∀ (g : unitCoordinateLattice (K := K)) x,
      F ((g : mixedEmbedding.realSpace K) + x) = F x := by
    intro g x
    by_cases hx : x ∈ negativeRadialHalfSpace (K := K)
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∈
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx, hf]
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∉
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx]
  have hfund :=
    setIntegral_negUnitFundamentalParamSet_eq F hF
  rw [setIntegral_indicator measurableSet_negativeRadialHalfSpace,
    setIntegral_indicator measurableSet_negativeRadialHalfSpace] at hfund
  change (∫ y in unitFundamentalParamSet K ∩
      negativeRadialHalfSpace (K := K), f y) =
    ∫ y in positiveUnitFundamentalParamSet (K := K), f (-y)
  rw [setIntegral_positive_comp_neg_eq_negSlab_negative]
  simp_all

open Classical in
/--
@isnad1 id=iff.1h3v.s8.c7d5545839a6 from=translated src=- shape=4c76106e vocab=6618b01d
-/
theorem integrableOn_negative_iff_positive_comp_neg
    {E : Type*} [NormedAddCommGroup E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x) :
    IntegrableOn f (negativeUnitFundamentalParamSet (K := K)) ↔
      IntegrableOn (fun y ↦ f (-y))
        (positiveUnitFundamentalParamSet (K := K)) := by
  let F := (negativeRadialHalfSpace (K := K)).indicator f
  have hF : ∀ (g : unitCoordinateLattice (K := K)) x,
      F ((g : mixedEmbedding.realSpace K) + x) = F x := by
    intro g x
    by_cases hx : x ∈ negativeRadialHalfSpace (K := K)
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∈
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx, hf]
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∉
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx]
  have hpreimage :
      (fun y : mixedEmbedding.realSpace K ↦ -y) ⁻¹'
          (negUnitFundamentalParamSet (K := K) ∩
            negativeRadialHalfSpace (K := K)) =
        positiveUnitFundamentalParamSet (K := K) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff,
      negUnitFundamentalParamSet, negativeRadialHalfSpace,
      positiveUnitFundamentalParamSet, positiveRadialHalfSpace,
      Set.mem_ofPred_eq, Pi.neg_apply, neg_neg, neg_lt_zero]
  constructor
  · intro hneg
    have hFstandard : IntegrableOn F (unitFundamentalParamSet K) := by
      apply IntegrableOn.congr_fun
        (hneg.integrable_indicator
          measurableSet_negativeUnitFundamentalParamSet).integrableOn
        _ measurableSet_unitFundamentalParamSet
      intro y hy
      by_cases hrad : y ∈ negativeRadialHalfSpace (K := K)
      · simp [F, negativeUnitFundamentalParamSet, hy, hrad]
      · simp [F, negativeUnitFundamentalParamSet, hrad]
    have hFneg :
        IntegrableOn F (negUnitFundamentalParamSet (K := K)) :=
      ((isAddFundamentalDomain_unitFundamentalParamSet).integrableOn_iff
        (isAddFundamentalDomain_negUnitFundamentalParamSet (K := K)) hF).mp
        hFstandard
    have hfneg :
        IntegrableOn f
          (negUnitFundamentalParamSet (K := K) ∩
            negativeRadialHalfSpace (K := K)) := by
      apply IntegrableOn.congr_fun
        (hFneg.mono_set Set.inter_subset_left)
        _ (measurableSet_negUnitFundamentalParamSet.inter
          measurableSet_negativeRadialHalfSpace)
      intro y hy
      simp [F, hy.2]
    have hmap :=
      (Measure.measurePreserving_neg
        (volume : Measure (mixedEmbedding.realSpace K))).integrableOn_comp_preimage
        measurableEmbedding_neg
        (f := f)
        (s := negUnitFundamentalParamSet (K := K) ∩
          negativeRadialHalfSpace (K := K))
    rw [hpreimage] at hmap
    exact hmap.mpr hfneg
  · intro hreflect
    have hmap :=
      (Measure.measurePreserving_neg
        (volume : Measure (mixedEmbedding.realSpace K))).integrableOn_comp_preimage
        measurableEmbedding_neg
        (f := f)
        (s := negUnitFundamentalParamSet (K := K) ∩
          negativeRadialHalfSpace (K := K))
    rw [hpreimage] at hmap
    have hfneg := hmap.mp hreflect
    have hFneg :
        IntegrableOn F (negUnitFundamentalParamSet (K := K)) := by
      have hindicator :
          Integrable
            ((negUnitFundamentalParamSet (K := K) ∩
              negativeRadialHalfSpace (K := K)).indicator f) :=
        hfneg.integrable_indicator
          (measurableSet_negUnitFundamentalParamSet.inter
            measurableSet_negativeRadialHalfSpace)
      apply IntegrableOn.congr_fun hindicator.integrableOn
        _ measurableSet_negUnitFundamentalParamSet
      intro y hy
      by_cases hrad : y ∈ negativeRadialHalfSpace (K := K)
      · simp [F, hy, hrad]
      · simp [F, hrad]
    have hFstandard :
        IntegrableOn F (unitFundamentalParamSet K) :=
      ((isAddFundamentalDomain_negUnitFundamentalParamSet (K := K)).integrableOn_iff
        isAddFundamentalDomain_unitFundamentalParamSet hF).mp hFneg
    apply IntegrableOn.congr_fun
      (hFstandard.mono_set Set.inter_subset_left)
      _ measurableSet_negativeUnitFundamentalParamSet
    intro y hy
    simp [F, hy.2]

open Classical in
/--
@isnad1 id=eq.2h4v.s8.f0c3f630ec27 from=translated src=- shape=42987625 vocab=cae295f1
-/
theorem setIntegral_positiveUnitFundamentalParamSet_add_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x)
    (a : mixedEmbedding.realSpace K) (ha : a w₀ = 0) :
    (∫ x in positiveUnitFundamentalParamSet (K := K), f (x + a)) =
      ∫ x in positiveUnitFundamentalParamSet (K := K), f x := by
  let P := (positiveRadialHalfSpace (K := K)).indicator f
  have hP : ∀ (g : unitCoordinateLattice (K := K)) x,
      P ((g : mixedEmbedding.realSpace K) + x) = P x := by
    intro g x
    by_cases hx : x ∈ positiveRadialHalfSpace (K := K)
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∈
            positiveRadialHalfSpace (K := K) := by
        simpa [positiveRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [P, hx, hgx, hf]
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∉
            positiveRadialHalfSpace (K := K) := by
        simpa [positiveRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [P, hx, hgx]
  have hPa (x : mixedEmbedding.realSpace K) :
      P (x + a) =
        (positiveRadialHalfSpace (K := K)).indicator
          (fun y ↦ f (y + a)) x := by
    have hmem :
        x + a ∈ positiveRadialHalfSpace (K := K) ↔
          x ∈ positiveRadialHalfSpace (K := K) := by
      simp [positiveRadialHalfSpace, ha]
    by_cases hx : x ∈ positiveRadialHalfSpace (K := K)
    · simp [P, hx, hmem.mpr hx]
    · have hxa : x + a ∉ positiveRadialHalfSpace (K := K) :=
        fun h ↦ hx (hmem.mp h)
      simp [P, hx, hxa]
  calc
    (∫ x in positiveUnitFundamentalParamSet (K := K), f (x + a)) =
        ∫ x in unitFundamentalParamSet K, P (x + a) := by
      rw [show positiveUnitFundamentalParamSet (K := K) =
          unitFundamentalParamSet K ∩
            positiveRadialHalfSpace (K := K) by rfl,
        ← setIntegral_indicator measurableSet_positiveRadialHalfSpace]
      simp_all
    _ = ∫ x in unitFundamentalParamSet K, P x :=
      setIntegral_unitFundamentalParamSet_add_eq P hP a
    _ = ∫ x in positiveUnitFundamentalParamSet (K := K), f x := by
      rw [show positiveUnitFundamentalParamSet (K := K) =
          unitFundamentalParamSet K ∩
            positiveRadialHalfSpace (K := K) by rfl,
        ← setIntegral_indicator measurableSet_positiveRadialHalfSpace]

end NumberField.Odlyzko
