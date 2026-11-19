/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PairRefinement
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PairMass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing lines with small slice fibers

The balancing step first discards lines through low-multiplicity slice points.
A finite union bound retains half the line mass under the stated budget.
Multiplicities are always measured in the original line family.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

/--
@isnad1 id=eq.0h5v.s5.85a5fef13d4c from=translated src=- shape=67dedfc5 vocab=4def90ee
-/
theorem sliceMultiplicity_inter_preimage (a : ℝ) (G : Set (Line m))
    (B : Set (EuclideanSpace ℝ (Fin m))) (y : EuclideanSpace ℝ (Fin m)) :
    sliceMultiplicity a (G ∩ atHeight a ⁻¹' B) y = B.indicator (sliceMultiplicity a G) y := by
  by_cases hy : y ∈ B
  · rw [Set.indicator_of_mem hy]
    unfold sliceMultiplicity
    congr 1
    ext ξ
    simp [atHeight_lineAt, hy]
  · rw [Set.indicator_of_notMem hy]
    have he : lineAt a y ⁻¹' (G ∩ atHeight a ⁻¹' B) = ∅ := by
      ext ξ
      simp [atHeight_lineAt, hy]
    simp [sliceMultiplicity, he]

/--
@isnad1 id=eq.2h4v.s10.15c0840430ff from=translated src=- shape=decd1be3 vocab=b5adfb45
-/
theorem setLIntegral_sliceMultiplicity (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G)
    {B : Set (EuclideanSpace ℝ (Fin m))} (hB : MeasurableSet B) :
    (∫⁻ y in B, sliceMultiplicity a G y) = volume (G ∩ atHeight a ⁻¹' B) := by
  rw [← lintegral_indicator hB]
  simp_rw [← sliceMultiplicity_inter_preimage a G B]
  exact lintegral_sliceMultiplicity a (hG.inter (hB.preimage (by unfold atHeight; fun_prop)))

/--
@isnad1 id=le.1h4v.s9.8529412059a2 from=translated src=- shape=74d0634e vocab=a0db2dc9
-/
theorem volume_low_sliceMultiplicity_le (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G)
    (η : ℝ≥0∞) :
    volume (G ∩ {g | sliceMultiplicity a G (atHeight a g) < η}) ≤
      η * volume (atHeight a '' G) := by
  change volume (G ∩ atHeight a ⁻¹' {y | sliceMultiplicity a G y < η}) ≤ _
  rw [← setLIntegral_sliceMultiplicity a hG
    (measurableSet_lt (measurable_sliceMultiplicity a hG) measurable_const)]
  exact setLIntegral_lt_le_mul_measure (measurable_sliceMultiplicity a hG)
    (support_sliceMultiplicity_subset a G) η

/-- Lines passing only through fibers of original multiplicity at least the threshold.-/
noncomputable def denseLines (r : ι → ℝ) (I : Finset ι) (G : Set (Line m))
    (η : ℝ≥0∞) : Set (Line m) :=
  G ∩ ⋂ i ∈ I, {g | η ≤ sliceMultiplicity (r i) G (atHeight (r i) g)}

/--
@isnad1 id=le.0h6v.s5.ccc82848707a from=translated src=- shape=8314bab3 vocab=cfa521fc
-/
theorem denseLines_subset (r : ι → ℝ) (I : Finset ι) (G : Set (Line m)) (η : ℝ≥0∞) :
    denseLines r I G η ⊆ G := inter_subset_left

/--
@isnad1 id=measurab.1h6v.s7.a078a22afa75 from=translated src=- shape=848ddc1c vocab=8775c076
-/
theorem measurableSet_denseLines (r : ι → ℝ) (I : Finset ι)
    {G : Set (Line m)} (hG : MeasurableSet G) (η : ℝ≥0∞) :
    MeasurableSet (denseLines r I G η) :=
  hG.inter (I.measurableSet_biInter fun i _ ↦ measurableSet_le measurable_const
    ((measurable_sliceMultiplicity (r i) hG).comp (by unfold atHeight; fun_prop)))

/--
@isnad1 id=le.2h8v.s6.917cae7be6e2 from=translated src=- shape=f0c4c4ee vocab=f6ac5d27
-/
theorem le_sliceMultiplicity_of_mem_denseLines {r : ι → ℝ} {I : Finset ι}
    {G : Set (Line m)} {η : ℝ≥0∞} {g : Line m} (hg : g ∈ denseLines r I G η)
    {i : ι} (hi : i ∈ I) : η ≤ sliceMultiplicity (r i) G (atHeight (r i) g) :=
  mem_iInter.mp (mem_iInter.mp hg.2 i) hi

/--
@isnad1 id=le.0h6v.s6.d5cb5a070208 from=translated src=- shape=efffa742 vocab=4392b800
-/
theorem sdiff_denseLines_subset (r : ι → ℝ) (I : Finset ι) (G : Set (Line m)) (η : ℝ≥0∞) :
    G \ denseLines r I G η ⊆
      ⋃ i ∈ I, G ∩ {g | sliceMultiplicity (r i) G (atHeight (r i) g) < η} := by
  intro g hg
  by_contra h
  apply hg.2
  refine ⟨hg.1, mem_iInter.mpr fun i ↦ mem_iInter.mpr fun hi ↦ ?_⟩
  change η ≤ sliceMultiplicity (r i) G (atHeight (r i) g)
  exact le_of_not_gt fun hlt ↦ h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hg.1, hlt⟩⟩)

/--
@isnad1 id=le.1h6v.s9.d7f72e92b32a from=translated src=- shape=bf2b3686 vocab=908bc1d0
-/
theorem volume_sdiff_denseLines_le (r : ι → ℝ) (I : Finset ι)
    {G : Set (Line m)} (hG : MeasurableSet G) (η : ℝ≥0∞) :
    volume (G \ denseLines r I G η) ≤ ∑ i ∈ I, η * volume (atHeight (r i) '' G) := by
  calc
    _ ≤ volume (⋃ i ∈ I, G ∩ {g | sliceMultiplicity (r i) G (atHeight (r i) g) < η}) :=
      measure_mono (sdiff_denseLines_subset r I G η)
    _ ≤ ∑ i ∈ I, volume (G ∩ {g | sliceMultiplicity (r i) G (atHeight (r i) g) < η}) :=
      measure_biUnion_finset_le I _
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ volume_low_sliceMultiplicity_le (r i) hG η

/--
@isnad1 id=le.2h7v.s10.e9cf0b8a45db from=translated src=- shape=050e5569 vocab=639d43d4
-/
theorem volume_sdiff_denseLines_le_card (r : ι → ℝ) (I : Finset ι)
    {G : Set (Line m)} (hG : MeasurableSet G) (η N : ℝ≥0∞)
    (hN : ∀ i ∈ I, volume (atHeight (r i) '' G) ≤ N) :
    volume (G \ denseLines r I G η) ≤ I.card * η * N := by
  refine (volume_sdiff_denseLines_le r I hG η).trans ?_
  calc
    _ ≤ ∑ i ∈ I, η * N :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul le_rfl (hN i hi) bot_le bot_le
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

/--
@isnad1 id=le.4h7v.s11.1cb8564af828 from=translated src=- shape=5030f716 vocab=f6394094
-/
theorem half_volume_le_volume_denseLines (r : ι → ℝ) (I : Finset ι)
    {G : Set (Line m)} (hG : MeasurableSet G) (hfin : volume G ≠ ∞) (η N : ℝ≥0∞)
    (hN : ∀ i ∈ I, volume (atHeight (r i) '' G) ≤ N)
    (hbudget : I.card * η * N ≤ volume G / 2) :
    volume G / 2 ≤ volume (denseLines r I G η) := by
  have h := measure_le_inter_add_sdiff volume G (denseLines r I G η)
  rw [inter_eq_right.mpr (denseLines_subset r I G η)] at h
  have hloss := (volume_sdiff_denseLines_le_card r I hG η N hN).trans hbudget
  apply ENNReal.le_of_add_le_add_right (ne_top_of_le_ne_top hfin ENNReal.half_le_self)
  rw [ENNReal.add_halves]
  exact h.trans (add_le_add le_rfl hloss)

end NKBesicovitch.Projection
