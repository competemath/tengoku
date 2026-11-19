/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.ParentCorners

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting an inner pair family to corners

Swapping the two outer slopes interchanges the junctions and preserves the
intrinsic measure. Thus the parent counting identity also counts the corners
attached to each retained or discarded inner pair.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Corners with first line in `A` and inner pair in `W`.-/
def innerCorners (a b : ℝ) (A : Set (Line m)) (W : Set (PairCoordinates m)) :
    Set (CornerCoordinates m) := {p | cornerFirst a p ∈ A ∧ cornerInner b p ∈ W}

/--
@isnad1 id=measurep.0h1v.s10.d6cb1458aef0 from=translated src=- shape=35c8f3a3 vocab=98bf7919
-/
theorem measurePreserving_swap_cornerSlopes :
    MeasurePreserving (fun p : CornerCoordinates m ↦ (p.1, (p.2.2, p.2.1))) volume volume := by
  simpa [Prod.map_def, Prod.swap, Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure (Line m))).prod
      (Measure.measurePreserving_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
        (ν := (volume : Measure (EuclideanSpace ℝ (Fin m)))))

/--
@isnad1 id=eq.0h5v.s6.3bff09ac9184 from=translated src=- shape=54809311 vocab=830f217a
-/
theorem innerCorners_eq_preimage_parentCorners (a b : ℝ) (A : Set (Line m))
    (W : Set (PairCoordinates m)) :
    innerCorners a b A W =
      (fun p : CornerCoordinates m ↦ (p.1, (p.2.2, p.2.1))) ⁻¹' parentCorners b a W A := by
  ext p
  simp [innerCorners, parentCorners, cornerFirst, cornerLast, cornerInner, cornerParent, and_comm]

/--
@isnad1 id=measurab.2h5v.s8.c19d946798aa from=translated src=- shape=675028a3 vocab=94216204
-/
theorem measurableSet_innerCorners (a b : ℝ) {A : Set (Line m)} (hA : MeasurableSet A)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) :
    MeasurableSet (innerCorners a b A W) := by
  rw [innerCorners_eq_preimage_parentCorners]
  exact (measurableSet_parentCorners b a hW hA).preimage
    measurePreserving_swap_cornerSlopes.measurable

/--
@isnad1 id=eq.2h5v.s11.063d686a9985 from=translated src=- shape=47994b09 vocab=2eb301be
-/
theorem volume_innerCorners (a b : ℝ) {A : Set (Line m)} (hA : MeasurableSet A)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) :
    volume (innerCorners a b A W) =
      ∫⁻ p in W, sliceMultiplicity a A (atHeight a (lineAt b p.1 p.2.1)) := by
  rw [innerCorners_eq_preimage_parentCorners,
    measurePreserving_swap_cornerSlopes.measure_preimage
      (measurableSet_parentCorners b a hW hA).nullMeasurableSet,
    volume_parentCorners b a hW hA]

/-- Each specified inner pair has exactly the prescribed mass of first companions.
@isnad1 id=eq.3h6v.s11.ac0fa0e0e3c4 from=translated src=- shape=8b5f335d vocab=cafa7254
-/
theorem volume_innerCorners_of_constant_mass (a b : ℝ) {A : Set (Line m)}
    (hA : MeasurableSet A) {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (η : ℝ≥0∞)
    (hη : ∀ p ∈ W, sliceMultiplicity a A (atHeight a (lineAt b p.1 p.2.1)) = η) :
    volume (innerCorners a b A W) = volume W * η := by
  rw [volume_innerCorners a b hA hW]
  calc
    _ = ∫⁻ _p in W, η := setLIntegral_congr_fun hW hη
    _ = _ := by simp [mul_comm]

/--
@isnad1 id=eq.1h7v.s6.5c506b60d4b0 from=translated src=- shape=dbf7f65f vocab=af9da87f
-/
theorem innerCorners_eq_inter {a b : ℝ} {W : Set (PairCoordinates m)}
    {G₀ A B : Set (Line m)} (hW : W ⊆ companionPairs b G₀ B) :
    innerCorners a b A W = companionCorners a b G₀ A B ∩ cornerInner b ⁻¹' W := by
  ext p
  constructor
  · intro hp
    have h := hW hp.2
    refine ⟨⟨?_, hp.1, h.2⟩, hp.2⟩
    simpa only [first_cornerInner] using h.1
  · intro hp
    exact ⟨hp.1.2.1, hp.2⟩

end NKBesicovitch.Projection
