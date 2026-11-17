/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.PartialBorel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable least selection for finite ordered codomains

For a measurable relation whose codomain is finite and linearly ordered, its domain is measurable
and the least point in each nonempty vertical section is a measurable partial selector.  The
resulting partial graph uniformizes the original relation on its exact domain and has an exact
standard-Borel code under the usual standard-Borel hypotheses.

This is a genuine measurable-selection theorem, but only for a finite ordered codomain.  It does
not assert compact- or closed-valued measurable selection in an arbitrary Polish target.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- The finite set representing a vertical section.-/
noncomputable def finiteSection [Fintype Y] (R : Set (X × Y)) (x : X) : Finset Y := by
  classical
  exact Finset.univ.filter fun y => (x, y) ∈ R

@[simp] theorem mem_finiteSection [Fintype Y] {R : Set (X × Y)} {x : X} {y : Y} :
    y ∈ finiteSection R x ↔ (x, y) ∈ R := by
  classical
  simp [finiteSection]

theorem finiteSection_nonempty [Fintype Y] (R : Set (X × Y))
    (x : relationDomain R) : (finiteSection R x.1).Nonempty := by
  obtain ⟨y, hy⟩ := x.property
  exact ⟨y, mem_finiteSection.mpr hy⟩

/-- The least value in each nonempty finite vertical section.-/
noncomputable def finiteLeastSelector [Fintype Y] [LinearOrder Y] (R : Set (X × Y)) :
    relationDomain R → Y := fun x =>
  (finiteSection R x.1).min' (finiteSection_nonempty R x)

/-- The finite least selector chooses a point of the original relation.-/
theorem finiteLeastSelector_mem [Fintype Y] [LinearOrder Y] (R : Set (X × Y))
    (x : relationDomain R) : (x.1, finiteLeastSelector R x) ∈ R := by
  exact mem_finiteSection.mp
    (Finset.min'_mem (finiteSection R x.1) (finiteSection_nonempty R x))

/-- Exact minimum semantics for the finite selector.-/
theorem finiteLeastSelector_eq_iff [Fintype Y] [LinearOrder Y] (R : Set (X × Y))
    (x : relationDomain R) (y : Y) :
    finiteLeastSelector R x = y ↔
      (x.1, y) ∈ R ∧ ∀ z, (x.1, z) ∈ R → y ≤ z := by
  classical
  change (finiteSection R x.1).min' (finiteSection_nonempty R x) = y ↔ _
  rw [Finset.min'_eq_iff]
  simp only [mem_finiteSection]

/-- A measurable relation with finite codomain has measurable projection.-/
theorem MeasurableSet.measurableSet_relationDomain_of_finite
    [MeasurableSpace X] [MeasurableSpace Y] [Finite Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) : MeasurableSet (relationDomain R) := by
  have hdomain : relationDomain R = ⋃ y, DescriptiveSetTheory.horizontalSection R y := by
    ext x
    simp [relationDomain]
  rw [hdomain]
  exact MeasurableSet.iUnion fun y =>
    DescriptiveSetTheory.MeasurableSet.horizontalSection hR y

/-- The least selector of a measurable finite-codomain relation is measurable on its native
subtype domain.-/
theorem MeasurableSet.measurable_finiteLeastSelector
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype Y] [LinearOrder Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) : Measurable (finiteLeastSelector R) := by
  apply measurable_to_countable'
  intro y
  have hEq : finiteLeastSelector R ⁻¹' {y} =
      {x : relationDomain R |
        (x.1, y) ∈ R ∧ ∀ z, (x.1, z) ∈ R → y ≤ z} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, finiteLeastSelector_eq_iff]
  rw [hEq]
  apply ((DescriptiveSetTheory.MeasurableSet.horizontalSection hR y).preimage
    measurable_subtype_coe).inter
  have hForall : {x : relationDomain R |
      ∀ z, (x.1, z) ∈ R → y ≤ z} =
      ⋂ z, {x : relationDomain R | (x.1, z) ∈ R → y ≤ z} := by
    ext x
    simp
  change MeasurableSet ({x : relationDomain R |
    ∀ z, (x.1, z) ∈ R → y ≤ z} : Set (relationDomain R))
  rw [hForall]
  apply MeasurableSet.iInter
  intro z
  by_cases hyz : y ≤ z
  · convert MeasurableSet.univ using 1
    ext x
    simp [hyz]
  · convert ((DescriptiveSetTheory.MeasurableSet.horizontalSection hR z).preimage
      measurable_subtype_coe).compl using 1
    ext x
    simp [hyz]

/-- The least-selector graph uniformizes the original finite-codomain relation exactly.-/
theorem uniformizes_partialGraph_finiteLeastSelector [Fintype Y] [LinearOrder Y]
    (R : Set (X × Y)) :
    Uniformizes R (partialGraph (relationDomain R) (finiteLeastSelector R)) :=
  uniformizes_partialGraph_iff.mpr ⟨rfl, finiteLeastSelector_mem R⟩

/-- The measurable least selector has an exact standard-Borel graph code.-/
theorem MeasurableSet.exists_standardBorelCode_partialGraph_finiteLeastSelector
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Fintype Y] [LinearOrder Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) :
    ∃ c : StandardBorelCode (X × Y),
      c.eval = partialGraph (relationDomain R) (finiteLeastSelector R) :=
  exists_standardBorelCode_partialGraph
    (DescriptiveSetTheory.MeasurableSet.measurableSet_relationDomain_of_finite hR)
    (DescriptiveSetTheory.MeasurableSet.measurable_finiteLeastSelector hR)

end DescriptiveSetTheory
