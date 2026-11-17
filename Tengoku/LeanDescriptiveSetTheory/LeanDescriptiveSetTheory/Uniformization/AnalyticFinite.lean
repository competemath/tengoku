/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Regularity.Baire.Analytic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.FiniteSelection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Baire-regular uniformization of analytic finite-target relations

For an analytic relation with a finite linearly ordered codomain, the least point of every nonempty
section gives an exact uniformization.  Every ambient preimage of the resulting partial selector has
the Baire property: it is a finite union of finite Boolean combinations of analytic horizontal
sections.

`HasBaireMeasurableAmbientPreimages` is deliberately explicit.  It measures a partial function by
the subsets of the ambient source selected over its native domain, rather than silently treating an
arbitrary analytic domain as an open subspace.  The theorem is restricted to finite targets and is
not the general Jankov--von Neumann analytic uniformization theorem.
-/

open Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- Every target preimage of a partial map, viewed back in the ambient source, has the Baire
property.  Quantifying over all target sets is natural for the finite/discrete targets used here.-/
def HasBaireMeasurableAmbientPreimages [TopologicalSpace X] (s : Set X) (f : s → Y) : Prop :=
  ∀ t : Set Y, BaireMeasurableSet {x | ∃ hx : x ∈ s, f ⟨x, hx⟩ ∈ t}

/-- Horizontal sections of an analytic relation are analytic under the exact Polish/Hausdorff
hypotheses needed by analytic continuous preimages.
@isnad1 id=analytic.1h4v.s5.c8c5849a42cf from=translated src=- shape=a0d37361 vocab=abaa82fb
-/
theorem _root_.MeasureTheory.AnalyticSet.horizontalSection
    [TopologicalSpace X] [PolishSpace X] [TopologicalSpace Y] [T2Space Y]
    {R : Set (X × Y)} (hR : MeasureTheory.AnalyticSet R) (y : Y) :
    MeasureTheory.AnalyticSet (DescriptiveSetTheory.horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- The ambient cell on which `y` is the least point of a finite section.-/
def finiteLeastCell [LinearOrder Y] (R : Set (X × Y)) (y : Y) : Set X :=
  {x | (x, y) ∈ R ∧ ∀ z, (x, z) ∈ R → y ≤ z}

/--
@isnad1 id=iff.0h5v.s6.1e9b8a9b3669 from=translated src=- shape=28fe4389 vocab=0dc50231
-/
@[simp] theorem mem_finiteLeastCell_iff [Fintype Y] [LinearOrder Y]
    {R : Set (X × Y)} {x : X} {y : Y} :
    x ∈ finiteLeastCell R y ↔
      ∃ hx : x ∈ relationDomain R, finiteLeastSelector R ⟨x, hx⟩ = y := by
  constructor
  · intro h
    let hx : x ∈ relationDomain R := ⟨y, h.1⟩
    exact ⟨hx, (finiteLeastSelector_eq_iff R ⟨x, hx⟩ y).mpr h⟩
  · rintro ⟨hx, hxy⟩
    exact (finiteLeastSelector_eq_iff R ⟨x, hx⟩ y).mp hxy

/-- Every least-value cell of an analytic finite-target relation has the Baire property.
@isnad1 id=bairemea.1h4v.s5.44778c360ee2 from=translated src=- shape=578e64a4 vocab=52a541d3
-/
theorem baireMeasurableSet_finiteLeastCell
    [TopologicalSpace X] [PolishSpace X] [TopologicalSpace Y] [T2Space Y]
    [Finite Y] [LinearOrder Y]
    {R : Set (X × Y)} (hR : MeasureTheory.AnalyticSet R) (y : Y) :
    BaireMeasurableSet (finiteLeastCell R y) := by
  have hsection (z : Y) :
      BaireMeasurableSet (DescriptiveSetTheory.horizontalSection R z) :=
    (MeasureTheory.AnalyticSet.horizontalSection hR z).baireMeasurableSet
  have hAll : BaireMeasurableSet {x : X | ∀ z, (x, z) ∈ R → y ≤ z} := by
    have hEq : {x : X | ∀ z, (x, z) ∈ R → y ≤ z} =
        ⋂ z, {x : X | (x, z) ∈ R → y ≤ z} := by
      ext x
      simp
    rw [hEq]
    apply BaireMeasurableSet.iInter
    intro z
    by_cases hyz : y ≤ z
    · convert isOpen_univ.baireMeasurableSet using 1
      ext x
      simp [hyz]
    · convert (hsection z).compl using 1
      ext x
      simp [hyz]
  exact (hsection y).inter hAll

/-- The domain of an analytic finite-target relation has the Baire property.
@isnad1 id=bairemea.1h3v.s5.24483fe3e211 from=translated src=- shape=416f6d8e vocab=3e9098eb
-/
theorem baireMeasurableSet_relationDomain_of_analytic_countable
    [TopologicalSpace X] [PolishSpace X] [TopologicalSpace Y] [T2Space Y]
    [Countable Y]
    {R : Set (X × Y)} (hR : MeasureTheory.AnalyticSet R) :
    BaireMeasurableSet (relationDomain R) := by
  have hEq : relationDomain R =
      ⋃ y, DescriptiveSetTheory.horizontalSection R y := by
    ext x
    simp [relationDomain]
  rw [hEq]
  exact BaireMeasurableSet.iUnion fun y =>
    (MeasureTheory.AnalyticSet.horizontalSection hR y).baireMeasurableSet

/-- Exact ambient preimage decomposition into least-value cells.
@isnad1 id=eq.0h4v.s6.55fe61444a54 from=translated src=- shape=ea229e83 vocab=8ce851d4
-/
theorem ambientPreimage_finiteLeastSelector [Fintype Y] [LinearOrder Y]
    (R : Set (X × Y)) (t : Set Y) :
    {x | ∃ hx : x ∈ relationDomain R, finiteLeastSelector R ⟨x, hx⟩ ∈ t} =
      ⋃ y, ⋃ (_ : y ∈ t), finiteLeastCell R y := by
  ext x
  constructor
  · rintro ⟨hx, hxt⟩
    let y := finiteLeastSelector R ⟨x, hx⟩
    refine Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hxt, ?_⟩⟩
    exact mem_finiteLeastCell_iff.mpr ⟨hx, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hyt, hcell⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hdom, hselector⟩ := mem_finiteLeastCell_iff.mp hcell
    exact ⟨hdom, hselector.symm ▸ hyt⟩

/-- The least selector of an analytic finite-target relation has Baire-measurable ambient
preimages.
@isnad1 id=hasbaire.1h3v.s5.3cd7935cdefa from=translated src=- shape=e46ffce2 vocab=158bfb6a
-/
theorem hasBaireMeasurableAmbientPreimages_finiteLeastSelector
    [TopologicalSpace X] [PolishSpace X] [TopologicalSpace Y] [T2Space Y]
    [Fintype Y] [LinearOrder Y]
    {R : Set (X × Y)} (hR : MeasureTheory.AnalyticSet R) :
    HasBaireMeasurableAmbientPreimages (relationDomain R) (finiteLeastSelector R) := by
  intro t
  rw [ambientPreimage_finiteLeastSelector]
  exact BaireMeasurableSet.iUnion fun y => BaireMeasurableSet.iUnion fun _ =>
    baireMeasurableSet_finiteLeastCell hR y

/-- Restricted analytic uniformization: exact graph semantics and Baire regularity are proved as
separate clauses.
@isnad1 id=and.1h3v.s6.c6aa5a9b533e from=translated src=- shape=a5ff5753 vocab=e550115d
-/
theorem analytic_finite_uniformization
    [TopologicalSpace X] [PolishSpace X] [TopologicalSpace Y] [T2Space Y]
    [Fintype Y] [LinearOrder Y]
    {R : Set (X × Y)} (hR : MeasureTheory.AnalyticSet R) :
    Uniformizes R (partialGraph (relationDomain R) (finiteLeastSelector R)) ∧
      HasBaireMeasurableAmbientPreimages (relationDomain R) (finiteLeastSelector R) :=
  ⟨uniformizes_partialGraph_finiteLeastSelector R,
    hasBaireMeasurableAmbientPreimages_finiteLeastSelector hR⟩

end DescriptiveSetTheory
