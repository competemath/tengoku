/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.CountableSections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel graph decomposition for finite targets

A measurable relation with finite standard-Borel codomain is a finite union of pairwise-disjoint
graphs of Borel partial functions.  The piece indexed by `y` is the constant function with value
`y` on the horizontal section at `y`.  Domains, functions, graphs, exact coverage, and graph codes
are all checked separately.

This is the finite-target prototype permitted by the v1.46 fallback plan.  It does not prove the
Lusin--Novikov theorem for arbitrary countable vertical sections, and its public names deliberately
do not contain `LusinNovikov`.
-/

open MeasurableSpace Set

universe u v w

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v} {ι : Type w}

/-- A family of partial functions is a Borel decomposition of `R` when every native domain,
function, and graph is measurable, distinct graphs are disjoint, and their union is exactly `R`.-/
def IsBorelPartialFunctionDecomposition
    [MeasurableSpace X] [MeasurableSpace Y]
  (R : Set (X × Y)) (s : ι → Set X) (f : (i : ι) → s i → Y) : Prop :=
  (∀ i, MeasurableSet (s i)) ∧
    (∀ i, Measurable (f i)) ∧
    (∀ i, MeasurableSet (partialGraph (s i) (f i))) ∧
    (∀ ⦃i j⦄, i ≠ j → Disjoint (partialGraph (s i) (f i)) (partialGraph (s j) (f j))) ∧
    ⋃ i, partialGraph (s i) (f i) = R

/-- Existence of a Borel partial-function decomposition indexed by a finite type.-/
def HasFiniteBorelPartialFunctionDecomposition
    [MeasurableSpace X] [MeasurableSpace Y]
    (R : Set (X × Y)) : Prop :=
  ∃ (ι : Type v) (_ : Fintype ι) (s : ι → Set X) (f : (i : ι) → s i → Y),
    IsBorelPartialFunctionDecomposition R s f

/-- Native domain of the constant piece with target value `y`.-/
def finiteTargetPieceDomain (R : Set (X × Y)) (y : Y) : Set X :=
  horizontalSection R y

/-- Constant partial function on the horizontal section at `y`.-/
def finiteTargetPieceSelector (R : Set (X × Y)) (y : Y) :
    finiteTargetPieceDomain R y → Y :=
  fun _ => y

/-- Graph of the constant partial function selected by `y`.-/
def finiteTargetPiece (R : Set (X × Y)) (y : Y) : Set (X × Y) :=
  partialGraph (finiteTargetPieceDomain R y) (finiteTargetPieceSelector R y)

@[simp] theorem mem_finiteTargetPiece_iff {R : Set (X × Y)} {x : X} {y z : Y} :
    (x, z) ∈ finiteTargetPiece R y ↔ (x, y) ∈ R ∧ y = z := by
  constructor
  · rintro ⟨hx, hvalue⟩
    exact ⟨hx, hvalue⟩
  · rintro ⟨hxy, rfl⟩
    exact ⟨hxy, rfl⟩

@[simp] theorem relationDomain_finiteTargetPiece (R : Set (X × Y)) (y : Y) :
    relationDomain (finiteTargetPiece R y) = finiteTargetPieceDomain R y :=
  relationDomain_partialGraph _ _

theorem relationSingleValued_finiteTargetPiece (R : Set (X × Y)) (y : Y) :
    RelationSingleValued (finiteTargetPiece R y) :=
  relationSingleValued_partialGraph _ _

theorem finiteTargetPiece_subset (R : Set (X × Y)) (y : Y) :
    finiteTargetPiece R y ⊆ R := by
  rintro ⟨x, z⟩ hz
  obtain ⟨hxy, hyz⟩ := mem_finiteTargetPiece_iff.mp hz
  exact hyz ▸ hxy

theorem disjoint_finiteTargetPiece (R : Set (X × Y)) {y z : Y} (hyz : y ≠ z) :
    Disjoint (finiteTargetPiece R y) (finiteTargetPiece R z) := by
  rw [Set.disjoint_left]
  intro p hpy hpz
  have hyp := (mem_finiteTargetPiece_iff.mp hpy).2
  have hzp := (mem_finiteTargetPiece_iff.mp hpz).2
  exact hyz (hyp.trans hzp.symm)

/-- The finite-target pieces cover every relation exactly; finiteness is needed only to regard this
as a finite rather than arbitrary target-indexed family.-/
theorem iUnion_finiteTargetPiece (R : Set (X × Y)) :
    ⋃ y, finiteTargetPiece R y = R := by
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hp
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hp
    exact finiteTargetPiece_subset R z hz
  · intro hxy
    exact Set.mem_iUnion.mpr ⟨y, mem_finiteTargetPiece_iff.mpr ⟨hxy, rfl⟩⟩

theorem MeasurableSet.measurableSet_finiteTargetPieceDomain
    [MeasurableSpace X] [MeasurableSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    MeasurableSet (finiteTargetPieceDomain R y) :=
  DescriptiveSetTheory.MeasurableSet.horizontalSection hR y

theorem measurable_finiteTargetPieceSelector
    [MeasurableSpace X] [MeasurableSpace Y]
    (R : Set (X × Y)) (y : Y) :
    Measurable (finiteTargetPieceSelector R y) :=
  measurable_const

theorem MeasurableSet.measurableSet_finiteTargetPiece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    MeasurableSet (finiteTargetPiece R y) :=
  measurableSet_partialGraph
    (DescriptiveSetTheory.MeasurableSet.measurableSet_finiteTargetPieceDomain hR y)
    (measurable_finiteTargetPieceSelector R y)

theorem MeasurableSet.exists_standardBorelCode_finiteTargetPiece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    ∃ c : StandardBorelCode (X × Y), c.eval = finiteTargetPiece R y :=
  StandardBorelCode.exists_code
    (DescriptiveSetTheory.MeasurableSet.measurableSet_finiteTargetPiece hR y)

/-- Honest finite-target fallback: a measurable relation into a finite standard-Borel target has a
finite, pairwise-disjoint decomposition into Borel partial-function graphs.-/
theorem MeasurableSet.hasFiniteBorelPartialFunctionDecomposition_of_finiteTarget
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Finite Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) :
    HasFiniteBorelPartialFunctionDecomposition R := by
  letI := Fintype.ofFinite Y
  refine ⟨Y, inferInstance, finiteTargetPieceDomain R, finiteTargetPieceSelector R, ?_⟩
  refine ⟨fun y =>
    DescriptiveSetTheory.MeasurableSet.measurableSet_finiteTargetPieceDomain hR y,
    ?_, ?_, ?_, iUnion_finiteTargetPiece R⟩
  · exact fun y => measurable_finiteTargetPieceSelector R y
  · exact fun y =>
      DescriptiveSetTheory.MeasurableSet.measurableSet_finiteTargetPiece hR y
  · intro y z hyz
    exact disjoint_finiteTargetPiece R hyz

end DescriptiveSetTheory
