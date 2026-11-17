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

/--
@isnad1 id=iff.0h6v.s5.1eef208f21c8 from=translated src=- shape=e5fade33 vocab=5e823417
-/
@[simp] theorem mem_finiteTargetPiece_iff {R : Set (X × Y)} {x : X} {y z : Y} :
    (x, z) ∈ finiteTargetPiece R y ↔ (x, y) ∈ R ∧ y = z := by
  constructor
  · rintro ⟨hx, hvalue⟩
    exact ⟨hx, hvalue⟩
  · rintro ⟨hxy, rfl⟩
    exact ⟨hxy, rfl⟩

/--
@isnad1 id=eq.0h4v.s4.3557e8d0a605 from=translated src=- shape=3e864d97 vocab=24bb702d
-/
@[simp] theorem relationDomain_finiteTargetPiece (R : Set (X × Y)) (y : Y) :
    relationDomain (finiteTargetPiece R y) = finiteTargetPieceDomain R y :=
  relationDomain_partialGraph _ _

/--
@isnad1 id=relation.0h4v.s4.a461d9f175e6 from=translated src=- shape=52e6ae2a vocab=3fce9bd7
-/
theorem relationSingleValued_finiteTargetPiece (R : Set (X × Y)) (y : Y) :
    RelationSingleValued (finiteTargetPiece R y) :=
  relationSingleValued_partialGraph _ _

/--
@isnad1 id=le.0h4v.s4.f200edc7020c from=translated src=- shape=9c7ec848 vocab=3eab8780
-/
theorem finiteTargetPiece_subset (R : Set (X × Y)) (y : Y) :
    finiteTargetPiece R y ⊆ R := by
  rintro ⟨x, z⟩ hz
  obtain ⟨hxy, hyz⟩ := mem_finiteTargetPiece_iff.mp hz
  exact hyz ▸ hxy

/--
@isnad1 id=disjoint.1h5v.s6.2702ce639ed2 from=translated src=- shape=a23c57ab vocab=9872910b
-/
theorem disjoint_finiteTargetPiece (R : Set (X × Y)) {y z : Y} (hyz : y ≠ z) :
    Disjoint (finiteTargetPiece R y) (finiteTargetPiece R z) := by
  rw [Set.disjoint_left]
  intro p hpy hpz
  have hyp := (mem_finiteTargetPiece_iff.mp hpy).2
  have hzp := (mem_finiteTargetPiece_iff.mp hpz).2
  exact hyz (hyp.trans hzp.symm)

/-- The finite-target pieces cover every relation exactly; finiteness is needed only to regard this
as a finite rather than arbitrary target-indexed family.
@isnad1 id=eq.0h3v.s4.a940dfdae4dd from=translated src=- shape=85c82939 vocab=af20a033
-/
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

/--
@isnad1 id=measurab.1h4v.s5.3efcfb6b4355 from=translated src=- shape=694ea159 vocab=9aa0405f
-/
theorem MeasurableSet.measurableSet_finiteTargetPieceDomain
    [MeasurableSpace X] [MeasurableSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    MeasurableSet (finiteTargetPieceDomain R y) :=
  DescriptiveSetTheory.MeasurableSet.horizontalSection hR y

/--
@isnad1 id=measurab.0h4v.s5.5b15770c5b05 from=translated src=- shape=200f9bef vocab=0e6dba25
-/
theorem measurable_finiteTargetPieceSelector
    [MeasurableSpace X] [MeasurableSpace Y]
    (R : Set (X × Y)) (y : Y) :
    Measurable (finiteTargetPieceSelector R y) :=
  measurable_const

/--
@isnad1 id=measurab.1h4v.s5.d55730df4518 from=translated src=- shape=14a22033 vocab=6c608666
-/
theorem MeasurableSet.measurableSet_finiteTargetPiece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    MeasurableSet (finiteTargetPiece R y) :=
  measurableSet_partialGraph
    (DescriptiveSetTheory.MeasurableSet.measurableSet_finiteTargetPieceDomain hR y)
    (measurable_finiteTargetPieceSelector R y)

/--
@isnad1 id=ex.1h4v.s6.80e6fb751444 from=translated src=- shape=a1bc6d67 vocab=8f04e054
-/
theorem MeasurableSet.exists_standardBorelCode_finiteTargetPiece
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {R : Set (X × Y)} (hR : MeasurableSet R) (y : Y) :
    ∃ c : StandardBorelCode (X × Y), c.eval = finiteTargetPiece R y :=
  StandardBorelCode.exists_code
    (DescriptiveSetTheory.MeasurableSet.measurableSet_finiteTargetPiece hR y)

/-- Honest finite-target fallback: a measurable relation into a finite standard-Borel target has a
finite, pairwise-disjoint decomposition into Borel partial-function graphs.
@isnad1 id=hasfinit.1h3v.s5.055cb0110c98 from=translated src=- shape=e147e088 vocab=ff50ad94
-/
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
