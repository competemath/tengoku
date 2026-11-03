/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.CategoryTheory.ObjectProperty.Orthogonal
import Tengoku.Seed.CategoryTheory.Triangulated.Generators
import Tengoku.Seed.CategoryTheory.Triangulated.Orthogonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Semiorthogonal sequences

This file defines the generic root for semiorthogonal decompositions.  The root is a sequence of
object properties with the expected ordered Hom-vanishing.  Generation, strong generation, and
closure of the components under the triangulated operations are deliberately separate predicates:
none of them is smuggled into the carrier.

The components are object properties rather than new full subcategory structures.  This lets the
root reuse Mathlib's orthogonals and triangulated envelope, and lets geometric realizations add
their own closure and base-change theorems without creating a sibling hierarchy.
-/

open CategoryTheory

universe v u w

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The right orthogonal of any property is stable under retracts: a map from
a `P`-object into a retract extends to the ambient object, where it
vanishes.
@isnad1 id=isstable.0h2v.s4.d55303494037 from=translated src=- shape=10965991 vocab=a10521f3
-/
instance rightOrthogonal_isStableUnderRetracts (P : ObjectProperty C) :
    P.rightOrthogonal.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    intro A f hA
    rw [← Category.comp_id f, ← h.retract, ← Category.assoc,
      hY (f ≫ h.i) hA, zero_comp]

/-- The left orthogonal of any property is stable under retracts.
@isnad1 id=isstable.0h2v.s4.728c169b0a34 from=translated src=- shape=10965991 vocab=84b554c6
-/
instance leftOrthogonal_isStableUnderRetracts (P : ObjectProperty C) :
    P.leftOrthogonal.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    intro A f hA
    rw [← Category.id_comp f, ← h.retract, Category.assoc,
      hY (h.r ≫ f) hA, comp_zero]

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type w} [Preorder ι]

/-- An ordered family of object properties in which maps from an earlier component to a later
component vanish.  Fullness and triangulated closure are independent refinements below.-/
structure SemiorthogonalSequence (C : Type u) [Category.{v} C]
    [Limits.HasZeroMorphisms C] (ι : Type w) [Preorder ι] where
  /-- The component at an index.-/
  component : ι → ObjectProperty C
  /-- Maps from an earlier component to a later component vanish.-/
  semiorthogonal : ∀ ⦃i j : ι⦄, i < j → component j ≤ (component i).rightOrthogonal

namespace SemiorthogonalSequence

variable (S : SemiorthogonalSequence C ι)

/-- The property of lying in one of the components.  This is the common generator property used
by both classical and strong fullness.-/
def total : ObjectProperty C := ⨆ i, S.component i

/-- The residual object property of a semiorthogonal sequence: the right
orthogonal to the union of its components. This definition does not assert
that the sequence is full or that its components are admissible.-/
def residual : ObjectProperty C := S.total.rightOrthogonal

/--
@isnad1 id=le.0h4v.s5.2f691b6a481f from=translated src=- shape=8918032c vocab=cca3c72f
-/
lemma component_le_total (i : ι) : S.component i ≤ S.total :=
  le_iSup S.component i

/--
@isnad1 id=eq.1h10v.s6.03a1ebfcf27c from=translated src=- shape=2b2a0234 vocab=31088e7e
-/
lemma hom_eq_zero ⦃i j : ι⦄ (hij : i < j) ⦃X Y : C⦄
    (hX : S.component i X) (hY : S.component j Y) (f : X ⟶ Y) : f = 0 :=
  S.semiorthogonal hij Y hY f hX

/-- Maps from any component of the sequence to a residual object vanish.
@isnad1 id=eq.0h9v.s6.9efadf278315 from=translated src=- shape=69f6a7ff vocab=f3acebef
-/
lemma component_hom_residual_eq_zero (i : ι) ⦃X Y : C⦄
    (hX : S.component i X) (hY : S.residual Y) (f : X ⟶ Y) : f = 0 :=
  hY f (S.component_le_total i X hX)

/-- Each component is a triangulated object property.  This is independent of fullness.-/
def HasTriangulatedComponents
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  ∀ i, (S.component i).IsTriangulated

/-- The union of triangulated components is stable under shifts. The union
need not itself be extension-closed, which is why this conclusion is stated
only at the strength needed by orthogonal closure.
@isnad1 id=isstable.1h3v.s6.04915149269b from=translated src=- shape=e01dacb2 vocab=3fa6aae0
-/
theorem HasTriangulatedComponents.totalIsStableUnderShift
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (hS : S.HasTriangulatedComponents) : S.total.IsStableUnderShift ℤ := by
  letI (i : ι) : (S.component i).IsTriangulated := hS i
  constructor
  intro n
  constructor
  · intro X hX
    change S.total (X⟦n⟧)
    rw [total, ObjectProperty.prop_iSup_iff] at hX ⊢
    obtain ⟨i, hi⟩ := hX
    exact ⟨i, (S.component i).le_shift n _ hi⟩

/-- The residual of a sequence with triangulated components is triangulated.
No fullness or admissibility hypothesis is required for this closure fact.
@isnad1 id=istriang.1h3v.s6.6d3e5c5dcfcb from=translated src=- shape=98b7818d vocab=997b0553
-/
theorem HasTriangulatedComponents.residual_isTriangulated
    {D : Type*} [Category D] [Preadditive D] [Limits.HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] {κ : Type*} [Preorder κ]
    {T : SemiorthogonalSequence D κ} (hT : T.HasTriangulatedComponents) :
    T.residual.IsTriangulated := by
  letI : T.total.IsStableUnderShift ℤ := hT.totalIsStableUnderShift
  change T.total.rightOrthogonal.IsTriangulated
  infer_instance

/-- Classical fullness: the union of the components generates under shifts, binary products,
retracts, and arbitrarily many extensions.-/
def IsFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  S.total.IsClassicalTriangulatedGenerator

/-- Strong fullness: the union of the components generates after a uniformly bounded number of
extensions.  This is stronger than `IsFull`, not a field of the sequence.-/
def IsStronglyFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] : Prop :=
  S.total.IsStrongTriangulatedGenerator

/--
@isnad1 id=isfull.1h3v.s6.0383a8886a7b from=translated src=- shape=bf28eca7 vocab=9424b9bc
-/
lemma IsStronglyFull.isFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (hS : S.IsStronglyFull) : S.IsFull :=
  hS.isClassicalTriangulatedGenerator

/-- Transport the components along a functor once orthogonality of their essential images has
been proved in the target.  In particular, a geometric pullback theorem supplies `h`; pullback is
not a field of the semiorthogonal sequence.-/
def map {D : Type*} [Category* D] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    (h : ∀ ⦃i j : ι⦄, i < j →
      (S.component j).map F ≤ ((S.component i).map F).rightOrthogonal) :
    SemiorthogonalSequence D ι where
  component i := (S.component i).map F
  semiorthogonal := h

/--
@isnad1 id=eq.1h6v.s7.457455c5d8b1 from=translated src=- shape=1e1a7343 vocab=1edc94ad
-/
@[simp]
lemma map_component {D : Type*} [Category* D] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    (h : ∀ ⦃i j : ι⦄, i < j →
      (S.component j).map F ≤ ((S.component i).map F).rightOrthogonal) (i : ι) :
    (S.map F h).component i = (S.component i).map F := rfl

/-- Restrict a semiorthogonal sequence along a strictly monotone map of index types.-/
def reindex {κ : Type*} [Preorder κ] (f : κ → ι)
    (hf : ∀ ⦃i j : κ⦄, i < j → f i < f j) : SemiorthogonalSequence C κ where
  component i := S.component (f i)
  semiorthogonal := by
    intro i j hij
    exact S.semiorthogonal (hf hij)

/--
@isnad1 id=eq.1h6v.s6.0744327aed2c from=translated src=- shape=89c0907c vocab=3ecc59f1
-/
@[simp]
lemma reindex_component {κ : Type*} [Preorder κ] (f : κ → ι)
    (hf : ∀ ⦃i j : κ⦄, i < j → f i < f j) (i : κ) :
    (reindex S f hf).component i = S.component (f i) := rfl

end SemiorthogonalSequence

end CategoryTheory.Triangulated
