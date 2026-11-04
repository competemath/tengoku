/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Basic
import Tengoku.Seed.CategoryTheory.Products.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic semiorthogonal sequences

Two inhabitants keep the generic root honest before any geometry is introduced:

* the one-block sequence, which is strongly full;
* the two-block sequence on a product category, whose blocks are the two factors.

Mathlib does not currently put zero morphisms on product categories, so this file supplies the
componentwise instance.  No preadditive or pretriangulated product instance is asserted.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- Product categories inherit zero morphisms componentwise.-/
instance productHasZeroMorphisms : HasZeroMorphisms (C × D) where
  zero X Y := ⟨(0, 0)⟩
  comp_zero := by
    intro X Y f Z
    ext <;> simp
  zero_comp := by
    intro X Y Z f
    ext <;> simp

end CategoryTheory.Limits

namespace CategoryTheory.Triangulated

namespace SemiorthogonalSequence

section Single

variable {C : Type u₁} [Category.{v₁} C] [Limits.HasZeroMorphisms C]

/-- The one-block semiorthogonal sequence.-/
def single : SemiorthogonalSequence C (Fin 1) where
  component _ := ⊤
  semiorthogonal := by
    intro i j hij
    omega

/--
@isnad1 id=eq.0h2v.s6.8c46a204b9fe from=translated src=- shape=1cb69f81 vocab=90ac4a16
-/
@[simp]
lemma single_component (i : Fin 1) : (single (C := C)).component i = ⊤ := rfl

/--
@isnad1 id=eq.0h1v.s5.33037bd0a7b4 from=translated src=- shape=7c942948 vocab=5bba5199
-/
@[simp]
lemma single_total : (single (C := C)).total = ⊤ := by
  apply top_unique
  intro X _
  exact (single (C := C)).component_le_total 0 X trivial

/--
@isnad1 id=isstrong.0h1v.s6.8ab1e8b9c2ba from=translated src=- shape=62744c11 vocab=089ca601
-/
lemma single_isStronglyFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    (single (C := C)).IsStronglyFull := by
  refine ⟨0, ?_⟩
  rw [single_total]
  apply top_unique
  exact (⊤ : ObjectProperty C).le_triangEnvelopeIter 0

/--
@isnad1 id=isfull.0h1v.s6.f13f89210d12 from=translated src=- shape=62744c11 vocab=55d9cafe
-/
lemma single_isFull
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    (single (C := C)).IsFull :=
  single_isStronglyFull.isFull

end Single

section Product

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]

/-- The two factor properties on `C × D`.  The first block consists of objects whose second
component is zero; the second block consists of objects whose first component is zero.-/
def productComponent (i : Fin 2) : ObjectProperty (C × D) :=
  if i = 0 then fun X ↦ Limits.IsZero X.2 else fun X ↦ Limits.IsZero X.1

omit [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] in
/--
@isnad1 id=eq.0h2v.s5.48455e76ce91 from=translated src=- shape=32932b5a vocab=4de33f64
-/
@[simp]
lemma productComponent_zero : productComponent (C := C) (D := D) 0 =
    (fun X ↦ Limits.IsZero X.2) := by
  simp [productComponent]

omit [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] in
/--
@isnad1 id=eq.0h2v.s5.d1ca8415bf94 from=translated src=- shape=7e14296a vocab=dbc5a240
-/
@[simp]
lemma productComponent_one : productComponent (C := C) (D := D) 1 =
    (fun X ↦ Limits.IsZero X.1) := by
  simp [productComponent]

/-- The factors of a product category form a two-block semiorthogonal sequence.-/
def product : SemiorthogonalSequence (C × D) (Fin 2) where
  component := productComponent
  semiorthogonal := by
    intro i j hij X hX Y f hY
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 1 := Fin.ext (by omega)
    subst i
    subst j
    rw [productComponent_zero] at hY
    rw [productComponent_one] at hX
    apply Prod.hom_ext
    · exact hX.eq_of_tgt f.1 0
    · exact hY.eq_of_src f.2 0

/--
@isnad1 id=eq.0h3v.s6.980ac06fafe5 from=translated src=- shape=4cc1755e vocab=96b77c27
-/
@[simp]
lemma product_component (i : Fin 2) :
    (product (C := C) (D := D)).component i = productComponent i := rfl

end Product

end SemiorthogonalSequence

end CategoryTheory.Triangulated
