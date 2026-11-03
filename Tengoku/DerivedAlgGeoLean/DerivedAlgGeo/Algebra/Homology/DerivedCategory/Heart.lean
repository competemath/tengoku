/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Homology.DerivedCategory.TStructure
import Tengoku.Seed.Algebra.Homology.DerivedCategory.FullyFaithful
import Tengoku.Seed.CategoryTheory.Triangulated.TStructure.Heart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The heart of the canonical t-structure is the original abelian category

For an abelian category `C` with a derived category, the heart of the canonical t-structure on
`DerivedCategory C` is `C` itself, embedded by `singleFunctor C 0`.

Mathlib states this as the motivating example of `TStructure.Heart` and does not prove it; nothing
in either tree identified the heart of the canonical t-structure with anything. This file supplies
the identification, in Mathlib's own designated form.

## What the proof is

Nothing new. Both halves are already in Mathlib and only had to be put together:

* `singleFunctor C 0` is additive, full and faithful — `DerivedCategory.Basic` and
  `DerivedCategory.FullyFaithful`;
* its objects are `≤ 0` and `≥ 0`, so they lie in the heart — the two instances beside
  `exists_iso_singleFunctor_obj_of_isGE_of_isLE`;
* conversely an object of the heart is `≤ 0` and `≥ 0`, so
  `exists_iso_singleFunctor_obj_of_isGE_of_isLE` at `n = 0` puts it in the essential image.

That is exactly the four fields of `TStructure.Heart`, so the identification is registered as an
instance and every consumer of `ιHeart` gets it.

## Why this exists

Numerical data on an abelian category — a rank, a degree, a Mukai class, all of them homomorphisms
out of `K₀Ab` — is written against the category the sheaves live in. The stability machinery is
written against the heart of a t-structure. Without this identification the two cannot meet, and
the abstract stability theory can never be instantiated on a category of sheaves.

`heartEquivalence` is the transport vehicle; combined with `K₀Ab.congr` it moves a homomorphism out
of `K₀Ab C` to one out of `K₀Ab` of the heart.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object in the essential image of `singleFunctor C 0` lies in the heart.
@isnad1 id=heart.0h2v.s6.8355328fb157 from=translated src=- shape=a6637c7f vocab=3da99fb7
-/
theorem heart_singleFunctor_obj (X : C) :
    (TStructure.t (C := C)).heart ((singleFunctor C 0).obj X) := by
  rw [TStructure.mem_heart_iff]
  exact ⟨inferInstance, inferInstance⟩

/-- **The essential image of `singleFunctor C 0` is exactly the heart.**
@isnad1 id=eq.0h1v.s6.8477ac984e13 from=translated src=- shape=a1f0c1ca vocab=6ebabf73
-/
theorem essImage_singleFunctor_eq_heart :
    (singleFunctor C 0).essImage = (TStructure.t (C := C)).heart := by
  ext X
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact (TStructure.t (C := C)).heart.prop_of_iso e (heart_singleFunctor_obj C Y)
  · intro hX
    rw [TStructure.mem_heart_iff] at hX
    obtain ⟨hle, hge⟩ := hX
    haveI := hle
    haveI := hge
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0
    exact ⟨Y, ⟨e.symm⟩⟩

/-- **`C` is the heart of the canonical t-structure on `DerivedCategory C`.**

Mathlib names this as the motivating example of `TStructure.Heart` and leaves it unproved. All
four fields come from existing results; see the module docstring.-/
noncomputable instance isHeart : (TStructure.t (C := C)).Heart C where
  ι := singleFunctor C 0
  essImage_eq_heart := essImage_singleFunctor_eq_heart C

/-- The inclusion supplied by `isHeart` is `singleFunctor C 0`.
@isnad1 id=eq.0h1v.s6.4e4dc652b28f from=translated src=- shape=ec5173e5 vocab=15285e05
-/
theorem ιHeart_eq : (TStructure.t (C := C)).ιHeart (H := C) = singleFunctor C 0 := rfl

section Equivalence

/-- `singleFunctor C 0` lifted to the heart as a full subcategory.-/
noncomputable def toHeart : C ⥤ (TStructure.t (C := C)).heart.FullSubcategory :=
  ObjectProperty.lift _ (singleFunctor C 0) (heart_singleFunctor_obj C)

/--
@isnad1 id=eq.0h1v.s7.c94453e8ad15 from=translated src=- shape=f1f81378 vocab=02578296
-/
@[simp]
theorem toHeart_comp_ι :
    toHeart C ⋙ (TStructure.t (C := C)).heart.ι = singleFunctor C 0 := rfl

/--
@isnad1 id=full.0h1v.s6.fb8a120b9029 from=translated src=- shape=1c6b0280 vocab=7f51d4b2
-/
instance toHeart_full : (toHeart C).Full :=
  inferInstanceAs (ObjectProperty.lift _ (singleFunctor C 0) (heart_singleFunctor_obj C)).Full

/--
@isnad1 id=faithful.0h1v.s6.c8d6c962350e from=translated src=- shape=1c6b0280 vocab=622c7dc0
-/
instance toHeart_faithful : (toHeart C).Faithful :=
  inferInstanceAs (ObjectProperty.lift _ (singleFunctor C 0) (heart_singleFunctor_obj C)).Faithful

/--
@isnad1 id=esssurj.0h1v.s6.b6166b67c7db from=translated src=- shape=1c6b0280 vocab=8ca52093
-/
instance toHeart_essSurj : (toHeart C).EssSurj where
  mem_essImage := by
    rintro ⟨X, hX⟩
    rw [TStructure.mem_heart_iff] at hX
    obtain ⟨hle, hge⟩ := hX
    haveI := hle
    haveI := hge
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0
    exact ⟨Y, ⟨((TStructure.t (C := C)).heart.ι).preimageIso e.symm⟩⟩

/--
@isnad1 id=isequiva.0h1v.s6.c9da997be047 from=translated src=- shape=1c6b0280 vocab=bcf99aa3
-/
instance toHeart_isEquivalence : (toHeart C).IsEquivalence where

/-- **The heart of the canonical t-structure is `C`.**

This is the transport vehicle: numerical data written on `C` moves to the heart along it, which is
what lets stability theory stated for a heart be instantiated on a category of sheaves.-/
noncomputable def heartEquivalence : C ≌ (TStructure.t (C := C)).heart.FullSubcategory :=
  (toHeart C).asEquivalence

/--
@isnad1 id=eq.0h1v.s7.4422f611d5da from=translated src=- shape=4f12733f vocab=c66fc846
-/
@[simp]
theorem heartEquivalence_functor : (heartEquivalence C).functor = toHeart C := rfl

/--
@isnad1 id=eq.0h2v.s7.fce0f9ce9d89 from=translated src=- shape=64ea4f8a vocab=1d7d4830
-/
@[simp]
theorem toHeart_obj_obj (X : C) :
    ((toHeart C).obj X).obj = (singleFunctor C 0).obj X := rfl

end Equivalence

end DerivedCategory
