/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.CategoryTheory.Abelian.Exact
import Tengoku.Seed.Algebra.Homology.ShortComplex.ShortExact
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.Presentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Grothendieck groups of categorical short exact sequences

This file turns the presentation in `KTheory.Presentation` into a directly usable construction
for an abelian category and for a full class of objects inside it. The latter is the intended
entry point for finite locally free sheaves, perfect complexes, or coherent sheaves once their
geometric predicates and closure properties are available.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace ExactGrothendieck

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- Three objects form an exact triple when they occur in a categorical short exact sequence.-/
def shortExactObjects (A B D : C) : Prop :=
  ∃ (f : A ⟶ B) (g : B ⟶ D) (zero : f ≫ g = 0),
    (ShortComplex.mk f g zero).ShortExact

/-- The Grothendieck group of all objects of a category, modulo categorical short exact
sequences.-/
abbrev CategoryGroup := Group C (shortExactObjects C)

/-- The class of a categorical object.-/
def categoryClassOf (E : C) : CategoryGroup C :=
  classOf C (shortExactObjects C) E

/-- A short exact sequence gives the usual relation in the categorical Grothendieck group.-/
theorem categoryClassOf_middle {A B D : C} {f : A ⟶ B} {g : B ⟶ D}
    (zero : f ≫ g = 0) (h : (ShortComplex.mk f g zero).ShortExact) :
    categoryClassOf C B = categoryClassOf C A + categoryClassOf C D :=
  classOf_middle C (shortExactObjects C) A B D ⟨f, g, zero, h⟩

section Abelian

variable (Acat : Type u) [Category.{v} Acat] [Abelian Acat]

/-- The zero object represents zero in the categorical Grothendieck group.-/
@[simp]
theorem categoryClassOf_zero : categoryClassOf Acat (0 : Acat) = 0 := by
  let S : ShortComplex Acat :=
    ShortComplex.mk (0 : (0 : Acat) ⟶ 0) (0 : (0 : Acat) ⟶ 0) zero_comp
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_mono S rfl).2
        (inferInstance : Mono (0 : (0 : Acat) ⟶ 0)) }
  have h := categoryClassOf_middle (C := Acat) S.zero hS
  change categoryClassOf Acat (0 : Acat) =
    categoryClassOf Acat (0 : Acat) + categoryClassOf Acat (0 : Acat) at h
  have h' := congrArg (fun z => z - categoryClassOf Acat (0 : Acat)) h
  symm
  simpa only [sub_self, add_sub_cancel_right] using h'

/-- Isomorphic objects define the same class in the categorical Grothendieck group.-/
theorem categoryClassOf_iso {A B : Acat} (e : A ≅ B) :
    categoryClassOf Acat A = categoryClassOf Acat B := by
  let S := ShortComplex.mk e.hom (0 : B ⟶ (0 : Acat)) comp_zero
  haveI : IsIso e.hom := by infer_instance
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_epi S rfl).2
        (inferInstance : Epi e.hom) }
  have h := categoryClassOf_middle (C := Acat) S.zero hS
  change categoryClassOf Acat B =
    categoryClassOf Acat A + categoryClassOf Acat (0 : Acat) at h
  simpa using h.symm

end Abelian

variable (P : C → Prop)

/-- Exact triples in the full class of objects satisfying `P`, computed in the ambient
category.-/
def shortExactIn (A B D : {E : C // P E}) : Prop :=
  ∃ (f : A.1 ⟶ B.1) (g : B.1 ⟶ D.1) (zero : f ≫ g = 0),
    (ShortComplex.mk f g zero).ShortExact

/-- The exact Grothendieck group of a full geometric class `P` of ambient objects.-/
abbrev SubcategoryGroup := Group {E : C // P E} (shortExactIn C P)

/-- The class of an object carrying a proof that it belongs to the selected geometric class.-/
def subcategoryClassOf (E : C) (hE : P E) : SubcategoryGroup C P :=
  classOf {E : C // P E} (shortExactIn C P) ⟨E, hE⟩

/-- A short exact sequence whose three terms satisfy `P` gives the defining relation in the
selected exact Grothendieck group.-/
theorem subcategoryClassOf_middle {A B D : C} (hA : P A) (hB : P B) (hD : P D)
    {f : A ⟶ B} {g : B ⟶ D} (zero : f ≫ g = 0)
    (h : (ShortComplex.mk f g zero).ShortExact) :
    subcategoryClassOf C P B hB =
      subcategoryClassOf C P A hA + subcategoryClassOf C P D hD :=
  classOf_middle {E : C // P E} (shortExactIn C P) ⟨A, hA⟩ ⟨B, hB⟩ ⟨D, hD⟩
    ⟨f, g, zero, h⟩

section AbelianSubcategory

variable (Acat : Type u) [Category.{v} Acat] [Abelian Acat]
variable (Q : Acat → Prop)

/-- An object of the selected class which is zero in the ambient abelian category represents
zero in the selected Grothendieck group.-/
theorem subcategoryClassOf_isZero {Z : Acat} (hZ : Q Z) (zeroZ : IsZero Z) :
    subcategoryClassOf Acat Q Z hZ = 0 := by
  letI : Mono (0 : Z ⟶ Z) := zeroZ.mono _
  letI : Epi (0 : Z ⟶ Z) := zeroZ.epi _
  let S : ShortComplex Acat := ShortComplex.mk (0 : Z ⟶ Z) (0 : Z ⟶ Z) zero_comp
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_mono S rfl).2 inferInstance }
  have h := subcategoryClassOf_middle (C := Acat) Q hZ hZ hZ S.zero hS
  change subcategoryClassOf Acat Q Z hZ =
    subcategoryClassOf Acat Q Z hZ + subcategoryClassOf Acat Q Z hZ at h
  have h' := congrArg (fun z => z - subcategoryClassOf Acat Q Z hZ) h
  symm
  simpa only [sub_self, add_sub_cancel_right] using h'

/-- Isomorphic ambient objects in the selected class have the same selected Grothendieck
class, provided the selected class contains a zero object.-/
theorem subcategoryClassOf_iso {A B Z : Acat} (hA : Q A) (hB : Q B)
    (hZ : Q Z) (zeroZ : IsZero Z) (e : A ≅ B) :
    subcategoryClassOf Acat Q A hA = subcategoryClassOf Acat Q B hB := by
  letI : Epi (0 : B ⟶ Z) := zeroZ.epi _
  haveI : IsIso e.hom := by infer_instance
  let S : ShortComplex Acat := ShortComplex.mk e.hom (0 : B ⟶ Z) comp_zero
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_epi S rfl).2 (inferInstance : Epi e.hom) }
  have h := subcategoryClassOf_middle (C := Acat) Q hA hB hZ S.zero hS
  change subcategoryClassOf Acat Q B hB =
    subcategoryClassOf Acat Q A hA + subcategoryClassOf Acat Q Z hZ at h
  rw [subcategoryClassOf_isZero Acat Q hZ zeroZ, add_zero] at h
  exact h.symm

end AbelianSubcategory

section Functoriality

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]

/-- A functor preserving zero morphisms and short exact complexes induces the expected map on
categorical Grothendieck groups.-/
def mapOfShortExactFunctor (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact) :
    CategoryGroup C →+ CategoryGroup D :=
  map F.obj fun A B E h => by
    obtain ⟨f, g, zero, hshort⟩ := h
    let S := ShortComplex.mk f g zero
    let T := S.map F
    change shortExactObjects D T.X₁ T.X₂ T.X₃
    exact ⟨T.f, T.g, T.zero, hF S hshort⟩

@[simp]
theorem mapOfShortExactFunctor_classOf (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact) (E : C) :
    mapOfShortExactFunctor F hF (categoryClassOf C E) = categoryClassOf D (F.obj E) := by
  simp [mapOfShortExactFunctor, categoryClassOf]

/-- A short-exact-preserving functor mapping a full object class `P` into a full object class `Q`
induces a map on their exact Grothendieck groups.-/
def mapOfShortExactFunctorOn (P : C → Prop) (Q : D → Prop)
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hobj : ∀ E, P E → Q (F.obj E))
    (hF : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact) :
    SubcategoryGroup C P →+ SubcategoryGroup D Q :=
  map (fun E => ⟨F.obj E.1, hobj E.1 E.2⟩) fun A B E h => by
    obtain ⟨f, g, zero, hshort⟩ := h
    let S := ShortComplex.mk f g zero
    let T := S.map F
    change shortExactIn D Q
      ⟨T.X₁, hobj A.1 A.2⟩ ⟨T.X₂, hobj B.1 B.2⟩ ⟨T.X₃, hobj E.1 E.2⟩
    exact ⟨T.f, T.g, T.zero, hF S hshort⟩

@[simp]
theorem mapOfShortExactFunctorOn_classOf (P : C → Prop) (Q : D → Prop)
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hobj : ∀ E, P E → Q (F.obj E))
    (hF : ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact)
    (E : C) (hE : P E) :
    mapOfShortExactFunctorOn P Q F hobj hF (subcategoryClassOf C P E hE) =
      subcategoryClassOf D Q (F.obj E) (hobj E hE) := by
  simp [mapOfShortExactFunctorOn, subcategoryClassOf]

end Functoriality

end ExactGrothendieck
