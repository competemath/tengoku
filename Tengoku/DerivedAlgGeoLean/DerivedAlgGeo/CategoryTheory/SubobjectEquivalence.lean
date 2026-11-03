/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.CategoryTheory.Subobject.Lattice
import Tengoku.Seed.CategoryTheory.Subobject.Limits
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.Zero
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Tengoku.Seed.CategoryTheory.Abelian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Subobjects along a functor, and the order isomorphism from an equivalence

Mathlib maps subobjects along a morphism (`Subobject.map`) and along an isomorphism *of objects*
(`Subobject.mapIsoToOrderIso`), both inside a single category. It does not map them along a
**functor**, so an equivalence of categories does not yet carry subobject lattices to subobject
lattices.

This file supplies that. `mapFunctor` pushes a subobject forward along any mono-preserving functor,
and `mapEquivalence` upgrades it to an order isomorphism when the functor is half of an
equivalence. For abelian categories, a functor preserving monos, epis, and binary coproducts
also carries binary joins of subobjects to binary joins. Preserving monos and epis likewise
allows the image of a lifted arrow into a fixed target to lift its image subobject in
the abelian setting.

## Why an order isomorphism and not just a monotone map

The consumers are chain conditions and filtrations. A monotone map carries a chain to a chain, but
it does not carry a *strictly* increasing chain to a strictly increasing one, and it need not carry
the bottom and top to the bottom and top. An order isomorphism does all three, which is what makes
it possible to transport a Harder–Narasimhan filtration along an equivalence.

## The shape of the proofs

For the equivalence results, the proofs reduce a subobject to a representing mono,
then compare explicit morphisms using the unit isomorphism. Image preservation
uses the epi--mono image factorization and balancedness instead.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subobject

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

section MapFunctor

variable (F : A ⥤ B) [F.PreservesMonomorphisms]

/-- **A subobject pushed forward along a mono-preserving functor.**-/
def mapFunctor {X : A} : Subobject X → Subobject (F.obj X) :=
  Subobject.lift (fun _ f _ ↦ Subobject.mk (F.map f))
    (by
      intro A₁ A₂ f g _ _ i hi
      exact Subobject.mk_eq_mk_of_comm _ _ (F.mapIso i)
        (by rw [Functor.mapIso_hom, ← F.map_comp, hi]))

/--
@isnad1 id=eq.0h6v.s6.1e61ef5267a3 from=translated src=- shape=7c577365 vocab=e87c9a34
-/
@[simp]
theorem mapFunctor_mk {X A₁ : A} (f : A₁ ⟶ X) [Mono f] :
    mapFunctor F (Subobject.mk f) = Subobject.mk (F.map f) :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.92a12c9eda80 from=translated src=- shape=d58d7d67 vocab=24be4114
-/
theorem mapFunctor_eq_mk_arrow {X : A} (P : Subobject X) :
    mapFunctor F P = Subobject.mk (F.map P.arrow) := by
  conv_lhs => rw [← Subobject.mk_arrow P]
  rfl

/--
@isnad1 id=monotone.0h4v.s6.ab7122bb0f2b from=translated src=- shape=2b35fb1e vocab=fcf8b570
-/
theorem mapFunctor_monotone {X : A} : Monotone (mapFunctor F (X := X)) := by
  intro P Q h
  rw [mapFunctor_eq_mk_arrow, mapFunctor_eq_mk_arrow]
  refine Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE P Q h)) ?_
  rw [← F.map_comp, Subobject.ofLE_arrow]

/-- Mapping along an isomorphism and back is the identity. Stated as a lemma rather than reached
by `rw [← map_comp]`, whose motive is not type correct here: `Subobject.map` carries a `Mono`
instance argument that changes under the rewrite.
@isnad1 id=eq.0h5v.s6.082aa842c57d from=translated src=- shape=0b6b0859 vocab=40dfac7f
-/
theorem map_inv_map_hom {X Y : A} (i : X ≅ Y) (P : Subobject X) :
    (Subobject.map i.inv).obj ((Subobject.map i.hom).obj P) = P := by
  induction P using Subobject.ind with
  | h f =>
      haveI : Mono (f ≫ i.hom) := mono_comp _ _
      simp only [Subobject.map_mk, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/--
@isnad1 id=eq.0h5v.s6.f4e70f9fcc34 from=translated src=- shape=e8544ffc vocab=40dfac7f
-/
theorem map_hom_map_inv {X Y : A} (i : X ≅ Y) (Q : Subobject Y) :
    (Subobject.map i.hom).obj ((Subobject.map i.inv).obj Q) = Q := by
  induction Q using Subobject.ind with
  | h f =>
      haveI : Mono (f ≫ i.inv) := mono_comp _ _
      simp only [Subobject.map_mk, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end MapFunctor

section MapFunctorImage

variable [HasImages A] [HasEqualizers A]
  [HasImages B] [HasEqualizers B] [Balanced B]

/-- Every arrow into `G.obj X` extends from a source object into the fixed
source target `X`, up to an isomorphism on the arrow's domain. This is an
explicit input for localization arguments, not an automatic consequence of
essential surjectivity on objects.-/
def FixedTargetArrowExtension (G : A ⥤ B) (X : A) : Prop :=
  ∀ {Z : B} (β : Z ⟶ G.obj X),
    ∃ (Y : A) (f : Y ⟶ X) (e : Z ≅ G.obj Y), β = e.hom ≫ G.map f

/-- Only monomorphisms into `G.obj X` need extend in order to lift subobjects.
Unlike extension of all arrows, this does not force every object of `B` into
the essential image of `G`.-/
def FixedTargetMonoExtension (G : A ⥤ B) (X : A) : Prop :=
  ∀ {Z : B} (β : Z ⟶ G.obj X), Mono β →
    ∃ (Y : A) (f : Y ⟶ X) (e : Z ≅ G.obj Y), β = e.hom ≫ G.map f

end MapFunctorImage

section MapEquivalence

variable (e : A ≌ B) [e.functor.PreservesMonomorphisms] [e.inverse.PreservesMonomorphisms]

/-- The unit of an equivalence at `X`, with both endpoints spelled out.

`e.unitIso.app X` has type `(𝟭 A).obj X ≅ (e.functor ⋙ e.inverse).obj X`. That is definitionally
what is wanted but not syntactically, and the difference defeats `rw` on `Subobject.map`, whose
statements are dependent in the ambient object. Naming the isomorphism with its endpoints spelled
out is what makes the rewrites below go through.-/
def unitAt (X : A) : X ≅ e.inverse.obj (e.functor.obj X) := e.unitIso.app X

omit [e.functor.PreservesMonomorphisms] [e.inverse.PreservesMonomorphisms] in
/--
@isnad1 id=eq.0h6v.s8.16e79723826d from=translated src=- shape=c32802a1 vocab=edea21ed
-/
theorem unitAt_naturality {X Y : A} (f : X ⟶ Y) :
    f ≫ (unitAt e Y).hom = (unitAt e X).hom ≫ e.inverse.map (e.functor.map f) :=
  e.unitIso.hom.naturality f

/-- **The round trip through an equivalence is the unit isomorphism.**

This is the one step with content: naturality of the unit rewrites the round trip as composition
with a unit component, and that component is invertible, so the two subobjects agree.
@isnad1 id=eq.0h5v.s8.b5a2fd5a6529 from=translated src=- shape=fbc97b6a vocab=40f8d96f
-/
theorem mapFunctor_inverse_functor {X : A} (P : Subobject X) :
    mapFunctor e.inverse (mapFunctor e.functor P) =
      (Subobject.map (unitAt e X).hom).obj P := by
  induction P using Subobject.ind with
  | h f =>
      haveI : Mono (e.functor.map f) := inferInstance
      haveI : Mono (e.inverse.map (e.functor.map f)) := inferInstance
      haveI : Mono (f ≫ (unitAt e X).hom) := mono_comp _ _
      simp only [mapFunctor_mk, Subobject.map_mk]
      refine (Subobject.mk_eq_mk_of_comm _ _ (unitAt e _) ?_).symm
      exact (unitAt_naturality e f).symm

/-- **The order isomorphism on subobjects induced by an equivalence.**-/
def mapEquivalence (X : A) : Subobject X ≃o Subobject (e.functor.obj X) where
  toFun := mapFunctor e.functor
  invFun := fun Q ↦ (Subobject.map (unitAt e X).inv).obj (mapFunctor e.inverse Q)
  left_inv := by
    intro P
    dsimp only
    rw [mapFunctor_inverse_functor]
    exact map_inv_map_hom (unitAt e X) P
  right_inv := by
    intro Q
    dsimp only
    induction Q using Subobject.ind with
    | h g =>
        haveI : Mono (e.inverse.map g) := inferInstance
        haveI : Mono (e.inverse.map g ≫ (unitAt e X).inv) := mono_comp _ _
        have hc : e.functor.map ((unitAt e X).inv) =
            (e.counitIso.app (e.functor.obj X)).hom :=
          (Equivalence.counit_app_functor e X).symm
        simp only [mapFunctor_mk, Subobject.map_mk, Functor.map_comp, hc]
        haveI : Mono (e.functor.map (e.inverse.map g) ≫
            (e.counitIso.app (e.functor.obj X)).hom) := mono_comp _ _
        exact Subobject.mk_eq_mk_of_comm _ _ (e.counitIso.app _)
          (e.counitIso.hom.naturality g).symm
  map_rel_iff' := by
    intro P Q
    refine ⟨fun h ↦ ?_, fun h ↦ mapFunctor_monotone _ h⟩
    have hle : (Subobject.map (unitAt e X).hom).obj P ≤
        (Subobject.map (unitAt e X).hom).obj Q := by
      rw [← mapFunctor_inverse_functor, ← mapFunctor_inverse_functor]
      exact mapFunctor_monotone e.inverse h
    have h2 := (Subobject.map (unitAt e X).inv).monotone hle
    simpa only [map_inv_map_hom] using h2

/--
@isnad1 id=eq.0h5v.s8.eaeea9d90f5e from=translated src=- shape=c51ef0c5 vocab=ab35465b
-/
@[simp]
theorem mapEquivalence_apply (X : A) (P : Subobject X) :
    mapEquivalence e X P = mapFunctor e.functor P := rfl

end MapEquivalence

section Cokernel

variable [Abelian A] [Abelian B] (F : A ⥤ B) [F.PreservesZeroMorphisms]
  [F.PreservesMonomorphisms] [PreservesFiniteColimits F]

/-- **The underlying object of a pushed-forward subobject** is the image of the underlying object.

`mapFunctor F P` is only propositionally `mk (F.map P.arrow)`, so this is an `isoOfEqMk` rather
than a definitional equality.-/
noncomputable def mapFunctorIso {X : A} (P : Subobject X) :
    ((mapFunctor F P : Subobject (F.obj X)) : B) ≅ F.obj (P : A) :=
  Subobject.isoOfEqMk _ (F.map P.arrow) (mapFunctor_eq_mk_arrow F P)

omit [Abelian A] [Abelian B] [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] in
/--
@isnad1 id=eq.0h5v.s8.2433d8ef86df from=translated src=- shape=2d7f527d vocab=ad64a0ed
-/
@[reassoc (attr := simp)]
theorem mapFunctorIso_hom_arrow {X : A} (P : Subobject X) :
    (mapFunctorIso F P).hom ≫ F.map P.arrow = (mapFunctor F P).arrow := by
  simp [mapFunctorIso]

omit [Abelian A] [Abelian B] [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] in
/-- **The chain step transports.** Both sides are maps into a subobject, so it is enough to compose
with its arrow, which is a mono.
@isnad1 id=eq.1h6v.s9.37042fdca31b from=translated src=- shape=506a8087 vocab=774a889d
-/
theorem ofLE_mapFunctor {X : A} {P Q : Subobject X} (h : P ≤ Q) :
    Subobject.ofLE (mapFunctor F P) (mapFunctor F Q) (mapFunctor_monotone F h) ≫
        (mapFunctorIso F Q).hom =
      (mapFunctorIso F P).hom ≫ F.map (Subobject.ofLE P Q h) := by
  haveI : Mono (F.map Q.arrow) := inferInstance
  refine (cancel_mono (F.map Q.arrow)).1 ?_
  rw [Category.assoc, mapFunctorIso_hom_arrow, Subobject.ofLE_arrow, Category.assoc,
    ← F.map_comp, Subobject.ofLE_arrow, mapFunctorIso_hom_arrow]

/-- **The successive quotient transports.**

This is what a Harder–Narasimhan filtration needs beyond the order isomorphism: its factors are
cokernels of chain steps, and they must be identified with the images of the original factors.
The square of `ofLE_mapFunctor` is an isomorphism square, so the cokernels agree; then `F`
preserving finite colimits moves the cokernel inside.-/
noncomputable def cokernelOfLEMapFunctorIso {X : A} {P Q : Subobject X} (h : P ≤ Q) :
    cokernel (Subobject.ofLE (mapFunctor F P) (mapFunctor F Q) (mapFunctor_monotone F h)) ≅
      F.obj (cokernel (Subobject.ofLE P Q h)) :=
  (cokernel.mapIso _ (F.map (Subobject.ofLE P Q h)) (mapFunctorIso F P) (mapFunctorIso F Q)
      (ofLE_mapFunctor F h)).trans
    (PreservesCokernel.iso F (Subobject.ofLE P Q h)).symm

end Cokernel

end CategoryTheory.Subobject
