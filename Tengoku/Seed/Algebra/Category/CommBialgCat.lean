/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.CommAlgCat.Monoidal
public import Tengoku.Seed.CategoryTheory.Monoidal.Mon
public import Tengoku.Seed.RingTheory.Bialgebra.Equiv

/-!
# The category of commutative bialgebras over a commutative ring

This file defines the bundled category `CommBialgCat R` of commutative bialgebras over a fixed
commutative ring `R` along with the forgetful functor to `CommAlgCat`.
-/

@[expose] public section

noncomputable section

open Bialgebra Coalgebra Opposite CategoryTheory Limits MonObj
open scoped MonoidalCategory

universe v u
variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of commutative `R`-bialgebras and their morphisms. -/
structure CommBialgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [bialgebra : Bialgebra R carrier]

namespace CommBialgCat
variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

attribute [instance] commRing bialgebra

initialize_simps_projections CommBialgCat (-commRing, -bialgebra)

instance : CoeSort (CommBialgCat R) (Type v) := ⟨carrier⟩

attribute [coe] CommBialgCat.carrier

variable (R) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Turn an unbundled `R`-bialgebra into the corresponding object in the category of `R`-bialgebras.

This is the preferred way to construct a term of `CommBialgCat R`. -/
abbrev of (X : Type v) [CommRing X] [Bialgebra R X] : CommBialgCat.{v} R := ⟨X⟩

variable (R) in
/--
@isnad1 id=eq.0h2v.s5.6a9ec35e2d5f from=seed src=0 shape=1a29407e vocab=f34b0d79
-/
lemma coe_of (X : Type v) [CommRing X] [Bialgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommBialgCat R`. -/
@[ext]
structure Hom (A B : CommBialgCat.{v} R) where
  private mk ::
  /-- The underlying bialgebra map. -/
  hom' : A →ₐc[R] B

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (CommBialgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (CommBialgCat.{v} R) (· →ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommBialgCat` back into a `BialgHom`. -/
abbrev Hom.hom (f : Hom A B) : A →ₐc[R] B := ConcreteCategory.hom (C := CommBialgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `CommBialgCat R`. -/
abbrev ofHom {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (f : X →ₐc[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := CommBialgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommBialgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/--
@isnad1 id=eq.0h2v.s8.43fe9a8a3d9e from=seed src=0 shape=33f0c149 vocab=d8144d4f
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id R A := rfl
/--
@isnad1 id=eq.0h6v.s9.09335a4e3ca5 from=seed src=0 shape=bee14914 vocab=dd9153b1
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
@isnad1 id=eq.0h3v.s10.e51bc904d5ac from=seed src=0 shape=973c5d29 vocab=4ae62193
-/
lemma id_apply (A : CommBialgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp
/--
@isnad1 id=eq.0h7v.s12.ff8c83d2f882 from=seed src=0 shape=63d54618 vocab=38f3f5fa
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

/--
@isnad1 id=eq.1h5v.s8.0f67234fc059 from=seed src=0 shape=fc8760c0 vocab=d640373f
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

/--
@isnad1 id=eq.0h4v.s9.984aa28d7f2e from=seed src=0 shape=b57642be vocab=e1954ceb
-/
@[simp] lemma hom_ofHom (f : X →ₐc[R] Y) : (ofHom f).hom = f := rfl
/--
@isnad1 id=eq.0h4v.s6.960a5d17a4d0 from=seed src=0 shape=c023c5ca vocab=f732fa08
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

/--
@isnad1 id=eq.0h2v.s7.37064bd381c4 from=seed src=0 shape=8244a9e1 vocab=e83265f1
-/
@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

/--
@isnad1 id=eq.0h6v.s9.32711ac65b36 from=seed src=0 shape=8a3aa5f0 vocab=75bb1994
-/
@[simp]
lemma ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/--
@isnad1 id=eq.0h5v.s10.3e21907f90ea from=seed src=0 shape=512fa152 vocab=487c7b39
-/
lemma ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

/--
@isnad1 id=eq.0h5v.s11.3cc5f87d2a97 from=seed src=0 shape=49dee655 vocab=92cd84ea
-/
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
/--
@isnad1 id=eq.0h5v.s11.5d59b734c401 from=seed src=0 shape=ff482979 vocab=92cd84ea
-/
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

instance : Inhabited (CommBialgCat R) := ⟨of R R⟩

/--
@isnad1 id=eq.0h2v.s9.d1d8b33d19b4 from=seed src=0 shape=55f909fa vocab=2e531260
-/
lemma forget_obj (A : CommBialgCat.{v} R) : (forget (CommBialgCat.{v} R)).obj A = A :=
  rfl

/--
@isnad1 id=eq.0h4v.s13.0bbe9f965e06 from=seed src=0 shape=35c89bcd vocab=92379343
-/
@[deprecated ConcreteCategory.forget_map_eq_ofHom (since := "2026-03-06")]
lemma forget_map (f : A ⟶ B) : (forget (CommBialgCat.{v} R)).map f = (f : _ → _) := rfl

instance : CommRing ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| CommRing A

instance : Bialgebra R ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| Bialgebra R A

instance hasForgetToCommAlgCat : HasForget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R) where
  forget₂.obj M := .of R M
  forget₂.map f := CommAlgCat.ofHom f.hom.toAlgHom

/--
@isnad1 id=eq.0h2v.s9.af42fb2a44f7 from=seed src=0 shape=b246d507 vocab=7734ed7e
-/
@[simp] lemma forget₂_commAlgCat_obj (A : CommBialgCat.{v} R) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).obj A = .of R A := rfl

/--
@isnad1 id=eq.0h4v.s11.72f7dc663577 from=seed src=0 shape=ad8e53fc vocab=ef1068c0
-/
@[simp] lemma forget₂_commAlgCat_map (f : A ⟶ B) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).map f =
      CommAlgCat.ofHom f.hom.toAlgHom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
bialgebra. -/
@[simps]
def ofIsoSelf (M : CommBialgCat.{v} R) : of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[deprecated (since := "2026-06-09")] alias ofSelfIso := ofIsoSelf

/-- Build an isomorphism in the category `CommBialgCat R` from a `BialgEquiv` between
`Bialgebra`s. -/
@[simps]
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐc[R] Y)
  inv := ofHom (e.symm : Y →ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommBialgCat R`. -/
@[simps apply, simps -isSimp symm_apply]
def bialgEquivOfIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Bialgebra equivalences between `Bialgebra`s are the same as isomorphisms in `CommBialgCat`. -/
@[simps]
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := bialgEquivOfIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

/--
@isnad1 id=reflects.0h1v.s9.f5876554120b from=seed src=0 shape=2740f13a vocab=e7df3c0f
-/
instance reflectsIsomorphisms_forget : (forget (CommBialgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommBialgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommBialgCat

attribute [local ext] Quiver.Hom.unop_inj

instance CommAlgCat.monObjOpOf {A : Type u} [CommRing A] [Bialgebra R A] :
    MonObj (op <| CommAlgCat.of R A) where
  one := (CommAlgCat.ofHom <| counitAlgHom R A).op
  mul := (CommAlgCat.ofHom <| comulAlgHom R A).op
  one_mul := by ext; exact Coalgebra.rTensor_counit_comul _
  mul_one := by ext; exact Coalgebra.lTensor_counit_comul _
  mul_assoc := by ext; exact (Coalgebra.coassoc_symm_apply _).symm

/--
@isnad1 id=eq.0h2v.s9.a12325a71e30 from=seed src=0 shape=f1e65563 vocab=2ad8613c
-/
@[simp]
lemma CommAlgCat.one_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    η[op <| CommAlgCat.of R A].unop.hom = counitAlgHom R A := rfl

/--
@isnad1 id=eq.0h2v.s9.91fc3219fc4b from=seed src=0 shape=7a27c800 vocab=851292b5
-/
@[simp]
lemma CommAlgCat.mul_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    μ[op <| CommAlgCat.of R A].unop.hom = comulAlgHom R A := rfl

instance {A : Type u} [CommRing A] [Bialgebra R A] [IsCocomm R A] :
    IsCommMonObj (Opposite.op <| CommAlgCat.of R A) where
  mul_comm := by ext; exact comm_comul R _

instance {A B : Type u} [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]
    (f : A →ₐc[R] B) : IsMonHom (CommAlgCat.ofHom f.toAlgHom).op where

instance (A : (CommAlgCat R)ᵒᵖ) [MonObj A] : Bialgebra R A.unop :=
  .ofAlgHom μ[A].unop.hom η[A].unop.hom
    congr(($((MonObj.mul_assoc_flip A).symm)).unop.hom)
    congr(($(MonObj.one_mul A)).unop.hom)
    congr(($(MonObj.mul_one A)).unop.hom)

variable (R) in
/-- Commutative bialgebras over a commutative ring `R` are the same thing as comonoid
`R`-algebras. -/
@[simps! functor_obj_unop_X inverse_obj unitIso_hom_app
  unitIso_inv_app counitIso_hom_app counitIso_inv_app]
def commBialgCatEquivComonCommAlgCat : CommBialgCat R ≌ (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  functor.obj A := .op <| .mk <| .op <| .of R A
  functor.map {A B} f := .op <| .mk' <| .op <| CommAlgCat.ofHom <| f.hom.toAlgHom
  inverse.obj A := .of R A.unop.X.unop
  inverse.map {A B} f := CommBialgCat.ofHom <| .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

/--
@isnad1 id=eq.0h4v.s10.48216fa516fa from=seed src=0 shape=638cd0ce vocab=1ba1c734
-/
@[simp]
lemma commBialgCatEquivComonCommAlgCat_functor_map_unop_hom {A B : CommBialgCat R} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).functor.map f).unop.hom =
    (CommAlgCat.ofHom f.hom.toAlgHom).op := rfl

/--
@isnad1 id=eq.0h4v.s13.d1f28e85964a from=seed src=0 shape=7ddd6f3e vocab=fee23fda
-/
@[simp]
lemma commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom
    {A B : (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).inverse.map f).hom.toAlgHom =
    f.unop.hom.unop.hom := rfl

instance {A : CommBialgCat.{u} R} [IsCocomm R A] :
    IsCommMonObj ((commBialgCatEquivComonCommAlgCat R).functor.obj A).unop.X :=
  inferInstanceAs <| IsCommMonObj <| op <| CommAlgCat.of R A
