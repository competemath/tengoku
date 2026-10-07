/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
public import Tengoku.Seed.RingTheory.Coalgebra.Equiv

/-!
# The category of coalgebras over a commutative ring

We introduce the bundled category `CoalgCat` of coalgebras over a fixed commutative ring `R`
along with the forgetful functor to `ModuleCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-coalgebras. -/
structure CoalgCat extends ModuleCat.{v} R where
  instCoalgebra : Coalgebra R carrier

attribute [instance] CoalgCat.instCoalgebra

variable {R}

namespace CoalgCat

open Coalgebra

instance : CoeSort (CoalgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

/--
@isnad1 id=eq.0h2v.s5.f25e1885bb64 from=seed src=0 shape=0fb5c524 vocab=e78f84b7
-/
@[simp] theorem moduleCat_of_toModuleCat (X : CoalgCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

variable (R) in
/-- The object in the category of `R`-coalgebras associated to an `R`-coalgebra. -/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] [Coalgebra R X] :
    CoalgCat R :=
  { ModuleCat.of R X with
    instCoalgebra := (inferInstance : Coalgebra R X) }

/--
@isnad1 id=eq.0h2v.s8.14243fe334bb from=seed src=0 shape=19ebfb3d vocab=11f7a06b
-/
@[simp]
lemma of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

/--
@isnad1 id=eq.0h2v.s7.5b3b1857ec68 from=seed src=0 shape=ab4925d7 vocab=1a22030e
-/
@[simp]
lemma of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `CoalgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : CoalgCat.{v} R) where
  /-- The underlying `CoalgHom` -/
  toCoalgHom' : V →ₗc[R] W

instance category : Category (CoalgCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨CoalgHom.id R M⟩
  comp f g := ⟨CoalgHom.comp g.toCoalgHom' f.toCoalgHom'⟩

instance concreteCategory : ConcreteCategory (CoalgCat.{v} R) (· →ₗc[R] ·) where
  hom f := f.toCoalgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `CoalgCat` back into a `CoalgHom`. -/
abbrev Hom.toCoalgHom {X Y : CoalgCat.{v} R} (f : Hom X Y) : X →ₗc[R] Y :=
  ConcreteCategory.hom (C := CoalgCat.{v} R) f

/-- Typecheck a `CoalgHom` as a morphism in `CoalgCat R`. -/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Coalgebra R X] [Coalgebra R Y] (f : X →ₗc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

/--
@isnad1 id=injectiv.0h3v.s7.4f1f29422b39 from=seed src=0 shape=d67a5d13 vocab=9b2aef77
-/
lemma Hom.toCoalgHom_injective (V W : CoalgCat.{v} R) :
    Function.Injective (Hom.toCoalgHom' : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

/--
@isnad1 id=eq.1h5v.s7.cd936491ea84 from=seed src=0 shape=c2bb297f vocab=ae94adc3
-/
@[ext]
lemma hom_ext {M N : CoalgCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom) :
    f = g :=
  Hom.ext h

/--
@isnad1 id=eq.0h6v.s9.b3dadde5f3ed from=seed src=0 shape=59761aca vocab=508f8f44
-/
@[simp] theorem toCoalgHom_comp {M N U : CoalgCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toCoalgHom = g.toCoalgHom.comp f.toCoalgHom :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.98d279c6eebc from=seed src=0 shape=8136922c vocab=2798ff81
-/
@[simp] theorem toCoalgHom_id {M : CoalgCat.{v} R} :
    Hom.toCoalgHom (𝟙 M) = CoalgHom.id _ _ :=
  rfl

instance hasForgetToModule : HasForget₂ (CoalgCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toCoalgHom.toLinearMap }

/--
@isnad1 id=eq.0h2v.s9.e6fb8569860d from=seed src=0 shape=6e955027 vocab=c5393d3a
-/
@[simp]
theorem forget₂_obj (X : CoalgCat R) :
    (forget₂ (CoalgCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

/--
@isnad1 id=eq.0h4v.s11.bfea5d22d70e from=seed src=0 shape=c45202bf vocab=023318d6
-/
@[simp]
theorem forget₂_map (X Y : CoalgCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgCat R) (ModuleCat R)).map f = ModuleCat.ofHom (f.toCoalgHom : X →ₗ[R] Y) :=
  rfl

end CoalgCat

namespace CoalgEquiv

open CoalgCat

variable {X Y Z : Type v}
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
variable [Coalgebra R X] [Coalgebra R Y] [Coalgebra R Z]

/-- Build an isomorphism in the category `CoalgCat R` from a
`CoalgEquiv`. -/
@[simps]
def toCoalgIso (e : X ≃ₗc[R] Y) : CoalgCat.of R X ≅ CoalgCat.of R Y where
  hom := CoalgCat.ofHom e
  inv := CoalgCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

/--
@isnad1 id=eq.0h2v.s6.d2350c4e124a from=seed src=0 shape=f9b5c9d8 vocab=686cf7e2
-/
@[simp] theorem toCoalgIso_refl :
    toCoalgIso (CoalgEquiv.refl R X) = .refl _ :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.6c68b4c9041a from=seed src=0 shape=5222a3d3 vocab=1d684b46
-/
@[simp] theorem toCoalgIso_symm (e : X ≃ₗc[R] Y) :
    toCoalgIso e.symm = (toCoalgIso e).symm :=
  rfl

/--
@isnad1 id=eq.0h6v.s8.d9deafb75411 from=seed src=0 shape=cda4193f vocab=6878e2fd
-/
@[simp] theorem toCoalgIso_trans (e : X ≃ₗc[R] Y) (f : Y ≃ₗc[R] Z) :
    toCoalgIso (e.trans f) = toCoalgIso e ≪≫ toCoalgIso f :=
  rfl

end CoalgEquiv

namespace CategoryTheory.Iso

open Coalgebra

variable {X Y Z : CoalgCat.{v} R}

/-- Build a `CoalgEquiv` from an isomorphism in the category
`CoalgCat R`. -/
def toCoalgEquiv (i : X ≅ Y) : X ≃ₗc[R] Y :=
  { i.hom.toCoalgHom with
    invFun := i.inv.toCoalgHom
    left_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.3) x
    right_inv := fun x => CoalgHom.congr_fun (congr_arg CoalgCat.Hom.toCoalgHom i.4) x }

/--
@isnad1 id=eq.0h4v.s9.2935e392cc34 from=seed src=0 shape=2f9768ca vocab=b780a9fc
-/
@[simp] theorem toCoalgEquiv_toCoalgHom (i : X ≅ Y) :
    i.toCoalgEquiv = i.hom.toCoalgHom := rfl

/--
@isnad1 id=eq.0h2v.s8.511b6a9aaedd from=seed src=0 shape=8136922c vocab=edbfb553
-/
@[simp] theorem toCoalgEquiv_refl : toCoalgEquiv (.refl X) = .refl _ _ :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.ae47f66f2f23 from=seed src=0 shape=ebd95204 vocab=8b97a649
-/
@[simp] theorem toCoalgEquiv_symm (e : X ≅ Y) :
    toCoalgEquiv e.symm = (toCoalgEquiv e).symm :=
  rfl

/--
@isnad1 id=eq.0h6v.s8.9d6d01e119fd from=seed src=0 shape=38f03c1b vocab=2c6af405
-/
@[simp] theorem toCoalgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toCoalgEquiv (e ≪≫ f) = e.toCoalgEquiv.trans f.toCoalgEquiv :=
  rfl

end CategoryTheory.Iso

/--
@isnad1 id=reflects.0h1v.s8.fbd1ba6a5522 from=seed src=0 shape=28e8c1e5 vocab=bff0376d
-/
instance CoalgCat.forget_reflects_isos :
    (forget (CoalgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CoalgCat.{v} R)).map f)
    let e : X ≃ₗc[R] Y := { f.toCoalgHom, i.toEquiv with }
    exact ⟨e.toCoalgIso.isIso_hom.1⟩
