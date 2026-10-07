/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.CoalgCat.Basic
public import Tengoku.Seed.Algebra.Category.AlgCat.Basic
public import Tengoku.Seed.RingTheory.Bialgebra.Equiv

/-!
# The category of bialgebras over a commutative ring

We introduce the bundled category `BialgCat` of bialgebras over a fixed commutative ring `R`
along with the forgetful functors to `CoalgCat` and `AlgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of `R`-bialgebras. -/
structure BialgCat where
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instBialgebra : Bialgebra R carrier]

initialize_simps_projections BialgCat (-instRing, -instBialgebra)
attribute [instance] BialgCat.instBialgebra BialgCat.instRing

variable {R}

namespace BialgCat

open Bialgebra

instance : CoeSort (BialgCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩

variable (R) in
/-- The object in the category of `R`-bialgebras associated to an `R`-bialgebra. -/
@[simps]
def of (X : Type v) [Ring X] [Bialgebra R X] :
    BialgCat R where
  carrier := X

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h2v.s8.f85394301e44 from=seed src=0 shape=83cec2c0 vocab=8db64594
-/
@[simp]
lemma of_comul {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h2v.s8.d08bb4122c4b from=seed src=0 shape=a13ffaa3 vocab=605ff04f
-/
@[simp]
lemma of_counit {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

/-- A type alias for `BialgHom` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : BialgCat.{v} R) where
  /-- The underlying `BialgHom` -/
  toBialgHom' : V →ₐc[R] W

instance category : Category (BialgCat.{v} R) where
  Hom X Y := Hom X Y
  id X := ⟨BialgHom.id R X⟩
  comp f g := ⟨BialgHom.comp g.toBialgHom' f.toBialgHom'⟩

instance concreteCategory : ConcreteCategory (BialgCat.{v} R) (· →ₐc[R] ·) where
  hom f := f.toBialgHom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `BialgCat` back into a `BialgHom`. -/
abbrev Hom.toBialgHom {X Y : BialgCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BialgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `BialgCat R`. -/
abbrev ofHom {X Y : Type v} [Ring X] [Ring Y]
    [Bialgebra R X] [Bialgebra R Y] (f : X →ₐc[R] Y) :
    of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

/--
@isnad1 id=injectiv.0h3v.s8.eaa32cb9e42e from=seed src=0 shape=d7cdd3b2 vocab=524af207
-/
lemma Hom.toBialgHom_injective (V W : BialgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.
/--
@isnad1 id=eq.1h5v.s8.67e48216e2fc from=seed src=0 shape=fc8760c0 vocab=f5936973
-/
@[ext]
lemma hom_ext {X Y : BialgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g :=
  Hom.ext h

/--
@isnad1 id=eq.0h6v.s9.c231d529f168 from=seed src=0 shape=bee14914 vocab=19d88ad9
-/
@[simp] theorem toBialgHom_comp {X Y Z : BialgCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toBialgHom = g.toBialgHom.comp f.toBialgHom :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.c91e16fdaa3c from=seed src=0 shape=33f0c149 vocab=bb31d19e
-/
@[simp] theorem toBialgHom_id {M : BialgCat.{v} R} :
    Hom.toBialgHom (𝟙 M) = BialgHom.id _ _ :=
  rfl

instance hasForgetToAlgebra : HasForget₂ (BialgCat R) (AlgCat R) where
  forget₂ :=
    { obj := fun X => AlgCat.of R X
      map := fun {X Y} f => AlgCat.ofHom f.toBialgHom }

/--
@isnad1 id=eq.0h2v.s9.4d113b483dd9 from=seed src=0 shape=b246d507 vocab=72f95c4b
-/
@[simp]
theorem forget₂_algebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (AlgCat R)).obj X = AlgCat.of R X :=
  rfl

/--
@isnad1 id=eq.0h4v.s11.9133263e67d8 from=seed src=0 shape=ad8e53fc vocab=b298b82c
-/
@[simp]
theorem forget₂_algebra_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (AlgCat R)).map f = AlgCat.ofHom f.toBialgHom :=
  rfl

instance hasForgetToCoalgebra : HasForget₂ (BialgCat R) (CoalgCat R) where
  forget₂ :=
    { obj := fun X => CoalgCat.of R X
      map := fun {_ _} f => CoalgCat.ofHom f.toBialgHom }

/--
@isnad1 id=eq.0h2v.s10.ead8405d1f51 from=seed src=0 shape=370fcb58 vocab=8945626a
-/
@[simp]
theorem forget₂_coalgebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (CoalgCat R)).obj X = CoalgCat.of R X :=
  rfl

/--
@isnad1 id=eq.0h4v.s11.42458d9a53c4 from=seed src=0 shape=db1a92a6 vocab=1dbfe1d1
-/
@[simp]
theorem forget₂_coalgebra_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (CoalgCat R)).map f = CoalgCat.ofHom f.toBialgHom :=
  rfl

end BialgCat

namespace BialgEquiv

open BialgCat

variable {X Y Z : Type v}
variable [Ring X] [Ring Y] [Ring Z]
variable [Bialgebra R X] [Bialgebra R Y] [Bialgebra R Z]

/-- Build an isomorphism in the category `BialgCat R` from a
`BialgEquiv`. -/
@[simps]
def toBialgIso (e : X ≃ₐc[R] Y) : BialgCat.of R X ≅ BialgCat.of R Y where
  hom := BialgCat.ofHom e
  inv := BialgCat.ofHom e.symm
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv

/--
@isnad1 id=eq.0h2v.s6.f419e1344aad from=seed src=0 shape=047d547d vocab=1ef9bd6b
-/
@[simp] theorem toBialgIso_refl : toBialgIso (BialgEquiv.refl R X) = .refl _ :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.fe5bfa13d2bd from=seed src=0 shape=706674b8 vocab=160f1f75
-/
@[simp] theorem toBialgIso_symm (e : X ≃ₐc[R] Y) :
    toBialgIso e.symm = (toBialgIso e).symm :=
  rfl

/--
@isnad1 id=eq.0h6v.s9.c9c911ff6c44 from=seed src=0 shape=f1af3133 vocab=7020d527
-/
@[simp] theorem toBialgIso_trans (e : X ≃ₐc[R] Y) (f : Y ≃ₐc[R] Z) :
    toBialgIso (e.trans f) = toBialgIso e ≪≫ toBialgIso f :=
  rfl

end BialgEquiv

namespace CategoryTheory.Iso

open Bialgebra

variable {X Y Z : BialgCat.{v} R}

/-- Build a `BialgEquiv` from an isomorphism in the category
`BialgCat R`. -/
def toBialgEquiv (i : X ≅ Y) : X ≃ₐc[R] Y :=
  { i.hom.toBialgHom with
    invFun := i.inv.toBialgHom
    left_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.3) x
    right_inv := fun x => BialgHom.congr_fun (congr_arg BialgCat.Hom.toBialgHom i.4) x }

/--
@isnad1 id=eq.0h4v.s10.6ef32c80ef11 from=seed src=0 shape=a47a2bd7 vocab=fc2f1eda
-/
@[simp] theorem toBialgEquiv_toBialgHom (i : X ≅ Y) :
    (i.toBialgEquiv : X →ₐc[R] Y) = i.hom.1 := rfl

/--
@isnad1 id=eq.0h2v.s8.fc5d05dddcb8 from=seed src=0 shape=33f0c149 vocab=e1ca0f5b
-/
@[simp] theorem toBialgEquiv_refl : toBialgEquiv (.refl X) = .refl _ _ :=
  rfl

/--
@isnad1 id=eq.0h4v.s9.7fc176d23e25 from=seed src=0 shape=c8ca355b vocab=40f15cc7
-/
@[simp] theorem toBialgEquiv_symm (e : X ≅ Y) :
    toBialgEquiv e.symm = (toBialgEquiv e).symm :=
  rfl

/--
@isnad1 id=eq.0h6v.s9.e3080d39f72d from=seed src=0 shape=b1d58bef vocab=4c8bb140
-/
@[simp] theorem toBialgEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toBialgEquiv (e ≪≫ f) = e.toBialgEquiv.trans f.toBialgEquiv :=
  rfl

end CategoryTheory.Iso

/--
@isnad1 id=reflects.0h1v.s9.110b779e9474 from=seed src=0 shape=2740f13a vocab=6cd6fe49
-/
instance BialgCat.forget_reflects_isos :
    (forget (BialgCat.{v} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (BialgCat.{v} R)).map f)
    let e : X ≃ₐc[R] Y := { f.toBialgHom, i.toEquiv with }
    exact ⟨e.toBialgIso.isIso_hom.1⟩
