/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.PEmptyInstances
public import Tengoku.Seed.Algebra.Group.Equiv.Defs
public import Tengoku.Seed.CategoryTheory.ConcreteCategory.Forget
public import Tengoku.Seed.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Category instances for `Mul`, `Add`, `Semigroup` and `AddSemigroup`

We introduce the bundled categories:
* `MagmaCat`
* `AddMagmaCat`
* `Semigrp`
* `AddSemigrp`

along with the relevant forgetful functors between them.

This closely follows `Mathlib/Algebra/Category/MonCat/Basic.lean`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/

@[expose] public section


universe u v

open CategoryTheory

/-- The category of additive magmas and additive magma morphisms. -/
structure AddMagmaCat : Type (u + 1) where
  /-- The underlying additive magma. -/
  (carrier : Type u)
  [str : Add carrier]

/-- The category of magmas and magma morphisms. -/
@[to_additive]
structure MagmaCat : Type (u + 1) where
  /-- The underlying magma. -/
  (carrier : Type u)
  [str : Mul carrier]

attribute [instance] AddMagmaCat.str MagmaCat.str

initialize_simps_projections AddMagmaCat (carrier → coe, -str)
initialize_simps_projections MagmaCat (carrier → coe, -str)

namespace MagmaCat

@[to_additive]
instance : CoeSort MagmaCat (Type u) :=
  ⟨MagmaCat.carrier⟩

attribute [coe] AddMagmaCat.carrier MagmaCat.carrier

/-- Construct a bundled `MagmaCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddMagmaCat` from the underlying type and typeclass. -/]
abbrev of (M : Type u) [Mul M] : MagmaCat := ⟨M⟩

end MagmaCat

/-- The type of morphisms in `AddMagmaCat R`. -/
@[ext]
structure AddMagmaCat.Hom (A B : AddMagmaCat.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A →ₙ+ B

/-- The type of morphisms in `MagmaCat R`. -/
@[to_additive, ext]
structure MagmaCat.Hom (A B : MagmaCat.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A →ₙ* B

namespace MagmaCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : Category MagmaCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : ConcreteCategory MagmaCat (· →ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MagmaCat` back into a `MulHom`. -/
@[to_additive /-- Turn a morphism in `AddMagmaCat` back into an `AddHom`. -/]
abbrev Hom.hom {X Y : MagmaCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := MagmaCat) f

/-- Typecheck a `MulHom` as a morphism in `MagmaCat`. -/
@[to_additive /-- Typecheck an `AddHom` as a morphism in `AddMagmaCat`. -/]
abbrev ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := MagmaCat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : MagmaCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddMagmaCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/--
@isnad1 id=eq.0h1v.s6.3f25656a7222 from=seed src=0 shape=bae0b6c4 vocab=2066886b
-/
@[to_additive (attr := simp)]
lemma coe_id {X : MagmaCat} : (𝟙 X : X → X) = id := rfl

/--
@isnad1 id=eq.0h5v.s8.269736cb1c06 from=seed src=0 shape=bfb9d4a0 vocab=bccd52ae
-/
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : MagmaCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

/--
@isnad1 id=eq.0h6v.s7.9a0e06912c37 from=seed src=0 shape=2362f298 vocab=77008646
-/
@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/--
@isnad1 id=eq.1h4v.s7.c061ecb7fc92 from=seed src=0 shape=2fe9d3b5 vocab=035cef16
-/
@[to_additive (attr := ext)]
lemma ext {X Y : MagmaCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

/--
@isnad1 id=eq.0h1v.s3.6eb0c0adf466 from=seed src=0 shape=62728698 vocab=c610057e
-/
@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (M : Type u) [Mul M] : (MagmaCat.of M : Type u) = M := rfl

/--
@isnad1 id=eq.0h1v.s4.0d359ec84c32 from=seed src=0 shape=98150753 vocab=89f92a18
-/
@[to_additive (attr := simp)]
lemma hom_id {M : MagmaCat} : (𝟙 M : M ⟶ M).hom = MulHom.id M := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h2v.s6.cc0b493d2b9b from=seed src=0 shape=567e892f vocab=24783fe5
-/
@[to_additive]
lemma id_apply (M : MagmaCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

/--
@isnad1 id=eq.0h5v.s6.c2fb053fac19 from=seed src=0 shape=f9bc9902 vocab=3cbdd879
-/
@[to_additive (attr := simp)]
lemma hom_comp {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h6v.s8.7dcdbcd0eb10 from=seed src=0 shape=f8fbaaa5 vocab=bfa1c7a7
-/
@[to_additive]
lemma comp_apply {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

/--
@isnad1 id=eq.1h4v.s5.e44c60aa00d5 from=seed src=0 shape=bce286ca vocab=a03faa3d
-/
@[to_additive (attr := ext)]
lemma hom_ext {M N : MagmaCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/--
@isnad1 id=eq.0h3v.s5.aa4c7b1781b6 from=seed src=0 shape=ee82f57b vocab=99900333
-/
@[to_additive (attr := simp)]
lemma hom_ofHom {M N : Type u} [Mul M] [Mul N] (f : M →ₙ* N) : (ofHom f).hom = f := rfl

/--
@isnad1 id=eq.0h3v.s5.c37d61879b9c from=seed src=0 shape=67807d68 vocab=4101e015
-/
@[to_additive (attr := simp)]
lemma ofHom_hom {M N : MagmaCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

/--
@isnad1 id=eq.0h1v.s5.8d34823ab65e from=seed src=0 shape=fa1b0b56 vocab=ec578003
-/
@[to_additive (attr := simp)]
lemma ofHom_id {M : Type u} [Mul M] : ofHom (MulHom.id M) = 𝟙 (of M) := rfl

/--
@isnad1 id=eq.0h5v.s6.3d8606314a80 from=seed src=0 shape=17e991ae vocab=60bcace7
-/
@[to_additive (attr := simp)]
lemma ofHom_comp {M N P : Type u} [Mul M] [Mul N] [Mul P]
    (f : M →ₙ* N) (g : N →ₙ* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.1ee4ddbe0906 from=seed src=0 shape=c7895988 vocab=be17e381
-/
@[to_additive]
lemma ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
@isnad1 id=eq.0h4v.s7.77fb74e48077 from=seed src=0 shape=a6fcc484 vocab=3cac73cf
-/
@[to_additive]
lemma inv_hom_apply {M N : MagmaCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

/--
@isnad1 id=eq.0h4v.s7.c1daca04da9e from=seed src=0 shape=f8bdf8bf vocab=3cac73cf
-/
@[to_additive]
lemma hom_inv_apply {M N : MagmaCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

/--
@isnad1 id=eq.0h3v.s6.212bccad80e0 from=seed src=0 shape=b360b6c4 vocab=ec352e4c
-/
@[to_additive (attr := simp)]
lemma mulEquiv_coe_eq {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
instance : Inhabited MagmaCat :=
  ⟨MagmaCat.of PEmpty⟩

end MagmaCat

/-- The category of additive semigroups and semigroup morphisms. -/
structure AddSemigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddSemigroup carrier]

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive]
structure Semigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Semigroup carrier]

attribute [instance] AddSemigrp.str Semigrp.str

initialize_simps_projections AddSemigrp (carrier → coe, -str)
initialize_simps_projections Semigrp (carrier → coe, -str)

namespace Semigrp

@[to_additive]
instance : CoeSort Semigrp (Type u) :=
  ⟨Semigrp.carrier⟩

attribute [coe] AddSemigrp.carrier Semigrp.carrier

/-- Construct a bundled `Semigrp` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddSemigrp` from the underlying type and typeclass. -/]
abbrev of (M : Type u) [Semigroup M] : Semigrp := ⟨M⟩

end Semigrp

/-- The type of morphisms in `AddSemigrp R`. -/
@[ext]
structure AddSemigrp.Hom (A B : AddSemigrp.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A →ₙ+ B

/-- The type of morphisms in `Semigrp R`. -/
@[to_additive, ext]
structure Semigrp.Hom (A B : Semigrp.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A →ₙ* B

namespace Semigrp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : Category Semigrp.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : ConcreteCategory Semigrp (· →ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Semigrp` back into a `MulHom`. -/
@[to_additive /-- Turn a morphism in `AddSemigrp` back into an `AddHom`. -/]
abbrev Hom.hom {X Y : Semigrp.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Semigrp) f

/-- Typecheck a `MulHom` as a morphism in `Semigrp`. -/
@[to_additive /-- Typecheck an `AddHom` as a morphism in `AddSemigrp`. -/]
abbrev ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Semigrp) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : Semigrp.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddSemigrp.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/--
@isnad1 id=eq.0h1v.s6.3cdb7051088c from=seed src=0 shape=bae0b6c4 vocab=e9331294
-/
@[to_additive (attr := simp)]
lemma coe_id {X : Semigrp} : (𝟙 X : X → X) = id := rfl

/--
@isnad1 id=eq.0h5v.s8.f39e037134eb from=seed src=0 shape=bfb9d4a0 vocab=0463ab05
-/
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

/--
@isnad1 id=eq.0h6v.s7.9a0e06912c37 from=seed src=0 shape=2362f298 vocab=77008646
-/
@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/--
@isnad1 id=eq.1h4v.s7.9d3f95fce7ba from=seed src=0 shape=2fe9d3b5 vocab=64e8cc70
-/
@[to_additive (attr := ext)]
lemma ext {X Y : Semigrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

/--
@isnad1 id=eq.0h1v.s3.b5388a44faae from=seed src=0 shape=62728698 vocab=0cdbf81e
-/
@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (R : Type u) [Semigroup R] : ↑(Semigrp.of R) = R :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.46e47dafcad9 from=seed src=0 shape=98150753 vocab=2812eea8
-/
@[to_additive (attr := simp)]
lemma hom_id {X : Semigrp} : (𝟙 X : X ⟶ X).hom = MulHom.id X := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h2v.s6.95e4e2c172c5 from=seed src=0 shape=567e892f vocab=53b18cf6
-/
@[to_additive]
lemma id_apply (X : Semigrp) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

/--
@isnad1 id=eq.0h5v.s6.fe5ea2acefb0 from=seed src=0 shape=f9bc9902 vocab=75d5975e
-/
@[to_additive (attr := simp)]
lemma hom_comp {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h6v.s8.058d9bd9a62b from=seed src=0 shape=f8fbaaa5 vocab=1879d0dc
-/
@[to_additive]
lemma comp_apply {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

/--
@isnad1 id=eq.1h4v.s5.07b52d169796 from=seed src=0 shape=bce286ca vocab=d449ac09
-/
@[to_additive (attr := ext)]
lemma hom_ext {X Y : Semigrp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/--
@isnad1 id=eq.0h3v.s5.25d5098d7f2d from=seed src=0 shape=ee82f57b vocab=31b53c1d
-/
@[to_additive (attr := simp)]
lemma hom_ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : (ofHom f).hom = f := rfl

/--
@isnad1 id=eq.0h3v.s5.9faa3a506908 from=seed src=0 shape=67807d68 vocab=d107d78d
-/
@[to_additive (attr := simp)]
lemma ofHom_hom {X Y : Semigrp} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

/--
@isnad1 id=eq.0h1v.s5.e86e10b31665 from=seed src=0 shape=fa1b0b56 vocab=758f113a
-/
@[to_additive (attr := simp)]
lemma ofHom_id {X : Type u} [Semigroup X] : ofHom (MulHom.id X) = 𝟙 (of X) := rfl

/--
@isnad1 id=eq.0h5v.s6.2c9a5df788d3 from=seed src=0 shape=17e991ae vocab=6a80f63a
-/
@[to_additive (attr := simp)]
lemma ofHom_comp {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z]
    (f : X →ₙ* Y) (g : Y →ₙ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.88bec70327ff from=seed src=0 shape=c7895988 vocab=4f778566
-/
@[to_additive]
lemma ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
@isnad1 id=eq.0h4v.s7.7eb54246469a from=seed src=0 shape=a6fcc484 vocab=c037a367
-/
@[to_additive]
lemma inv_hom_apply {X Y : Semigrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
@isnad1 id=eq.0h4v.s7.b37e667c6c92 from=seed src=0 shape=f8bdf8bf vocab=c037a367
-/
@[to_additive]
lemma hom_inv_apply {X Y : Semigrp} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
@isnad1 id=eq.0h3v.s7.2c777bf5dbfd from=seed src=0 shape=b360b6c4 vocab=617f1f18
-/
@[to_additive (attr := simp)]
lemma mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
instance : Inhabited Semigrp :=
  ⟨Semigrp.of PEmpty⟩

@[to_additive]
instance hasForgetToMagmaCat : HasForget₂ Semigrp MagmaCat where
  forget₂ :=
    { obj R := MagmaCat.of R
      map f := MagmaCat.ofHom f.hom }

end Semigrp

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `MagmaCat` from a `MulEquiv` between `Mul`s. -/
@[to_additive (attr := simps)
      /-- Build an isomorphism in the category `AddMagmaCat` from an `AddEquiv` between `Add`s. -/]
def MulEquiv.toMagmaCatIso (e : X ≃* Y) : MagmaCat.of X ≅ MagmaCat.of Y where
  hom := MagmaCat.ofHom e.toMulHom
  inv := MagmaCat.ofHom e.symm.toMulHom

end

section

variable [Semigroup X] [Semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `MulEquiv` between `Semigroup`s. -/
@[to_additive (attr := simps)
  /-- Build an isomorphism in the category
  `AddSemigroup` from an `AddEquiv` between `AddSemigroup`s. -/]
def MulEquiv.toSemigrpIso (e : X ≃* Y) : Semigrp.of X ≅ Semigrp.of Y where
  hom := Semigrp.ofHom e.toMulHom
  inv := Semigrp.ofHom e.symm.toMulHom

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MagmaCat`. -/
@[to_additive
      /-- Build an `AddEquiv` from an isomorphism in the category `AddMagmaCat`. -/]
def magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `MulEquiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive
  /-- Build an `AddEquiv` from an isomorphism in the category `AddSemigroup`. -/]
def semigrpIsoToMulEquiv {X Y : Semigrp} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso

/-- multiplicative equivalences between `Mul`s are the same as (isomorphic to) isomorphisms
in `MagmaCat` -/
@[to_additive
    /-- additive equivalences between `Add`s are the same
    as (isomorphic to) isomorphisms in `AddMagmaCat` -/]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] :
    (X ≃* Y) ≅ (MagmaCat.of X ≅ MagmaCat.of Y) where
  hom := ↾fun e ↦ e.toMagmaCatIso
  inv := ↾fun i ↦ i.magmaCatIsoToMulEquiv

/-- multiplicative equivalences between `Semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive
  /-- additive equivalences between `AddSemigroup`s are
  the same as (isomorphic to) isomorphisms in `AddSemigroup` -/]
def mulEquivIsoSemigrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    (X ≃* Y) ≅ (Semigrp.of X ≅ Semigrp.of Y) where
  hom := ↾fun e ↦ e.toSemigrpIso
  inv := ↾fun i ↦ i.semigrpIsoToMulEquiv

/--
@isnad1 id=reflects.0h0v.s5.25cc3c5685c7 from=seed src=0 shape=397b964b vocab=61091ef4
-/
@[to_additive]
instance MagmaCat.forgetReflectsIsos : (forget MagmaCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMagmaCatIso.isIso_hom

/--
@isnad1 id=reflects.0h0v.s5.77c8a05ce9cb from=seed src=0 shape=397b964b vocab=0094741f
-/
@[to_additive]
instance Semigrp.forgetReflectsIsos : (forget Semigrp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget Semigrp).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toSemigrpIso.isIso_hom

/-- Ensure that `forget₂ CommMonCat MonCat` automatically reflects isomorphisms.
@isnad1 id=full.0h0v.s6.0a06db5345d8 from=seed src=0 shape=343ac400 vocab=4a3ee2fe
-/
@[to_additive /-- Ensure that `forget₂ AddCommMonCat AddMonCat` automatically reflects
isomorphisms. -/]
instance Semigrp.forget₂_full : (forget₂ Semigrp MagmaCat).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/

example : (forget₂ Semigrp MagmaCat).ReflectsIsomorphisms := inferInstance
