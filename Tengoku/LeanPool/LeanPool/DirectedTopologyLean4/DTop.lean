/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.Constructions
public import Tengoku

/-!
# LeanPool.DirectedTopologyLean4.DTop
-/

@[expose] public section

/-
  This file contains the definition of `dTopCat`, the category of directed spaces.
  The structure of this file is based on the approach for the undirected version in Mathlib:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Category/TopCat/Basic.lean
-/

open DirectedMap
open CategoryTheory

universe u

/-- The category of directed topological spaces. -/
structure dTopCat where
  /-- The underlying type of a directed topological space. -/
  carrier : Type u
  [str : DirectedSpace carrier]

namespace dTopCat

attribute [instance] dTopCat.str

instance : CoeSort dTopCat (Type u) := ⟨dTopCat.carrier⟩

attribute [coe] dTopCat.carrier

/-- Construct a bundled `dTopCat` from the underlying type and the typeclass. -/
def of (X : Type u) [DirectedSpace X] : dTopCat := ⟨X⟩

/--
@isnad1 id=eq.0h1v.s3.6dfe5fc4be68 from=translated src=- shape=62728698 vocab=290baef6
-/
@[simp]
lemma coe_of (X : Type u) [DirectedSpace X] : (of X : Type u) = X := rfl

/-- The type of morphisms in `dTopCat`. -/
@[ext]
structure Hom (X Y : dTopCat.{u}) where
  /-- The underlying `DirectedMap`. -/
  hom' : D(X,Y)

instance : Category dTopCat where
  Hom X Y := Hom X Y
  id X := ⟨DirectedMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance concreteCategory : ConcreteCategory.{u} dTopCat (fun X Y => D(X,Y)) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

namespace Hom

/-- Turn a morphism in `dTopCat` back into a `DirectedMap`. -/
abbrev hom {X Y : dTopCat.{u}} (f : Hom X Y) : D(X,Y) :=
  ConcreteCategory.hom (C := dTopCat) f

end Hom

/-- Typecheck a `DirectedMap` as a morphism in `dTopCat`. -/
abbrev ofHom {X Y : Type u} [DirectedSpace X] [DirectedSpace Y] (f : D(X,Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := dTopCat) f

/--
@isnad1 id=eq.0h1v.s4.0ed909bd4a4d from=translated src=- shape=98150753 vocab=ced30f81
-/
@[simp]
lemma hom_id {X : dTopCat.{u}} : (𝟙 X : X ⟶ X).hom = DirectedMap.id X := rfl

/--
@isnad1 id=eq.0h2v.s6.b1a0a6bd4252 from=translated src=- shape=567e892f vocab=35f986d7
-/
@[simp]
lemma id_app (X : dTopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

/--
@isnad1 id=eq.0h5v.s6.d299847287ad from=translated src=- shape=f9bc9902 vocab=0dd8ae26
-/
@[simp]
lemma hom_comp {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
@isnad1 id=eq.0h6v.s8.09f1c84318cc from=translated src=- shape=f8fbaaa5 vocab=64a29da2
-/
@[simp]
lemma comp_app {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

/--
@isnad1 id=eq.1h4v.s5.da1a4c546ea3 from=translated src=- shape=bce286ca vocab=15252e88
-/
@[ext]
lemma hom_ext {X Y : dTopCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g := Hom.ext hf

/--
@isnad1 id=eq.1h4v.s7.b53e2bf97be5 from=translated src=- shape=2fe9d3b5 vocab=f0271db4
-/
@[ext]
lemma ext {X Y : dTopCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

/--
@isnad1 id=eq.0h3v.s5.78ea495b67a6 from=translated src=- shape=ee82f57b vocab=09013d61
-/
@[simp]
lemma hom_ofHom {X Y : Type u} [DirectedSpace X] [DirectedSpace Y] (f : D(X,Y)) :
    (ofHom f).hom = f := rfl

/--
@isnad1 id=eq.0h3v.s5.86d2e82a8497 from=translated src=- shape=67807d68 vocab=b269bfec
-/
@[simp]
lemma ofHom_hom {X Y : dTopCat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

/--
@isnad1 id=eq.0h1v.s5.32b1e8dfadd5 from=translated src=- shape=fa1b0b56 vocab=6e7c8c13
-/
@[simp]
lemma ofHom_id {X : Type u} [DirectedSpace X] : ofHom (DirectedMap.id X) = 𝟙 (of X) := rfl

/--
@isnad1 id=eq.0h5v.s6.c1378b9aa626 from=translated src=- shape=17e991ae vocab=8ddba3a8
-/
@[simp]
lemma ofHom_comp {X Y Z : Type u} [DirectedSpace X] [DirectedSpace Y] [DirectedSpace Z]
    (f : D(X,Y)) (g : D(Y,Z)) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

instance subspaceCoe {X : dTopCat} : CoeTC (Set X) dTopCat := ⟨fun s => dTopCat.of s⟩

/-- The inclusion of a directed subspace into its ambient space. -/
def DirectedSubtypeHom {X : dTopCat} (Y : Set X) : (dTopCat.of Y) ⟶ X :=
  ofHom (DirectedSubtypeInclusion (fun s => s ∈ Y))

/-- The inclusion between two directed subspaces, given a subset relation. -/
def DirectedSubsetHom {X : dTopCat} {Y₀ Y₁ : Set X} (h : Y₀ ⊆ Y₁) : (dTopCat.of Y₀) ⟶ Y₁ :=
  ofHom (DirectedSubsetInclusion h)

end dTopCat
