/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.CommAlgCat.Basic
public import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The co-Cartesian monoidal category structure on commutative `R`-algebras

This file provides the co-Cartesian-monoidal category structure on `CommAlgCat R` constructed
explicitly using the tensor product.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits TensorProduct Opposite
open Algebra.TensorProduct
open Algebra.TensorProduct (lid rid assoc comm)

noncomputable section

namespace CommAlgCat
universe u v
variable {R : Type u} [CommRing R] {A B C D : CommAlgCat.{u} R}

variable (A B)

/-- The explicit cocone with tensor products as the fibered coproduct in `CommAlgCat`. -/
def binaryCofan : BinaryCofan A B := .mk (ofHom includeLeft) (ofHom <| includeRight (A := A))

/--
@isnad1 id=eq.0h3v.s8.ce6e88b85b4b from=seed src=0 shape=7b6960fb vocab=45d9345e
-/
@[simp] lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom includeLeft := rfl
/--
@isnad1 id=eq.0h3v.s8.edd9b5a1cd7e from=seed src=0 shape=8f729ac5 vocab=754db27d
-/
@[simp] lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom includeRight := rfl
/--
@isnad1 id=eq.0h3v.s7.1ebc1eb71888 from=seed src=0 shape=0255054a vocab=a8489fd6
-/
@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

/-- Verify that the pushout cocone is indeed the colimit. -/
def binaryCofanIsColimit : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ofHom (lift f.hom g.hom fun _ _ ↦ .all _ _))
    (fun f g ↦ by ext1; exact lift_comp_includeLeft _ _ fun _ _ ↦ .all _ _)
    (fun f g ↦ by ext1; exact lift_comp_includeRight _ _ fun _ _ ↦ .all _ _)
    (fun f g m hm₁ hm₂ ↦ by
      ext1
      refine liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ ↦ .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

/-- The initial object of `CommAlgCat R` is `R` as an algebra over itself. -/
def isInitialSelf : IsInitial (of R R) :=
  .ofUniqueHom (fun A ↦ ofHom (Algebra.ofId R A)) fun _ _ ↦ hom_ext (Algebra.ext_id _ _ _)

attribute [local simp] one_def in
instance : MonoidalCategory (CommAlgCat.{u} R) where
  tensorObj S T := of R (S ⊗[R] T)
  whiskerLeft _ {_ _} f := ofHom (map (.id _ _) f.hom)
  whiskerRight f T := ofHom (map f.hom (.id _ _))
  tensorHom f g := ofHom (map f.hom g.hom)
  tensorUnit := .of R R
  associator _ _ _ := isoMk (assoc R R R _ _ _)
  leftUnitor _ := isoMk (lid R _)
  rightUnitor _ := isoMk (rid R R _)

/--
@isnad1 id=eq.0h1v.s4.292937d7047f from=seed src=0 shape=c8bba8de vocab=e87e129d
-/
@[simp] lemma coe_tensorUnit : 𝟙_ (CommAlgCat.{u} R) = R := rfl

/--
@isnad1 id=eq.0h3v.s7.5c943432048e from=seed src=0 shape=9e9ee682 vocab=0c5f2dc5
-/
@[simp] lemma coe_tensorObj : A ⊗ B = A ⊗[R] B := rfl

variable {A B}

/--
@isnad1 id=eq.0h7v.s8.257ac5784263 from=seed src=0 shape=7bd967ff vocab=fe97708a
-/
@[simp] lemma tensorHom_hom (f : A ⟶ C) (g : B ⟶ D) : (f ⊗ₘ g).hom = map f.hom g.hom := rfl

variable (C) in
/--
@isnad1 id=eq.0h5v.s8.c2fb58f8c657 from=seed src=0 shape=0fd31f77 vocab=c28e22e3
-/
@[simp] lemma whiskerRight_hom (f : A ⟶ B) : (f ▷ C).hom = map f.hom (.id _ _) := rfl

variable (C) in
/--
@isnad1 id=eq.0h5v.s8.2c9021dca7d3 from=seed src=0 shape=2a3f34ee vocab=4b262337
-/
@[simp] lemma whiskerLeft_hom (f : A ⟶ B) : (C ◁ f).hom = map (.id _ _) f.hom := rfl

variable (A B C) in
/--
@isnad1 id=eq.0h4v.s11.2685c874d1cc from=seed src=0 shape=6d0d849d vocab=1c350ef8
-/
@[simp] lemma associator_hom_hom : (α_ A B C).hom.hom = (assoc R R R A B C).toAlgHom := rfl

variable (A B C) in
/--
@isnad1 id=eq.0h4v.s12.00ea653d17d9 from=seed src=0 shape=c45f2ed4 vocab=9a1d6bd8
-/
@[simp] lemma associator_inv_hom : (α_ A B C).inv.hom = (assoc R R R A B C).symm.toAlgHom := rfl

instance : BraidedCategory (CommAlgCat.{u} R) where
  braiding S T := isoMk (comm R _ _)
  braiding_naturality_right := by intros; ext : 1; dsimp; ext <;> rfl
  braiding_naturality_left := by intros; ext : 1; dsimp; ext <;> rfl
  hexagon_forward S T U := by ext : 1; dsimp; ext <;> rfl
  hexagon_reverse S T U := by ext : 1; dsimp; ext <;> rfl

variable (A B) in
/--
@isnad1 id=eq.0h3v.s9.ea21f30e91c1 from=seed src=0 shape=678af2b1 vocab=7874974c
-/
@[simp] lemma braiding_hom_hom : (β_ A B).hom.hom = (comm R A B).toAlgHom := rfl

variable (A B) in
/--
@isnad1 id=eq.0h3v.s9.844cf72561e9 from=seed src=0 shape=6f562ad9 vocab=6b4c2382
-/
@[simp] lemma braiding_inv_hom : (β_ A B).inv.hom = (comm R B A).toAlgHom := rfl

attribute [local ext] Quiver.Hom.unop_inj in
instance : CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  isTerminalTensorUnit := terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
  tensorProductIsBinaryProduct S T := BinaryCofan.IsColimit.op <| binaryCofanIsColimit S.unop T.unop
  fst_def S T := by ext x; change x ⊗ₜ 1 = x ⊗ₜ algebraMap R T.unop 1; simp
  snd_def S T := by ext x; change 1 ⊗ₜ x = algebraMap R S.unop 1 ⊗ₜ x; simp

variable {A B C : (CommAlgCat.{u} R)ᵒᵖ}

/--
@isnad1 id=eq.0h3v.s9.8c5b46735ff2 from=seed src=0 shape=4f6d3fd0 vocab=429758e3
-/
@[simp] lemma fst_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (fst A B).unop.hom = includeLeft := rfl
/--
@isnad1 id=eq.0h3v.s9.6fc2f2825375 from=seed src=0 shape=8414fe4c vocab=4d707b0f
-/
@[simp] lemma snd_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (snd A B).unop.hom = includeRight := rfl

variable (A B) in
/--
@isnad1 id=eq.0h2v.s9.73aeaf0abd7f from=seed src=0 shape=489868e0 vocab=7d694e97
-/
@[simp] lemma toUnit_unop_hom : (toUnit A).unop.hom = Algebra.ofId R A.unop := rfl

/--
@isnad1 id=eq.0h6v.s9.d38fc6fa17e9 from=seed src=0 shape=8075f030 vocab=030213d1
-/
@[simp] lemma lift_unop_hom (f : C ⟶ A) (g : C ⟶ B) :
    (lift f g).unop.hom = lift f.unop.hom g.unop.hom fun _ _ ↦ .all _ _ := rfl

end CommAlgCat
