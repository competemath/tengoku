/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Lift
public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Sum
public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Sigma
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Hom

/-!
# Binary Coproducts of Quasi-Borel Spaces

This file defines binary coproducts of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· ⊕ ·` type.

See [HeunenKSY17], Proposition 17.
-/

@[expose] public section

namespace QuasiBorelSpace.Sum

universe u v

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]
  {E : Type*} [QuasiBorelSpace E]

/--
We derive the `QuasiBorelSpace` instance for `A ⊕ B` via `Sigma (Encoding A B)`.
-/
def Encoding (A : Type u) (B : Type v) : Bool → Type (max u v)
  | true => ULift A
  | false => ULift B

namespace Encoding

/-- The encoded version of `Sum.inl`. -/
def inl (x : A) : Sigma (Encoding A B) := ⟨true, ⟨x⟩⟩

/-- The encoded version of `Sum.inr`. -/
def inr (x : B) : Sigma (Encoding A B) := ⟨false, ⟨x⟩⟩

/-- The encoded version of `Sum.elim`. -/
def elim (f : A → C) (g : B → C) : Sigma (Encoding A B) → C
  | ⟨true, x⟩ => f x.down
  | ⟨false, x⟩ => g x.down

instance {b : Bool} : QuasiBorelSpace (Encoding A B b) := by
  cases b <;>
  · dsimp only [Encoding]
    infer_instance

/--
@isnad1 id=ishom.0h2v.s5.a40d9afadd23 from=translated src=- shape=4413ecef vocab=c4872700
-/
@[fun_prop]
lemma isHom_inl : IsHom (inl (A := A) (B := B)) := by
  unfold inl
  fun_prop

/--
@isnad1 id=ishom.0h2v.s5.8516dc1436c3 from=translated src=- shape=bb32ff57 vocab=3c869d7a
-/
@[fun_prop]
lemma isHom_inr : IsHom (inr (A := A) (B := B)) := by
  unfold inr
  fun_prop

/--
@isnad1 id=ishom.2h5v.s6.46b430f359ac from=translated src=- shape=e794309d vocab=46043e4f
-/
@[fun_prop]
lemma isHom_elim {f : A → C} (hf : IsHom f) {g : B → C} (hg : IsHom g) : IsHom (elim f g) := by
  apply Sigma.isHom_elim fun b ↦ ?_
  cases b <;>
  · simp only [elim]
    fun_prop

end Encoding

/-- Encodes an `A ⊕ B` as a `Sigma (Encoding A B)`. -/
def encode : A ⊕ B → Sigma (Encoding A B) :=
  Sum.elim Encoding.inl Encoding.inr

instance : QuasiBorelSpace (A ⊕ B) := lift encode

/--
@isnad1 id=ishom.0h2v.s5.37f9554f5a61 from=translated src=- shape=c45b51db vocab=0abc238b
-/
@[fun_prop]
lemma isHom_encode : IsHom (encode (A := A) (B := B)) := by
  apply isHom_of_lift

/--
@isnad1 id=ishom.0h2v.s4.fb1d23a7d01b from=translated src=- shape=da07f0c5 vocab=b1f3933b
-/
@[simp]
lemma isHom_inl : IsHom (Sum.inl : A → A ⊕ B) := by
  simp only [isHom_to_lift, encode, Sum.elim_inl]
  fun_prop

/--
@isnad1 id=ishom.1h4v.s5.dd967babd9e7 from=translated src=- shape=5035a985 vocab=b1f3933b
-/
@[fun_prop]
lemma isHom_inl' {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ Sum.inl (f x) : A → B ⊕ C) :=
  isHom_comp isHom_inl hf

/--
@isnad1 id=ishom.0h2v.s4.94a3c99708ba from=translated src=- shape=7ef2ecc6 vocab=3717617a
-/
@[simp]
lemma isHom_inr : IsHom (Sum.inr : B → A ⊕ B) := by
  simp only [isHom_to_lift, encode, Sum.elim_inr]
  fun_prop

/--
@isnad1 id=ishom.1h4v.s5.cb858769658f from=translated src=- shape=b3074f49 vocab=3717617a
-/
@[fun_prop]
lemma isHom_inr' {f : A → C} (hf : IsHom f) : IsHom (fun x ↦ Sum.inr (f x) : A → B ⊕ C) :=
  isHom_comp isHom_inr hf

/--
@isnad1 id=ishom.2h5v.s5.6304b2f952ea from=translated src=- shape=afa1c0bf vocab=95c4cbb9
-/
@[local fun_prop]
lemma isHom_elim
    {f : A → C} (hf : IsHom f)
    {g : B → C} (hg : IsHom g)
    : IsHom (Sum.elim f g) := by
  have : Sum.elim f g = fun x ↦ Encoding.elim f g (encode x) := by
    ext x
    cases x <;> rfl
  rw [this]
  fun_prop

/--
@isnad1 id=ishom.3h7v.s6.9bad3324cb34 from=translated src=- shape=63158b40 vocab=42b86354
-/
@[fun_prop]
lemma isHom_elim'
    {f : A → B → D} (hf : IsHom (fun x : A × B ↦ f x.1 x.2))
    {g : A → C → D} (hg : IsHom (fun x : A × C ↦ g x.1 x.2))
    {h : A → B ⊕ C} (hh : IsHom h)
    : IsHom (fun x ↦ Sum.elim (f x) (g x) (h x)) := by
  have {x}
      : Sum.elim (f x) (g x) (h x)
      = Sum.elim (γ := A →𝒒 D) (fun x ↦ .mk (f · x)) (fun x ↦ .mk (g · x)) (h x) x := by
    cases h x <;> rfl
  simp only [this]
  fun_prop

/--
@isnad1 id=ishom.3h8v.s7.1d44500447bb from=translated src=- shape=f57274e6 vocab=b581b487
-/
@[fun_prop]
lemma isHom_map
    {f : A → B → D} (hf : IsHom fun x : A × B ↦ f x.1 x.2)
    {g : A → C → E} (hg : IsHom fun x : A × C ↦ g x.1 x.2)
    {h : A → B ⊕ C} (hh : IsHom h)
    : IsHom (fun x ↦ Sum.map (f x) (g x) (h x)) := by
  change IsHom fun x ↦ Sum.elim (Sum.inl ∘ f x) (Sum.inr ∘ g x) (h x)
  fun_prop

/--
@isnad1 id=ishom.0h2v.s4.96fb0b94afd1 from=translated src=- shape=e7dbeadb vocab=bd2b3617
-/
@[fun_prop, simp]
lemma isHom_isLeft : IsHom (Sum.isLeft : A ⊕ B → Bool) := by
  have : (Sum.isLeft : A ⊕ B → Bool) = Sum.elim (fun _ ↦ true) (fun _ ↦ false) := by
    ext x
    cases x <;> rfl
  rw [this]
  fun_prop

end QuasiBorelSpace.Sum

namespace OmegaQuasiBorelSpace.Sum

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {A B C : Type*}

/--
@isnad1 id=ishom.2h5v.s6.78226e4cd32e from=translated src=- shape=ca4a687a vocab=5494b645
-/
@[fun_prop]
lemma isHom_projl
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    [QuasiBorelSpace C]
    {f : C → Chain (A ⊕ B)} (hf : IsHom f)
    {g : C → A} (hg : IsHom g)
    : IsHom (fun x ↦ Chain.Sum.projl (hA := ⟨g x⟩) (f x)) := by
  simp only [Chain.isHom_iff, Chain.Sum.projl_coe]
  intro i
  exact Sum.isHom_elim' (by fun_prop) (by fun_prop) (isHom_comp' (Chain.isHom_apply i) hf)

/--
@isnad1 id=ishom.2h5v.s6.7d122de3f68f from=translated src=- shape=dd1f79a2 vocab=96ac2a6d
-/
@[fun_prop]
lemma isHom_projr
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    [QuasiBorelSpace C]
    {f : C → Chain (A ⊕ B)} (hf : IsHom f)
    {g : C → B} (hb : IsHom g)
    : IsHom (fun x ↦ Chain.Sum.projr (hB := ⟨g x⟩) (f x)) := by
  simp only [Chain.isHom_iff, Chain.Sum.projr_coe]
  intro i
  exact Sum.isHom_elim' (by fun_prop) (by fun_prop) (isHom_comp' (Chain.isHom_apply i) hf)

/--
@isnad1 id=ishom.0h2v.s6.0eeb3eb56c57 from=translated src=- shape=739a05f1 vocab=cbf34485
-/
@[fun_prop, simp]
lemma isHom_distrib
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    : IsHom (Chain.Sum.distrib (A := A) (B := B)) := by
  simp (unfoldPartialApp := true) only [Chain.Sum.distrib]
  fun_prop

/-- Coproduct of omega quasi-borel spaces is again an omega quasi-borel space. -/
noncomputable instance
    [OmegaQuasiBorelSpace A] [OmegaQuasiBorelSpace B] :
    OmegaQuasiBorelSpace (A ⊕ B) where
  isHom_ωSup := by
    simp only [ωSup]
    fun_prop

end OmegaQuasiBorelSpace.Sum
