/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku

/-!
# Chain utilities for coproducts of ωCPOs

This file provides utilities for working with chains in sum types,
which are used to construct the ωCPO instance for coproducts.
-/

@[expose] public section

namespace OmegaCompletePartialOrder.Chain.Sum

variable {A B : Type*}
variable [Preorder A] [Preorder B]

/-- Left injection for chains of sums. -/
def inl (c : Chain A) : Chain (A ⊕ B) := c.map ⟨.inl, Sum.inl_mono⟩

/--
@isnad1 id=eq.0h4v.s6.891ede97b44b from=translated src=- shape=b5caaf8c vocab=b36dd49c
-/
@[simp]
lemma inl_coe (c : Chain A) (n : ℕ) : inl (B := B) c n = .inl (c n) := by rfl

/-- Right injection for chains of sums. -/
def inr (c : Chain B) : Chain (A ⊕ B) := c.map ⟨.inr, Sum.inr_mono⟩

/--
@isnad1 id=eq.0h4v.s6.94c6c29e1697 from=translated src=- shape=99980df0 vocab=272a599c
-/
@[simp]
lemma inr_coe (c : Chain B) (n : ℕ) : inr (A := A) c n = .inr (c n) := by rfl

/-- Projects left values out of a chain. -/
def projl [hA : Inhabited A] (c : Chain (A ⊕ B)) : Chain A where
  toFun n := Sum.elim id (fun _ ↦ default) (c n)
  monotone' := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    have hc := (OrderHomClass.mono c) (Nat.le_add_right n 1)
    cases hn : c n with
    | inl x =>
      cases hn₁ : c (n + 1) with
      | inl y =>
        simp_all
      | inr y => simp only [hn, hn₁, Sum.not_inl_le_inr] at hc
    | inr x =>
      cases hn₁ : c (n + 1) with
      | inl y => simp only [hn, hn₁, Sum.not_inr_le_inl] at hc
      | inr y => simp only [Sum.elim_inr, le_refl]

/--
@isnad1 id=eq.0h4v.s6.908c26058f07 from=translated src=- shape=e03ca6f7 vocab=8b3ee588
-/
@[simp]
lemma projl_coe [Inhabited A] (c : Chain (A ⊕ B)) (n : ℕ) :
    projl c n = Sum.elim id (fun _ ↦ default) (c n) := by
  rfl

/-- Swaps the two sides of an ordered sum. -/
def swapOrderHom : A ⊕ B →o B ⊕ A where
  toFun := Sum.swap
  monotone' := by
    intro x y h
    simp_all

/--
@isnad1 id=eq.0h3v.s6.679aa9ff605f from=translated src=- shape=39cdfaa9 vocab=399eb8c4
-/
@[simp]
lemma swapOrderHom_apply (x : A ⊕ B) : swapOrderHom x = Sum.swap x := rfl

/-- Projects right values out of a chain. -/
def projr [hB : Inhabited B] (c : Chain (A ⊕ B)) : Chain B :=
  projl (c.map swapOrderHom)

/--
@isnad1 id=eq.0h4v.s6.1ee9f9e7b947 from=translated src=- shape=859ffd57 vocab=38594a7c
-/
@[simp]
lemma projr_coe [Inhabited B] (c : Chain (A ⊕ B)) (n : ℕ) :
    projr c n = Sum.elim (fun _ ↦ default) id (c n) := by
  cases h : c n with
  | inl _ =>
    simp only [projr, projl_coe, coe_map, Function.comp_apply, h, swapOrderHom_apply,
      Sum.swap_inl, Sum.elim_inr, Sum.elim_inl]
  | inr _ =>
    simp only [projr, projl_coe, coe_map, Function.comp_apply, h, swapOrderHom_apply,
      Sum.swap_inr, Sum.elim_inl, id_eq, Sum.elim_inr]

/-- Splits a chain of sums into a sum of chains. -/
def distrib (c : Chain (A ⊕ B)) : Chain A ⊕ Chain B :=
  Sum.elim
    (fun d ↦
      let : Inhabited A := ⟨d⟩
      .inl (projl c))
    (fun d ↦
      let : Inhabited B := ⟨d⟩
      .inr (projr c))
    (c 0)

/--
@isnad1 id=eq.0h3v.s5.f3f7e82af3bb from=translated src=- shape=ca09fa6a vocab=c55dd6c9
-/
@[simp]
lemma distrib_inl (c : Chain A) : distrib (inl (B := B) c) = .inl c := by rfl

/--
@isnad1 id=eq.0h3v.s5.f18b213737e5 from=translated src=- shape=a5269c7e vocab=4482a006
-/
@[simp]
lemma distrib_inr (c : Chain B) : distrib (inr (A := A) c) = .inr c := by rfl

/--
@isnad1 id=var.0h6v.s5.c4d6f4df7a6d from=translated src=- shape=a0441166 vocab=4d5c0b22
-/
@[elab_as_elim]
lemma distrib_cases
    {p : Chain (A ⊕ B) → Prop}
    (inl : ∀ c, p (inl c))
    (inr : ∀ c, p (inr c))
    (c : Chain (A ⊕ B)) : p c := by
  suffices this : c = Sum.elim Sum.inl Sum.inr (distrib c) by
    rw [this]
    cases distrib c with
    | inl _ => apply inl
    | inr _ => apply inr
  apply Chain.ext
  funext n
  dsimp only [distrib]
  have := (OrderHomClass.mono c) (Nat.zero_le n)
  cases h₀ : c 0 with
  | inl x =>
    cases hₙ : c n with
    | inl y =>
      simp_all
    | inr y => simp only [h₀, hₙ, Sum.not_inl_le_inr] at this
  | inr x =>
    cases hₙ : c n with
    | inl y => simp only [h₀, hₙ, Sum.not_inr_le_inl] at this
    | inr y =>
      simp_all

end OmegaCompletePartialOrder.Chain.Sum
