/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.Data.Fintype.Option
public import Tengoku.Seed.Data.Fintype.Sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stable genera and finite label types

The stability condition `2g - 2 + |S| > 0` is represented without natural
number subtraction as `3 ≤ 2g + |S|`.
-/

@[expose] public section

namespace AxiomaticGW

/-- The usual stability condition for a genus and a finite set of markings,
written in a subtraction-free form suitable for natural numbers.-/
def StableArity (g : ℕ) (S : Type*) [Fintype S] : Prop :=
  3 ≤ 2 * g + Fintype.card S

namespace StableArity

/-- Complex dimension of the stable-curve moduli space in a stable arity.-/
def dimension (g : ℕ) (S : Type*) [Fintype S] : ℕ :=
  3 * g + Fintype.card S - 3

@[simp]
theorem dimension_zero_fin_three : dimension 0 (Fin 3) = 0 := by
  simp only [dimension, Nat.mul_zero, Fintype.card_fin, zero_add, Nat.sub_self]

/-- Relabelling does not change the complex dimension.-/
theorem dimension_equiv {g : ℕ} {S T : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) : dimension g S = dimension g T := by
  simp only [dimension]
  rw [Fintype.card_congr e]

/-- Forgetting one marking lowers the dimension by one.-/
theorem dimension_option {g : ℕ} {S : Type*} [Fintype S]
    (h : StableArity g S) :
    dimension g (Option S) = dimension g S + 1 := by
  simp only [dimension, Fintype.card_option, StableArity] at h ⊢
  omega

/-- A nonseparating boundary has codimension one.-/
theorem dimension_nonseparating {g : ℕ} {S : Type*} [Fintype S]
    (h : StableArity (g + 1) S) :
    dimension g (Option (Option S)) + 1 = dimension (g + 1) S := by
  simp only [dimension, Fintype.card_option, StableArity] at h ⊢
  omega

/-- A separating boundary has codimension one.-/
theorem dimension_separating {g₁ g₂ : ℕ} {S T : Type*}
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T)) :
    dimension g₁ (Option S) + dimension g₂ (Option T) + 1 =
      dimension (g₁ + g₂) (S ⊕ T) := by
  simp only [dimension, Fintype.card_option, Fintype.card_sum, StableArity] at h₁ h₂ ⊢
  omega

/-- Stability is invariant under an equivalence of finite label types.-/
theorem equiv {g : ℕ} {S T : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) : StableArity g S ↔ StableArity g T := by
  simp only [StableArity]
  rw [Fintype.card_congr e]

/-- Three genus-zero markings form a stable arity.-/
theorem zero_fin_three : StableArity 0 (Fin 3) := by
  simp only [StableArity, Nat.mul_zero, Fintype.card_fin, zero_add, Std.le_refl]

/-- Adding a marking preserves stability.-/
theorem option {g : ℕ} {S : Type*} [Fintype S] (h : StableArity g S) :
    StableArity g (Option S) := by
  simp only [StableArity, Fintype.card_option] at h ⊢
  omega

/-- The two arities appearing in nonseparating gluing have the same stability
condition.-/
theorem sum_fin_two_iff {g : ℕ} {S : Type*} [Fintype S] :
    StableArity g (S ⊕ Fin 2) ↔ StableArity (g + 1) S := by
  simp only [StableArity, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Two nested optional markings give the same stability condition as adding a
handle and retaining the original labels.-/
theorem double_option_iff {g : ℕ} {S : Type*} [Fintype S] :
    StableArity g (Option (Option S)) ↔ StableArity (g + 1) S := by
  simp only [StableArity, Fintype.card_option]
  omega

/-- Stable component arities give a stable arity after separating gluing.-/
theorem separating {g₁ g₂ : ℕ} {S T : Type*} [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T)) :
    StableArity (g₁ + g₂) (S ⊕ T) := by
  simp only [StableArity, Fintype.card_option, Fintype.card_sum] at h₁ h₂ ⊢
  omega

/-- Genus zero with two inputs becomes stable after adjoining the unit
marking used in the metric normalization axiom.-/
theorem zero_option_fin_two : StableArity 0 (Option (Fin 2)) := by
  simp only [StableArity, Nat.mul_zero, Fintype.card_option, Fintype.card_fin,
    Nat.reduceAdd, zero_add, Std.le_refl]

end StableArity

end AxiomaticGW
