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

/--
@isnad1 id=eq.0h0v.s4.fd6e8a4f4874 from=translated src=- shape=573f7cb9 vocab=778de7b9
-/
@[simp]
theorem dimension_zero_fin_three : dimension 0 (Fin 3) = 0 := by
  simp only [dimension, Nat.mul_zero, Fintype.card_fin, zero_add, Nat.sub_self]

/-- Relabelling does not change the complex dimension.
@isnad1 id=eq.0h4v.s4.40b6e3cc2573 from=translated src=- shape=f836fd79 vocab=e10edbdc
-/
theorem dimension_equiv {g : ℕ} {S T : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) : dimension g S = dimension g T := by
  simp only [dimension]
  rw [Fintype.card_congr e]

/-- Forgetting one marking lowers the dimension by one.
@isnad1 id=eq.1h2v.s5.6949e39679de from=translated src=- shape=a95ecfb0 vocab=3468e1f9
-/
theorem dimension_option {g : ℕ} {S : Type*} [Fintype S]
    (h : StableArity g S) :
    dimension g (Option S) = dimension g S + 1 := by
  simp only [dimension, Fintype.card_option, StableArity] at h ⊢
  omega

/-- A nonseparating boundary has codimension one.
@isnad1 id=eq.1h2v.s6.ab5d5677f710 from=translated src=- shape=2da5a59a vocab=3468e1f9
-/
theorem dimension_nonseparating {g : ℕ} {S : Type*} [Fintype S]
    (h : StableArity (g + 1) S) :
    dimension g (Option (Option S)) + 1 = dimension (g + 1) S := by
  simp only [dimension, Fintype.card_option, StableArity] at h ⊢
  omega

/-- A separating boundary has codimension one.
@isnad1 id=eq.2h4v.s6.b82ae0e414d0 from=translated src=- shape=6e9d39f8 vocab=30f49b81
-/
theorem dimension_separating {g₁ g₂ : ℕ} {S T : Type*}
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T)) :
    dimension g₁ (Option S) + dimension g₂ (Option T) + 1 =
      dimension (g₁ + g₂) (S ⊕ T) := by
  simp only [dimension, Fintype.card_option, Fintype.card_sum, StableArity] at h₁ h₂ ⊢
  omega

/-- Stability is invariant under an equivalence of finite label types.
@isnad1 id=iff.0h4v.s4.3009fc7139d4 from=translated src=- shape=1f280f71 vocab=ebb47229
-/
theorem equiv {g : ℕ} {S T : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) : StableArity g S ↔ StableArity g T := by
  simp only [StableArity]
  rw [Fintype.card_congr e]

/-- Three genus-zero markings form a stable arity.
@isnad1 id=stablear.0h0v.s4.21383c1f68c9 from=translated src=- shape=648e8daf vocab=e101b635
-/
theorem zero_fin_three : StableArity 0 (Fin 3) := by
  simp only [StableArity, Nat.mul_zero, Fintype.card_fin, zero_add, Std.le_refl]

/-- Adding a marking preserves stability.
@isnad1 id=stablear.1h2v.s4.f92d69d9738d from=translated src=- shape=7aa5589c vocab=59682966
-/
theorem option {g : ℕ} {S : Type*} [Fintype S] (h : StableArity g S) :
    StableArity g (Option S) := by
  simp only [StableArity, Fintype.card_option] at h ⊢
  omega

/-- The two arities appearing in nonseparating gluing have the same stability
condition.
@isnad1 id=iff.0h2v.s5.9aa3022b4d7a from=translated src=- shape=8ea55606 vocab=0a1085ff
-/
theorem sum_fin_two_iff {g : ℕ} {S : Type*} [Fintype S] :
    StableArity g (S ⊕ Fin 2) ↔ StableArity (g + 1) S := by
  simp only [StableArity, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Two nested optional markings give the same stability condition as adding a
handle and retaining the original labels.
@isnad1 id=iff.0h2v.s5.e4655c4bfa07 from=translated src=- shape=b23374b2 vocab=bfed2dbe
-/
theorem double_option_iff {g : ℕ} {S : Type*} [Fintype S] :
    StableArity g (Option (Option S)) ↔ StableArity (g + 1) S := by
  simp only [StableArity, Fintype.card_option]
  omega

/-- Stable component arities give a stable arity after separating gluing.
@isnad1 id=stablear.2h4v.s5.52614866fab2 from=translated src=- shape=b21dde60 vocab=6d6f457d
-/
theorem separating {g₁ g₂ : ℕ} {S T : Type*} [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T)) :
    StableArity (g₁ + g₂) (S ⊕ T) := by
  simp only [StableArity, Fintype.card_option, Fintype.card_sum] at h₁ h₂ ⊢
  omega

/-- Genus zero with two inputs becomes stable after adjoining the unit
marking used in the metric normalization axiom.
@isnad1 id=stablear.0h0v.s4.2598d8920f3d from=translated src=- shape=15faa485 vocab=f930ce17
-/
theorem zero_option_fin_two : StableArity 0 (Option (Fin 2)) := by
  simp only [StableArity, Nat.mul_zero, Fintype.card_option, Fintype.card_fin,
    Nat.reduceAdd, zero_add, Std.le_refl]

end StableArity

end AxiomaticGW
