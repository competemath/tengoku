/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Tengoku

/-!
General lemmas not specific to analysis of Boolean functions.
-/

@[expose] public section

namespace LeanPool.LeanBooleanfun.BooleanFun

open Finset Pi

variable {α : Type*}

variable {ι : Type*} [Fintype ι]

-- not to be confused with `Finset.sum_singleton`
/--
@isnad1 id=eq.1h4v.s6.40a948605cfb from=translated src=- shape=d90711fe vocab=ef200204
-/
lemma sum_singletons [AddCommMonoid α] {F : Finset ι → α} {G : ι → α} (h : ∀ i, F {i} = G i) :
    ∑ S ∈ {S | S.card = 1}, F S = ∑ i, G i := by
  symm
  apply sum_of_injOn (e := fun i ↦ {i})
  · intro j _ l _ h'
    simp only at h'
    exact Finset.singleton_inj.mp h'
  · intro j _
    simp
  · intro S hS hS'
    simp only [mem_filter, mem_univ, true_and] at hS
    obtain ⟨i, hi⟩ := card_eq_one.mp hS
    simp only [coe_univ, Set.image_univ, Set.mem_range, not_exists] at hS'
    exact absurd hi.symm (hS' i)
  · intro i _
    symm
    exact h i

/--
@isnad1 id=eq.0h3v.s6.51da698a7f57 from=translated src=- shape=d6cc36a3 vocab=ef200204
-/
lemma sum_singletons' [AddCommMonoid α] {F : Finset ι → α} :
    ∑ S ∈ {S | S.card = 1}, F S = ∑ i, F {i} := by apply sum_singletons; intro i; rfl

variable {P : Prop} [Decidable P] {a b c : α}

/--
@isnad1 id=eq.0h5v.s5.1c6bddf9cf2e from=translated src=- shape=50466c12 vocab=af84458f
-/
lemma ite_ite_same (a b c : α) :
    ite P (ite P a b) c = ite P a c := by split_ifs <;> rfl

/--
@isnad1 id=eq.1h5v.s5.951a8602acef from=translated src=- shape=130ea64a vocab=af84458f
-/
lemma rw_ite_left (h : P → a = c) :
    ite P a b = ite P c b := by
  split_ifs with hp
  · rw [h hp]
  · rfl

/--
@isnad1 id=eq.1h5v.s5.8f72ddb23cf0 from=translated src=- shape=ba6830ff vocab=af84458f
-/
lemma rw_ite_right (h : ¬P → a = c) :
    ite P b a = ite P b c := by
  split_ifs with hp
  · rfl
  · rw [h hp]

/--
@isnad1 id=eq.0h6v.s6.eb03f41be9c6 from=translated src=- shape=10fa9080 vocab=a8b81a11
-/
lemma ite_add_ite {α : Type*} [AddCommMonoid α] (a₁ b₁ a₂ b₂ : α) :
    ite P a₁ b₁ + ite P a₂ b₂ = ite P (a₁ + a₂) (b₁ + b₂) := by split_ifs <;> simp

/--
@isnad1 id=eq.0h5v.s5.712e41136249 from=translated src=- shape=9be1f5b0 vocab=af84458f
-/
lemma ite_ite_not (P : Prop) [Decidable P] (a b c : α) :
    ite P (ite (¬P) a b) c = ite P b c := by split_ifs <;> rfl

/--
@isnad1 id=eq.0h5v.s5.01c061dfd243 from=translated src=- shape=87327761 vocab=af84458f
-/
lemma ite_ite_not' (P : Prop) [Decidable P] (a b c : α) :
    ite (¬P) (ite P a b) c = ite (¬P) b c := by split_ifs <;> rfl

variable {p q : Prop}

/-- Real-valued `0-1` indicator testing a proposition. We prefer this over using `Set.indicator`
and we don't call it indicator to avoid overloading the Mathlib definition. -/
noncomputable abbrev oneOn (p : Prop) : ℝ := ite (h := Classical.propDecidable p) p 1 0

/--
@isnad1 id=eq.0h2v.s3.207b1667ec97 from=translated src=- shape=709c8ac0 vocab=3253b940
-/
lemma oneOn_true (h : p) : oneOn p = 1 := by simpa

/--
@isnad1 id=eq.1h1v.s3.6458d48363a1 from=translated src=- shape=5df7011e vocab=3253b940
-/
lemma oneOn_false (h : ¬p) : oneOn p = 0 := by simpa

/--
@isnad1 id=eq.0h2v.s4.f7a3384aceb3 from=translated src=- shape=d72babe5 vocab=25e0f07d
-/
lemma oneOn_and : oneOn (p ∧ q) = (oneOn p) * (oneOn q) := by
  unfold oneOn
  split_ifs <;> simp_all

/--
@isnad1 id=eq.0h1v.s4.e62679e5930b from=translated src=- shape=dc1424fd vocab=43dc7bff
-/
lemma oneOn_not : oneOn (¬p) = 1 - oneOn p := by
  unfold oneOn; split_ifs <;> simp

/--
@isnad1 id=eq.0h2v.s4.f1d617150eda from=translated src=- shape=c7fe450e vocab=f227b7de
-/
lemma oneOn_prod {p : ι → Prop} : ∏ i, oneOn (p i) = oneOn (∀ i, p i) := by
  classical
  unfold oneOn
  split_ifs with h
  · simp [h]
  · rw [not_forall] at h
    obtain ⟨i, hi⟩ := h
    rw [← Finset.prod_erase_mul (a := i) (s := Finset.univ) (h := Finset.mem_univ i)]
    simp [hi]

/-- Solutions of the equation `ρᵏ = ρ` in real numbers.
@isnad1 id=or.1h2v.s5.4dcc7978b886 from=translated src=- shape=a30c25cc vocab=873040dc
-/
lemma pow_eq_self_imp {ρ : ℝ} {k : ℕ} :
    ρ ^ k = ρ → (k = 1 ∨ ρ = 0 ∨ ρ = 1 ∨ ρ = -1) := by
  intro h
  cases k with
  | zero => right; right; left; symm; rwa [pow_zero] at h
  | succ k =>
    by_cases hρ : ρ = 0
    · right; left; assumption
    · rw [pow_succ] at h
      nth_rewrite 3 [← one_mul ρ] at h
      have h := mul_right_cancel₀ hρ h
      obtain h'|h'|⟨h', _⟩ := pow_eq_one_iff_cases.mp h
      · left; omega
      · right; right; left; assumption
      · right; right; right; assumption

end LeanPool.LeanBooleanfun.BooleanFun
