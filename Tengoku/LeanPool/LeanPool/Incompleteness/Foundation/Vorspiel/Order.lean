/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku

/-! # Order -/

@[expose] public section

section «lp_section_1»

variable {α : Sort u} (r : α → α → Prop)

local infix:50 " ≺ " => r

/-- Imported declaration from the Incompleteness formalization. -/
def IsInfiniteDescendingChain (c : ℕ → α) : Prop := ∀ i, c (i + 1) ≺ c i

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def descendingChain (z : α) : ℕ → α
  | 0       => z
  | (i + 1) => @Classical.epsilon α ⟨z⟩ (fun y => y ≺ descendingChain z i ∧ ¬Acc r y)

/--
@isnad1 id=iff.0h3v.s4.fc0ef6d79582 from=translated src=- shape=08cd5b50 vocab=0d1d1ec1
-/
lemma not_acc_iff {x : α} : ¬Acc r x ↔ ∃ y, y ≺ x ∧ ¬Acc r y :=
  ⟨by
    intro hx
    by_contra h
    exact hx <| Acc.intro x (fun y hy => by
      simp_all),
  by
    rintro ⟨y, hy, hy'⟩ hx
    exact hy' (Acc.inv hx hy)⟩

/--
@isnad1 id=eq.0h3v.s4.e5d05bc798fd from=translated src=- shape=98054f23 vocab=ca64955d
-/
@[simp] lemma descending_chain_zero (z : α) : descendingChain r z 0 = z := rfl

/--
@isnad1 id=isinfini.1h3v.s4.f4cd27149483 from=translated src=- shape=52dd7537 vocab=bfc8e3b2
-/
lemma isInfiniteDescendingChain_of_non_acc (z : α) (hz : ¬Acc r z) :
    IsInfiniteDescendingChain r (descendingChain r z) := by
  have : ∀ i, (i ≠ 0 → descendingChain r z i ≺ descendingChain r z i.pred) ∧
          ¬Acc r (descendingChain r z i) := by
    intro i
    induction i with
    | zero =>
        exact ⟨by intro h; exact False.elim (h rfl), hz⟩
    | succ i ih =>
      have : ∃ y, y ≺ (descendingChain r z i) ∧ ¬Acc r y := (not_acc_iff r).mp ih.2
      have hs := Classical.epsilon_spec this
      exact ⟨fun _ => hs.1, hs.2⟩
  intro i; simpa using (this (i + 1)).1

end «lp_section_1»

section «lp_section_2»

variable {α : Type*} [HeytingAlgebra α]

/--
@isnad1 id=le.0h4v.s6.c5d78eef1af8 from=translated src=- shape=1792c53d vocab=49ef2aab
-/
lemma himp_himp_inf_himp_inf_le (a b c : α) : (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := calc
  (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a = (a ⇨ b ⇨ c) ⊓ b ⊓ a := by simp only [inf_assoc, himp_inf_self]
  _                         = (a ⇨ b ⇨ c) ⊓ a ⊓ b := by simp only [inf_assoc, inf_comm a b]
  _                         ≤ (b ⇨ c) ⊓ b         := by
    simp only [himp_inf_self a (b ⇨ c), le_inf_iff]
    constructor
    · simp only [inf_assoc, inf_le_left]
    · exact inf_le_right
  _                         ≤ c                   := by simp

/--
@isnad1 id=le.0h4v.s6.807eff0c611c from=translated src=- shape=63752a0d vocab=58f85b1e
-/
lemma himp_inf_himp_inf_sup_le (a b c : α) : (a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c := by
  have ha : a ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have hb : b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, inf_comm (a ⇨ c) (b ⇨ c), ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have : a ⊔ b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := sup_le_iff.mpr ⟨ha, hb⟩
  simpa only [GeneralizedHeytingAlgebra.le_himp_iff, inf_comm (a ⊔ b)] using this

end «lp_section_2»
