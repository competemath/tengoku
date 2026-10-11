/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Tengoku

/-!
# Positive difference

This file defines the positive difference of set families and sets in an ordered additive group.

## Main declarations

* `Finset.posDiffs`: Positive difference of set families.
* `Finset.posSub`: Positive difference of sets in an ordered additive group.

## Notations

We declare the following notation in the `finset_family` locale:
* `s \₊ t` for `finset.posDiffs s t`
* `s -₊ t` for `finset.posSub s t`

## References

* [Bollobás, Leader, Radcliffe, *Reverse Kleitman Inequalities][bollobasleaderradcliffe1989]
-/

public section

open scoped Pointwise

variable {α : Type*}

namespace Finset

/-! ### Positive set difference -/

section posDiffs
section GeneralizedBooleanAlgebra
variable [GeneralizedBooleanAlgebra α] [DecidableRel (α := α) (· ≤ ·)] [DecidableEq α]
  {s t : Finset α} {a : α}

/-- The positive set difference of finsets `s` and `t` is the set of `a \ b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posDiffs (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun (a, b) ↦ b ≤ a).image fun (a, b) ↦ a \ b

scoped[FinsetFamily] infixl:70 " \\₊ " => Finset.posDiffs

open scoped FinsetFamily

@[simp] lemma mem_posDiffs : a ∈ s \₊ t ↔ ∃ b ∈ s, ∃ c ∈ t, c ≤ b ∧ b \ c = a := by
  simp_rw [posDiffs, mem_image, mem_filter, mem_product, Prod.exists, and_assoc, exists_and_left]

@[simp] lemma posDiffs_empty (s : Finset α) : s \₊ ∅ = ∅ := by simp [posDiffs]
@[simp] lemma empty_posDiffs (s : Finset α) : ∅ \₊ s = ∅ := by simp [posDiffs]

lemma posDiffs_subset_diffs : s \₊ t ⊆ s \\ t := by
  simp only [subset_iff, mem_posDiffs, mem_diffs]
  exact fun a ⟨b, hb, c, hc, _, ha⟩ ↦ ⟨b, hb, c, hc, ha⟩

end GeneralizedBooleanAlgebra

open scoped FinsetFamily

section Finset

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}

end Finset
end posDiffs

/-! ### Positive subtraction -/

section posSub
variable [Sub α] [Preorder α] [DecidableRel (α := α) (· ≤ ·)] [DecidableEq α] {s t : Finset α}
  {a : α}

/-- The positive subtraction of finsets `s` and `t` is the set of `a - b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posSub (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun (a, b) ↦ b ≤ a).image fun (a, b) ↦ a - b

scoped[FinsetFamily] infixl:70 " -₊ " => Finset.posSub

open scoped FinsetFamily

end posSub
end Finset
