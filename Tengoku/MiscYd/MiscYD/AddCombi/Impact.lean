/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Tengoku

/-!
# Impact function
-/

public section

open Function
open scoped Pointwise

namespace Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

section Mul
variable [Mul α] {n : ℕ}

/-- The multiplicative impact function of a finset. -/
@[to_additive]
noncomputable def mulImpact (s : Finset α) (n : ℕ) : ℕ :=
  ⨅ t : {t : Finset α // #t = n}, (s * t).card

@[to_additive (attr := simp)]
lemma mulImpact_empty (n : ℕ) : (∅ : Finset α).mulImpact n = 0 := by simp [mulImpact]

end Mul

section Group
variable [Group α] {n : ℕ}

@[to_additive (attr := simp)]
lemma mulImpact_singleton [Infinite α] (a : α) (n : ℕ) : ({a} : Finset α).mulImpact n = n := by
  simp only [mulImpact, singleton_mul, card_smul_finset]
  have : Nonempty {t : Finset α // #t = n} := nonempty_subtype.2 (exists_card_eq _)
  exact Eq.trans (iInf_congr Subtype.prop) ciInf_const

variable [Fintype α]

end Group

section CommGroup
variable [CommGroup α] [CommGroup β] {n : ℕ}

end CommGroup
end Finset
