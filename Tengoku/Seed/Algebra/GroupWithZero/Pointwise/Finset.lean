/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.Basic
public import Tengoku.Seed.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise operations of finsets in a group with zero

This file proves properties of pointwise operations of finsets in a group with zero.
-/

public section

assert_not_exists MulAction Ring

open scoped Pointwise

namespace Finset
variable {α : Type*}

section Mul

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

/--
@isnad1 id=le.2h4v.s6.48945571f987 from=seed src=0 shape=1b70347d vocab=d6413ddb
-/
lemma card_le_card_mul_left₀ [IsLeftCancelMulZero α] (has : a ∈ s) (ha : a ≠ 0) : #t ≤ #(s * t) :=
  card_le_card_mul_left_of_injective has (mul_right_injective₀ ha)

/--
@isnad1 id=le.2h4v.s6.1cc34db7eca2 from=seed src=0 shape=4728470d vocab=47df8631
-/
lemma card_le_card_mul_right₀ [IsRightCancelMulZero α] (hat : a ∈ t) (ha : a ≠ 0) : #s ≤ #(s * t) :=
  card_le_card_mul_right_of_injective hat (mul_left_injective₀ ha)

/--
@isnad1 id=le.0h2v.s5.9f77173a253a from=seed src=0 shape=e06a7f16 vocab=cdfcae03
-/
lemma card_le_card_mul_self₀ [IsLeftCancelMulZero α] : #s ≤ #(s * s) := by
  obtain hs | hs := (s.erase 0).eq_empty_or_nonempty
  · rw [erase_eq_empty_iff] at hs
    obtain rfl | rfl := hs <;> simp
  obtain ⟨a, ha⟩ := hs
  simp only [mem_erase, ne_eq] at ha
  exact card_le_card_mul_left₀ ha.2 ha.1

end Mul

section MulZeroClass
variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

/-! Note that `Finset` is not a `MulZeroClass` because `0 * ∅ ≠ 0`. -/

/--
@isnad1 id=le.0h2v.s5.71c88219b5fe from=seed src=0 shape=3d370dd3 vocab=83764dee
-/
lemma mul_zero_subset (s : Finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]
/--
@isnad1 id=le.0h2v.s5.55a4e3a53a57 from=seed src=0 shape=bcc23141 vocab=83764dee
-/
lemma zero_mul_subset (s : Finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]

/--
@isnad1 id=eq.1h2v.s5.d8af1a10e0ad from=seed src=0 shape=277a0d73 vocab=b561fc50
-/
lemma Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using! hs

/--
@isnad1 id=eq.1h2v.s5.4f9e9b2ab45b from=seed src=0 shape=ed746ba9 vocab=b561fc50
-/
lemma Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using! hs

end MulZeroClass

section GroupWithZero
variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

/--
@isnad1 id=le.0h2v.s6.fdd2be7350f3 from=seed src=0 shape=3d370dd3 vocab=04c8e08a
-/
lemma div_zero_subset (s : Finset α) : s / 0 ⊆ 0 := by simp [subset_iff, mem_div]

/--
@isnad1 id=le.0h2v.s6.9bd6fabfb517 from=seed src=0 shape=bcc23141 vocab=04c8e08a
-/
lemma zero_div_subset (s : Finset α) : 0 / s ⊆ 0 := by simp [subset_iff, mem_div]

/--
@isnad1 id=eq.1h2v.s6.9aae35a2b161 from=seed src=0 shape=277a0d73 vocab=f615658f
-/
lemma Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using! hs

/--
@isnad1 id=eq.1h2v.s6.1dac83fe964f from=seed src=0 shape=ed746ba9 vocab=f615658f
-/
lemma Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using! hs

/--
@isnad1 id=eq.0h1v.s5.01d3349de74e from=seed src=0 shape=045c6270 vocab=10bab496
-/
@[simp] protected lemma inv_zero : (0 : Finset α)⁻¹ = 0 := by ext; simp

end GroupWithZero
end Finset
