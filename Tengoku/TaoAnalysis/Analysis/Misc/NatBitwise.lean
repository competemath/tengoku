import Tengoku

/-!
# Additional lemmas for natural number bit operations

This file contains general-purpose lemmas about {name}`Nat.testBit`, {name}`Nat.bitIndices`,
and sums of powers of 2 that are used throughout the formalization.

## Main results

* {given -show}`n : ℕ, i : ℕ` `Nat.testBit_iff_mem_bitIndices`: {lean}`n.testBit i = true ↔ i ∈ n.bitIndices`
* {given -show}`j` `Nat.testBit_finset_sum_pow_two`: For a finset {given}`s` of natural numbers,
  {lean}`(∑ i ∈ s, 2^i).testBit j ↔ j ∈ s`
* {given -show}`k` `Nat.testBit_sum_pow_two_fin`: Same for {lean}`Finset (Fin k)`

These lemmas connect the bit representation of natural numbers with finset membership,
which is fundamental for binary encoding arguments.
-/

namespace Nat

/-- {lean}`n.testBit i = true` if and only if {name}`i` appears in {lean}`n.bitIndices`.
    This connects the pointwise bit test with the list of set bit positions. -/
lemma testBit_iff_mem_bitIndices (n i : ℕ) :
    n.testBit i = true ↔ i ∈ n.bitIndices := by
  constructor
  · intro h
    induction n using Nat.binaryRec generalizing i with
    | zero => simp at h
    | bit b n ih =>
      cases b
      · simp only [Nat.bit_false, Nat.bitIndices_two_mul, List.mem_map]
        rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
        · simp at h
        · have hi_succ : i = (i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
          rw [hi_succ, Nat.testBit_bit_succ] at h
          exact ⟨i - 1, ih _ h, hi_succ.symm⟩
      · simp only [Nat.bit_true, Nat.bitIndices_two_mul_add_one, List.mem_cons, List.mem_map]
        rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
        · left; rfl
        · right
          have hi_succ : i = (i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
          rw [hi_succ, Nat.testBit_bit_succ] at h
          exact ⟨i - 1, ih _ h, hi_succ.symm⟩
  · intro h
    induction n using Nat.binaryRec generalizing i with
    | zero => simp at h
    | bit b n ih =>
      cases b
      · simp only [Nat.bit_false, Nat.bitIndices_two_mul, List.mem_map] at h
        obtain ⟨j, hj, rfl⟩ := h
        rw [Nat.testBit_bit_succ]
        exact ih _ hj
      · simp only [Nat.bit_true, Nat.bitIndices_two_mul_add_one, List.mem_cons, List.mem_map] at h
        rcases h with rfl | ⟨j, hj, rfl⟩
        · simp
        · rw [Nat.testBit_bit_succ]
          exact ih _ hj

end Nat
