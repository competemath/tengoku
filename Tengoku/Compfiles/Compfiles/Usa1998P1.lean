/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1998, Problem 1

Suppose that the set { 1, 2, ..., 1998 } has been partitioned into disjoint
pairs {aᵢ, bᵢ}, where 1 ≤ i ≤ 999, so that for all i, |aᵢ - bᵢ| = 1 or 6.

Prove that the sum

  |a₁ - b₁| + |a₂ - b₂| + ... + |a₉₉₉ - b₉₉₉|

ends in the digit 9.
-/

namespace Usa1998P1

/--
@isnad1 id=iff.0h3v.s4.4ffe3b0d6cf1 from=translated src=- shape=30ae837b vocab=8de64140
-/
lemma zmod_eq (a b c : ℤ) : a ≡ b [ZMOD c] ↔ a % c = b % c := by rfl

/--
@isnad1 id=eq.0h1v.s5.34ab52b3f93d from=translated src=- shape=9403d667 vocab=40c6ea2c
-/
lemma mod2_abs (a : ℤ) : |a| % 2 = a % 2 := by
  obtain h | h := abs_cases a <;> rw [h.1]
  rw [Int.neg_emod_two]

-- For integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
/--
@isnad1 id=eq.0h2v.s5.4030b48b1156 from=translated src=- shape=2d901004 vocab=da599321
-/
lemma mod2_diff (a b : ℤ) : |a - b| % 2 = (a + b) % 2 := by
  rw [mod2_abs, Int.sub_eq_add_neg, Int.add_emod, Int.neg_emod_two, ← Int.add_emod]

/--
@isnad1 id=eq.0h1v.s6.4b3fa3e8ddb3 from=translated src=- shape=56e368ba vocab=373b85a3
-/
lemma lemma0 (n : ℕ) : (∑ x ∈ Finset.Icc 1 (4 * n + 2), (x:ℤ) % 2) % 2 = 1 := by
  norm_cast
  induction n with
  | zero => simp +arith +decide
  | succ n ih =>
    rw [show 4 * (n + 1) + 2 = (4 * n + 2) + 4 by lia]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    lia

end Usa1998P1
