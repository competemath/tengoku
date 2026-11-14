import Tengoku.Twinprime.TwinPrime.Analytic.DyadicIntervalCover
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicStaircase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Staircase corrections grouped by tree height

The recursive staircase detail is exactly the sum of the corrections at
the internal tree nodes. Grouping them by height provides the fixed levels
used in the maximal bilinear estimate. Triangle inequalities retain every
level and both factors of each rectangular correction.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The rectangular correction at one tree node. At a leaf its boundary
interval is empty, so the formula is zero without a separate convention.-/
def dyadicStaircaseCorrection (a b : ℕ → ℂ) (F : ℕ → ℕ) (p : ℕ × ℕ) : ℂ :=
  (∑ m ∈ Ico p.1 (p.1 + 2 ^ (p.2 - 1)), a m) *
    (∑ n ∈ Ico (F (p.1 + 2 ^ p.2 - 1)) (F (p.1 + 2 ^ (p.2 - 1) - 1)), b n)

/--
@isnad1 id=eq.0h4v.s5.620fdee2d061 from=translated src=- shape=22851aa9 vocab=55bc0999
-/
@[simp] theorem dyadicStaircaseCorrection_leaf (a b : ℕ → ℂ) (F : ℕ → ℕ) (M : ℕ) :
    dyadicStaircaseCorrection a b F (M, 0) = 0 := by
  simp [dyadicStaircaseCorrection]

/-- The recursive detail is the exact sum over all tree nodes; leaves
contribute zero. No monotonicity of the boundary is needed for this identity.
@isnad1 id=eq.0h5v.s5.b1f81c9d5046 from=translated src=- shape=ec2f0898 vocab=9f6e63b3
-/
theorem dyadicStaircaseDetail_eq_sum_tree (a b : ℕ → ℂ) (F : ℕ → ℕ) (M k : ℕ) :
    dyadicStaircaseDetail a b F M k =
      ∑ p ∈ dyadicTreeBlocks M k, dyadicStaircaseCorrection a b F p := by
  induction k generalizing M with
  | zero => simp [dyadicStaircaseDetail, dyadicTreeBlocks]
  | succ k ih =>
      rw [dyadicTreeBlocks, sum_insert (dyadicTreeBlocks_root_not_mem_children M k),
        sum_union (dyadicTreeBlocks_children_disjoint M k), ← ih M, ← ih (M + 2 ^ k)]
      simp only [dyadicStaircaseDetail, dyadicStaircaseCorrection, Nat.add_sub_cancel]
      ring

/-- Every internal node occurs in exactly one height group. The grouping
preserves the node formulas used in the geometric disjointness lemmas.
@isnad1 id=eq.0h5v.s6.55d011eb4f03 from=translated src=- shape=43fa00a6 vocab=df4f21a1
-/
theorem dyadicStaircaseDetail_eq_sum_levels (a b : ℕ → ℂ) (F : ℕ → ℕ) (M k : ℕ) :
    dyadicStaircaseDetail a b F M k =
      ∑ ℓ ∈ range k,
        ∑ p ∈ (dyadicTreeBlocks M k).filter (fun p => p.2 = ℓ + 1),
          dyadicStaircaseCorrection a b F p := by
  rw [dyadicStaircaseDetail_eq_sum_tree]
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have hheight := (mem_dyadicTreeBlocks_bounds M k p hp).2.2
  rcases p with ⟨m, h⟩
  cases h with
  | zero => simp
  | succ h =>
      have hh : h < k := by omega
      simp [hh]

/-- The same exact decomposition with the left-child height written as the
outer level index.
@isnad1 id=eq.0h5v.s8.ef625ad74b34 from=translated src=- shape=04bd745e vocab=2572283e
-/
theorem dyadicStaircaseDetail_eq_sum_levels_explicit
    (a b : ℕ → ℂ) (F : ℕ → ℕ) (M k : ℕ) :
    dyadicStaircaseDetail a b F M k =
      ∑ ℓ ∈ range k,
        ∑ p ∈ (dyadicTreeBlocks M k).filter (fun p => p.2 = ℓ + 1),
          (∑ m ∈ Ico p.1 (p.1 + 2 ^ ℓ), a m) *
            (∑ n ∈ Ico (F (p.1 + 2 ^ (ℓ + 1) - 1)) (F (p.1 + 2 ^ ℓ - 1)), b n) := by
  rw [dyadicStaircaseDetail_eq_sum_levels]
  apply sum_congr rfl
  intro ℓ _
  apply sum_congr rfl
  intro p hp
  simp only [dyadicStaircaseCorrection, (mem_filter.mp hp).2, Nat.add_sub_cancel]

/-- Triangle inequality grouped by height, retaining the product of norms
of the two rectangular factors.
@isnad1 id=le.0h5v.s8.aace73e38775 from=translated src=- shape=42077a0d vocab=8fde3829
-/
theorem norm_dyadicStaircaseDetail_le_levels
    (a b : ℕ → ℂ) (F : ℕ → ℕ) (M k : ℕ) :
    ‖dyadicStaircaseDetail a b F M k‖ ≤
      ∑ ℓ ∈ range k,
        ∑ p ∈ (dyadicTreeBlocks M k).filter (fun p => p.2 = ℓ + 1),
          ‖∑ m ∈ Ico p.1 (p.1 + 2 ^ (p.2 - 1)), a m‖ *
            ‖∑ n ∈ Ico (F (p.1 + 2 ^ p.2 - 1))
              (F (p.1 + 2 ^ (p.2 - 1) - 1)), b n‖ := by
  rw [dyadicStaircaseDetail_eq_sum_levels]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro ℓ _
  simpa only [dyadicStaircaseCorrection, norm_mul] using
    (norm_sum_le ((dyadicTreeBlocks M k).filter (fun p => p.2 = ℓ + 1))
      (dyadicStaircaseCorrection a b F))

/-- The baseline and all height groups bound the norm of the exact
staircase sum.
@isnad1 id=le.2h6v.s9.1a2a04561507 from=translated src=- shape=7ba29499 vocab=a5e0effd
-/
theorem norm_sum_dyadic_staircase_le_levels (a b : ℕ → ℂ) (F : ℕ → ℕ) (M N k : ℕ)
    (hN : ∀ m ∈ Ico M (M + 2 ^ k), N ≤ F m)
    (hF : AntitoneOn F (Set.Ico M (M + 2 ^ k))) :
    ‖∑ m ∈ Ico M (M + 2 ^ k), a m * (∑ n ∈ Ico N (F m), b n)‖ ≤
      ‖∑ m ∈ Ico M (M + 2 ^ k), a m‖ *
        ‖∑ n ∈ Ico N (F (M + 2 ^ k - 1)), b n‖ +
      ∑ ℓ ∈ range k,
        ∑ p ∈ (dyadicTreeBlocks M k).filter (fun p => p.2 = ℓ + 1),
          ‖∑ m ∈ Ico p.1 (p.1 + 2 ^ (p.2 - 1)), a m‖ *
            ‖∑ n ∈ Ico (F (p.1 + 2 ^ p.2 - 1))
              (F (p.1 + 2 ^ (p.2 - 1) - 1)), b n‖ := by
  rw [sum_dyadic_staircase_eq a b F M N k hN hF]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add le_rfl (norm_dyadicStaircaseDetail_le_levels a b F M k)

end TwinPrime.Analytic
