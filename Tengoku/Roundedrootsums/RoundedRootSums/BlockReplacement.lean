/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.BlockSum
import Tengoku.Roundedrootsums.RoundedRootSums.MainFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Block replacement

Decomposition of the square-root sum into complete square blocks.
-/

namespace RoundedRootSums

theorem sum_square_block_eq_blockSum (m : Nat) :
    Finset.sum (Finset.range (2 * m + 1))
        (fun k => Nat.sqrt (m ^ 2 + k)) =
      blockSum m := by
  rw [blockSum_formula]
  calc
    Finset.sum (Finset.range (2 * m + 1))
        (fun k => Nat.sqrt (m ^ 2 + k))
        =
        Finset.sum (Finset.range (2 * m + 1))
          (fun _ => m) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hklt : k < 2 * m + 1 :=
              Finset.mem_range.mp hk
            have hkle : k ≤ m + m := by
              omega
            exact Nat.sqrt_add_eq' m hkle
    _ = (2 * m + 1) * m := by
          simp
    _ = m * (2 * m + 1) := by
          exact Nat.mul_comm (2 * m + 1) m

theorem sum_before_square_eq_fullBlocks (m : Nat) :
    Finset.sum (Finset.range (m ^ 2 - 1))
        (fun k => Nat.sqrt (k + 1)) =
      fullBlocks m := by
  induction m with
  | zero =>
      simp [fullBlocks]
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        simp [fullBlocks, blockSum]
      · have hm_pos : 1 ≤ m := by
          omega
        have hm_sq_pos : 1 ≤ m ^ 2 := by
          nlinarith
        have hexpand :
            (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by
          ring
        have hsquare :
            (m + 1) ^ 2 - 1 =
              (m ^ 2 - 1) + (2 * m + 1) := by
          rw [hexpand]
          omega
        rw [hsquare]
        rw [Finset.sum_range_add]
        have htail :
            Finset.sum (Finset.range (2 * m + 1))
                (fun k =>
                  Nat.sqrt ((m ^ 2 - 1) + k + 1)) =
              blockSum m := by
          have hfun :
              (fun k =>
                Nat.sqrt ((m ^ 2 - 1) + k + 1)) =
              (fun k => Nat.sqrt (m ^ 2 + k)) := by
            funext k
            congr 1
            omega
          rw [hfun]
          exact sum_square_block_eq_blockSum m
        have hfull :
            fullBlocks (m + 1) =
              fullBlocks m + blockSum m := by
          unfold fullBlocks
          rw [Finset.sum_range_succ]
        rw [ih]
        rw [htail]
        exact hfull.symm

end RoundedRootSums
