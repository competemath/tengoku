/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.MainFormula
import Tengoku.Roundedrootsums.RoundedRootSums.RootSumSplit
import Tengoku.Roundedrootsums.RoundedRootSums.SumLemmas
import Tengoku.Roundedrootsums.RoundedRootSums.BlockReplacement
import Tengoku.Roundedrootsums.RoundedRootSums.Blocks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Main theorem

This file proves the main decomposition formula
for the sum of integer square roots.
-/

namespace RoundedRootSums

/--
Decomposition of the integer square-root sum into complete square blocks
and one final partial block.

If `m ^ 2 ≤ n < (m + 1) ^ 2`, then the terms up to `m ^ 2 - 1`
form the complete blocks indexed below `m`, while the remaining terms
all have integer square root equal to `m`.
@isnad1 id=eq.2h2v.s6.c6c959814216 from=translated src=- shape=f20383f5 vocab=eea02368
-/
theorem rootSum_main_formula
    (m n : Nat)
    (h₁ : m ^ 2 ≤ n)
    (h₂ : n < (m + 1) ^ 2) :
    rootSum n =
      fullBlocks m +
      lastBlock m n := by
  cases m with
  | zero =>
      have hn : n = 0 := by
        omega
      subst n
      simp [rootSum, fullBlocks, lastBlock]
  | succ m =>
      have hsplit :
          (m + 1) ^ 2 - 1 ≤ n := by
        omega
      rw [rootSum_split_at ((m + 1) ^ 2 - 1) n hsplit]
      rw [sum_before_square_eq_fullBlocks]
      have hsquare_pos :
          1 ≤ (m + 1) ^ 2 := by
        have hm_pos : 1 ≤ m + 1 := by
          omega
        nlinarith
      have hsquare_pred :
          (m + 1) ^ 2 - 1 + 1 =
            (m + 1) ^ 2 := by
        exact Nat.sub_add_cancel hsquare_pos
      have hlength :
          n - ((m + 1) ^ 2 - 1) =
            n - (m + 1) ^ 2 + 1 := by
        omega
      rw [hlength]
      have htail :
          Finset.sum
              (Finset.range (n - (m + 1) ^ 2 + 1))
              (fun k =>
                Nat.sqrt
                  (((m + 1) ^ 2 - 1) + k + 1)) =
            (n - (m + 1) ^ 2 + 1) * (m + 1) := by
        calc
          Finset.sum
              (Finset.range (n - (m + 1) ^ 2 + 1))
              (fun k =>
                Nat.sqrt
                  (((m + 1) ^ 2 - 1) + k + 1))
              =
              Finset.sum
                (Finset.range (n - (m + 1) ^ 2 + 1))
                (fun _ => m + 1) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  have hklt :
                      k < n - (m + 1) ^ 2 + 1 := by
                    exact Finset.mem_range.mp hk
                  apply sqrt_eq_of_mem_block (m + 1)
                  · omega
                  · omega
          _ = (n - (m + 1) ^ 2 + 1) * (m + 1) := by
                simp
      rw [htail]
      rfl

end RoundedRootSums
