/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.BlockSum
import Tengoku.Roundedrootsums.RoundedRootSums.PowerBlocks
import Tengoku.Roundedrootsums.RoundedRootSums.IntervalSums
import Tengoku.Roundedrootsums.RoundedRootSums.RootSum
import Tengoku.Roundedrootsums.RoundedRootSums.RootSumSplit
import Tengoku.Roundedrootsums.RoundedRootSums.ReciprocalRootSum
import Tengoku.Roundedrootsums.RoundedRootSums.RangeArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed formulas for integer square-root sums

This file introduces the contributions of the complete square blocks and the
final partial block.

It also proves closed and fully explicit formulas for the finite sum

`⌊√1⌋ + ⌊√2⌋ + ⋯ + ⌊√n⌋`.
-/

open scoped BigOperators

namespace RoundedRootSums

/--
The total contribution of the complete square-root blocks with indices
strictly below `m`.-/
def fullBlocks (m : Nat) : Nat :=
  Finset.sum (Finset.range m) blockSum

/--
The contribution of the final partial square-root block beginning at `m ^ 2`
and ending at `n`.-/
def lastBlock (m n : Nat) : Nat :=
  (n - m ^ 2 + 1) * m

/--
The sum of the complete square-root blocks can be written as the sum of their
explicit block formulas.-/
theorem fullBlocks_formula (m : Nat) :
    fullBlocks m =
      Finset.sum (Finset.range m)
        (fun j => j * (2 * j + 1)) := by
  unfold fullBlocks
  apply Finset.sum_congr rfl
  intro j hj
  exact blockSum_formula j

/--
The contribution of the final partial block is its length multiplied by its
constant square-root value.-/
theorem lastBlock_formula (m n : Nat) :
    lastBlock m n = (n - m ^ 2 + 1) * m := by
  rfl

/--
Closed formula for the sum of integer square roots.

The sum is expressed using `rootIndex n = ⌊√n⌋` and a finite sum of squares.-/
theorem rootSum_closed_formula (n : Nat) :
    rootSum n =
      rootIndex n * (n + 1) -
        Finset.sum (Finset.Icc 1 (rootIndex n))
          (fun m => m ^ 2) := by
  rw [reciprocal_root_identity]
  have htotal :
      Finset.sum (Finset.Icc 1 (rootIndex n))
          (fun m => reciprocalCount n m) +
        Finset.sum (Finset.Icc 1 (rootIndex n))
          (fun m => m ^ 2) =
      rootIndex n * (n + 1) := by
    calc
      Finset.sum (Finset.Icc 1 (rootIndex n))
            (fun m => reciprocalCount n m) +
          Finset.sum (Finset.Icc 1 (rootIndex n))
            (fun m => m ^ 2) =
        Finset.sum (Finset.Icc 1 (rootIndex n))
          (fun m => reciprocalCount n m + m ^ 2) := by
            rw [Finset.sum_add_distrib]
      _ =
        Finset.sum (Finset.Icc 1 (rootIndex n))
          (fun _ => n + 1) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hm_le : m ≤ rootIndex n :=
              (Finset.mem_Icc.mp hm).2
            have hsq : m ^ 2 ≤ n := by
              apply (le_sqrt_iff_sq_le m n).1
              simpa [rootIndex] using hm_le
            unfold reciprocalCount
            omega
      _ = rootIndex n * (n + 1) := by
            simp [Nat.card_Icc]
  omega

/--
Fully explicit closed formula for the sum of integer square roots.-/
theorem rootSum_explicit_formula (n : Nat) :
    rootSum n =
      rootIndex n * (n + 1) -
        rootIndex n * (rootIndex n + 1) *
          (2 * rootIndex n + 1) / 6 := by
  rw [rootSum_closed_formula]
  rw [sum_squares_Icc_one]

end RoundedRootSums
