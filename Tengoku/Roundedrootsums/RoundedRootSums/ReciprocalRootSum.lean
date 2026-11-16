/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.ReciprocalRoot
import Tengoku.Roundedrootsums.RoundedRootSums.DoubleCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reciprocal representation of square-root sums

This file develops a reciprocal counting representation of the finite sum
of integer square roots.

The main result rewrites `rootSum n` as a sum over positive integers
`m ≤ rootIndex n`, where each term counts the indices `k ≤ n`
satisfying `m ^ 2 ≤ k`.
-/

open scoped BigOperators

namespace RoundedRootSums

/--
The interval from `1` through `Nat.sqrt k` has cardinality `Nat.sqrt k`.-/
theorem card_Icc_one_sqrt (k : Nat) :
    (Finset.Icc 1 (Nat.sqrt k)).card = Nat.sqrt k := by
  rw [Nat.card_Icc]
  omega

/--
If `k ≤ n` and `m ^ 2 ≤ k`, then `m` does not exceed
the integer square root of `n`.-/
theorem sq_le_implies_le_rootIndex
    (m k n : Nat)
    (hk : k ≤ n)
    (hm : m ^ 2 ≤ k) :
    m ≤ rootIndex n := by
  unfold rootIndex
  apply (le_sqrt_iff_sq_le m n).2
  omega

/--
For `k ≤ n`, the positive integers `m ≤ rootIndex n`
satisfying `m ^ 2 ≤ k` are precisely the integers
from `1` through `Nat.sqrt k`.-/
theorem sqrt_as_filtered_card
    (k n : Nat)
    (hk : k ≤ n) :
    Nat.sqrt k =
      ((Finset.Icc 1 (rootIndex n)).filter
        (fun m => m ^ 2 ≤ k)).card := by
  have hfilter :
      (Finset.Icc 1 (rootIndex n)).filter
          (fun m => m ^ 2 ≤ k) =
        Finset.Icc 1 (Nat.sqrt k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hm
      exact ⟨hm.1.1, (le_sqrt_iff_sq_le m k).2 hm.2⟩
    · intro hm
      have hsq : m ^ 2 ≤ k :=
        (le_sqrt_iff_sq_le m k).1 hm.2
      exact
        ⟨⟨hm.1,
            sq_le_implies_le_rootIndex m k n hk hsq⟩,
          hsq⟩
  rw [hfilter, card_Icc_one_sqrt]

/--
Each term in `rootSum n` can be replaced by the number of admissible
reciprocal indices `m`.-/
theorem rootSum_as_filtered_cards (n : Nat) :
    rootSum n =
      Finset.sum (Finset.range n) (fun k =>
        ((Finset.Icc 1 (rootIndex n)).filter
          (fun m => m ^ 2 ≤ k + 1)).card) := by
  unfold rootSum
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k + 1 ≤ n := by
    exact Nat.succ_le_of_lt (Finset.mem_range.mp hk)
  exact sqrt_as_filtered_card (k + 1) n hk'

/--
Reciprocal counting identity for integer square roots.

The sum of `⌊√k⌋` for `1 ≤ k ≤ n` equals the sum, over
`1 ≤ m ≤ ⌊√n⌋`, of the number of integers `k ≤ n`
satisfying `m ^ 2 ≤ k`.-/
theorem reciprocal_root_identity (n : Nat) :
    rootSum n =
      Finset.sum (Finset.Icc 1 (rootIndex n))
        (fun m => reciprocalCount n m) := by
  rw [rootSum_as_filtered_cards]
  rw [← admissiblePairs_card_by_k]
  exact admissiblePairs_card_by_reciprocalCount n

end RoundedRootSums
