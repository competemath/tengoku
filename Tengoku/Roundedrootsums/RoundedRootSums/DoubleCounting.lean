/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.ReciprocalRoot
import Tengoku.Roundedrootsums.RoundedRootSums.FiberCard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Double counting

This file develops the double-counting argument used to rewrite
the square-root sum as a sum of reciprocal counting terms.
-/

open scoped BigOperators

namespace RoundedRootSums

/--
The admissible pairs `(k, m)` used in the reciprocal double count.

Here `k` ranges from `0` to `n - 1`, so `k + 1` represents
the original summation index from `1` to `n`.

The second coordinate satisfies
`1 ≤ m ≤ rootIndex n` and `m ^ 2 ≤ k + 1`.-/
def admissiblePairs (n : Nat) : Finset (Nat × Nat) :=
  ((Finset.range n).product (Finset.Icc 1 (rootIndex n))).filter
    (fun p => p.2 ^ 2 ≤ p.1 + 1)

/--
Counting admissible pairs by the first coordinate.
@isnad1 id=eq.0h1v.s6.faf36b9437df from=translated src=- shape=c3ae403b vocab=5e16a969
-/
theorem admissiblePairs_card_by_k (n : Nat) :
    (admissiblePairs n).card =
      Finset.sum (Finset.range n)
        (fun k =>
          ((Finset.Icc 1 (rootIndex n)).filter
            (fun m => m ^ 2 ≤ k + 1)).card) := by
  unfold admissiblePairs
  simpa using
    card_filter_product_eq_sum
      (Finset.range n)
      (Finset.Icc 1 (rootIndex n))
      (fun k m => m ^ 2 ≤ k + 1)

/--
Counting admissible pairs by the second coordinate.
@isnad1 id=eq.0h1v.s6.fe97d6daa04c from=translated src=- shape=bf7f36fb vocab=5e16a969
-/
theorem admissiblePairs_card_by_m (n : Nat) :
    (admissiblePairs n).card =
      Finset.sum (Finset.Icc 1 (rootIndex n))
        (fun m =>
          ((Finset.range n).filter
            (fun k => m ^ 2 ≤ k + 1)).card) := by
  unfold admissiblePairs
  simpa using
    card_filter_product_eq_sum_right
      (Finset.range n)
      (Finset.Icc 1 (rootIndex n))
      (fun k m => m ^ 2 ≤ k + 1)

/--
For a positive admissible `m`, the number of indices `k < n`
satisfying `m ^ 2 ≤ k + 1` equals `reciprocalCount n m`.
@isnad1 id=eq.2h2v.s6.d7f87c834367 from=translated src=- shape=47a3157f vocab=a64b42e2
-/
theorem filtered_range_card_eq_reciprocalCount
    (n m : Nat)
    (hm_pos : 1 ≤ m)
    (hm : m ≤ rootIndex n) :
    ((Finset.range n).filter
      (fun k => m ^ 2 ≤ k + 1)).card =
      reciprocalCount n m := by
  have hsq : m ^ 2 ≤ n := by
    apply (le_sqrt_iff_sq_le m n).1
    simpa [rootIndex] using hm
  have hsq_pos : 1 ≤ m ^ 2 := by
    nlinarith
  have hfilter :
      (Finset.range n).filter
          (fun k => m ^ 2 ≤ k + 1) =
        Finset.Icc (m ^ 2 - 1) (n - 1) := by
    ext k
    simp only [
      Finset.mem_filter,
      Finset.mem_range,
      Finset.mem_Icc
    ]
    omega
  rw [hfilter, Nat.card_Icc]
  unfold reciprocalCount
  omega

/--
Counting admissible pairs by the second coordinate
and evaluating every fiber explicitly.
@isnad1 id=eq.0h1v.s4.20cbcce6a56a from=translated src=- shape=f5a60935 vocab=11107500
-/
theorem admissiblePairs_card_by_reciprocalCount (n : Nat) :
    (admissiblePairs n).card =
      Finset.sum (Finset.Icc 1 (rootIndex n))
        (fun m => reciprocalCount n m) := by
  rw [admissiblePairs_card_by_m]
  apply Finset.sum_congr rfl
  intro m hm
  have hm_bounds : 1 ≤ m ∧ m ≤ rootIndex n := by
    exact Finset.mem_Icc.mp hm
  exact filtered_range_card_eq_reciprocalCount
    n m hm_bounds.1 hm_bounds.2

end RoundedRootSums
