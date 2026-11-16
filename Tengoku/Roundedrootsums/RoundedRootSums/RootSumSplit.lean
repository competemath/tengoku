/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku
import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.RootSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Splitting square-root sums

This file proves that the finite sum of integer square roots
can be split at an arbitrary intermediate index.
-/

namespace RoundedRootSums

/--
Splits `rootSum n` into the first `m` terms and the remaining tail,
provided `m ≤ n`.-/
theorem rootSum_split_at
    (m n : Nat)
    (h : m ≤ n) :
    rootSum n =
      Finset.sum (Finset.range m)
        (fun k => Nat.sqrt (k + 1)) +
      Finset.sum (Finset.range (n - m))
        (fun k => Nat.sqrt (m + k + 1)) := by
  unfold rootSum
  have hn : n = m + (n - m) := by
    omega
  rw [hn]
  simpa [Nat.add_assoc] using
    (Finset.sum_range_add
      (f := fun k => Nat.sqrt (k + 1))
      m
      (n - m))

end RoundedRootSums
