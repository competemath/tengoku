/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interval sum lemmas

Auxiliary lemmas for splitting finite sums over integer intervals.

These lemmas are used in later proofs involving block decompositions of
square-root sums.
-/

namespace RoundedRootSums

/--
Split a sum over `Finset.Icc a (b + 1)` into the sum over
`Finset.Icc a b` together with the last term.
@isnad1 id=eq.1h4v.s6.0ea7ae4eb1f7 from=translated src=- shape=8a7996e1 vocab=6e366bd1
-/
theorem sum_Icc_split_succ
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    (a b : ℕ)
    (h : a ≤ b + 1) :
    ∑ k ∈ Finset.Icc a (b + 1), f k =
      (∑ k ∈ Finset.Icc a b, f k) + f (b + 1) := by
  exact Finset.sum_Icc_succ_top h f

end RoundedRootSums
