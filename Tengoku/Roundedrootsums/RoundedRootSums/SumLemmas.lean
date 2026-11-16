/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku
import Tengoku.Roundedrootsums.RoundedRootSums.RangeArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Auxiliary summation lemmas

This file contains auxiliary lemmas for splitting finite sums over ranges.
-/

namespace RoundedRootSums

/--
Splits a sum over `Finset.range n` at an index `a ≤ n`.

The first summand contains the terms with indices below `a`, while the second
summand contains the remaining terms after shifting their indices by `a`.
@isnad1 id=eq.1h4v.s6.7a6d3fc98521 from=translated src=- shape=e6ca7c3a vocab=408b43ff
-/
theorem sum_range_split_sub
    {α : Type*}
    [AddCommMonoid α]
    (f : Nat → α)
    (a n : Nat)
    (h : a ≤ n) :
    Finset.sum (Finset.range n) f =
      Finset.sum (Finset.range a) f +
      Finset.sum (Finset.range (n - a))
        (fun k => f (a + k)) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  exact Finset.sum_range_add f a b

end RoundedRootSums
