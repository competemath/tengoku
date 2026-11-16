/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reciprocal square-root counts

This file introduces the counting function associated with the reciprocal
description of integer square-root sums.

For a fixed positive integer `m`, the relevant indices are those satisfying
`m ^ 2 ≤ k ≤ n`.
-/

namespace RoundedRootSums

/--
A natural number `m` does not exceed the integer square root of `k`
exactly when its square does not exceed `k`.
@isnad1 id=iff.0h2v.s5.5deccbf5c612 from=translated src=- shape=8b387b0b vocab=893cb839
-/
theorem le_sqrt_iff_sq_le (m k : Nat) :
    m ≤ Nat.sqrt k ↔ m ^ 2 ≤ k := by
  simpa [pow_two] using
    (Nat.le_sqrt : m ≤ Nat.sqrt k ↔ m * m ≤ k)

/--
For fixed `m`, the number of integers from `m ^ 2` through `n`,
written in a form that remains meaningful for all natural numbers.-/
def reciprocalCount (n m : Nat) : Nat :=
  n + 1 - m ^ 2

/--
If `m ^ 2 ≤ n`, then the reciprocal count is the length of the interval
from `m ^ 2` through `n`.
@isnad1 id=eq.1h2v.s6.8e3531a88748 from=translated src=- shape=ecfded54 vocab=65d62a47
-/
theorem reciprocalCount_formula
    (n m : Nat)
    (h : m ^ 2 ≤ n) :
    reciprocalCount n m = n - m ^ 2 + 1 := by
  unfold reciprocalCount
  omega

end RoundedRootSums
