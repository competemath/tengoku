/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

import Tengoku.Roundedrootsums.RoundedRootSums.Blocks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Square-root blocks as finite intervals

This file defines the finite square-root block associated with an index `m`
and proves basic membership and constancy properties for that block.
-/

namespace RoundedRootSums

/--
The square-root block with index `m`.

It is the finite interval from `m ^ 2` through `(m + 1) ^ 2 - 1`.-/
def squareBlock (m : Nat) : Finset Nat :=
  Finset.Icc (m ^ 2) ((m + 1) ^ 2 - 1)

/--
Membership in a square-root block.
@isnad1 id=iff.0h2v.s6.1d3000c213e2 from=translated src=- shape=e7b77f9f vocab=29a3fb2f
-/
theorem mem_squareBlock_iff (m k : Nat) :
    k ∈ squareBlock m ↔
      m ^ 2 ≤ k ∧ k ≤ (m + 1) ^ 2 - 1 := by
  simp [squareBlock]

/--
Every element of the square-root block has integer square root equal to `m`.
@isnad1 id=eq.1h2v.s6.6820b4c85e11 from=translated src=- shape=00f4b682 vocab=41fa939d
-/
theorem sqrt_const_on_squareBlock
    (m t : Nat)
    (ht : t < 2 * m + 1) :
    Nat.sqrt (m ^ 2 + t) = m := by
  simpa [squareBlock] using sqrt_const_on_block m t ht

end RoundedRootSums
