/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic definitions

This file introduces the basic definitions used throughout the project,
including the square-root summatory function and its root index.
-/

namespace RoundedRootSums

/--
`rootSum n` is the sum

`⌊√1⌋ + ⌊√2⌋ + ⋯ + ⌊√n⌋`.-/
def rootSum (n : Nat) : Nat :=
  Finset.sum (Finset.range n) (fun k => Nat.sqrt (k + 1))

/--
The largest integer whose square does not exceed `n`.

Equivalently, `rootIndex n = ⌊√n⌋`.-/
def rootIndex (n : ℕ) : ℕ :=
  Nat.sqrt n

end RoundedRootSums
