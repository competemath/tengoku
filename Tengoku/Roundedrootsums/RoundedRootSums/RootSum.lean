/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku
import Tengoku.Roundedrootsums.RoundedRootSums.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer square-root sums

This file records the basic unfolding theorem for the finite sum
of integer square roots.
-/

namespace RoundedRootSums

/--
`rootSum n` is the sum of the integer square roots of the integers
from `1` through `n`.-/
theorem rootSum_unfold (n : Nat) :
    rootSum n =
      Finset.sum (Finset.range n)
        (fun k => Nat.sqrt (k + 1)) := by
  rfl

end RoundedRootSums
