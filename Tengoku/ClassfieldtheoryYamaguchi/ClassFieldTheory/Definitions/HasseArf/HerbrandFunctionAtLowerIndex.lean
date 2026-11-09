/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.Field.Rat
import Tengoku.Seed.Data.Finset.Interval
import Tengoku.Seed.SetTheory.Cardinal.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The Herbrand function at integral lower indices
-/

open scoped BigOperators

noncomputable section

namespace ClassFieldTheory

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The Herbrand value at a nonnegative integral lower index:
`φ(n) = (1 / |G₀|) · ∑_{i=1}^{n} |Gᵢ|`.

Its ramification-theoretic interpretation requires the lower groups to be
finite.  The definition alone does not impose that hypothesis.-/
def herbrandFunctionAtLowerIndex (A : ValuationSubring L) (n : ℕ) : ℚ :=
  (∑ i ∈ Finset.Icc 1 n,
      (Nat.card (lowerRamificationGroup K A i) : ℚ)) /
    (Nat.card (lowerRamificationGroup K A 0) : ℚ)

end ClassFieldTheory
