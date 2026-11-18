import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Data.Nat.Prime.Basic
import Tengoku.Seed.Data.Rat.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The common definitions used throughout the formalization.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators

/-- The numerator of `∏_{j=1}^r (1 - p⁻ʲ)` after clearing powers of `p`.-/
def gammaNum (p r : ℕ) : ℕ :=
  ∏ j ∈ Finset.range r, (p ^ (j + 1) - 1)

/-- The common denominator of `∏_{j=1}^r (1 - p⁻ʲ)`.-/
def gammaDen (p r : ℕ) : ℕ :=
  p ^ (r * (r + 1) / 2)

/-- The finite Euler factor `γ_{p,r}`, represented exactly in `ℚ`.-/
def gammaQ (p r : ℕ) : ℚ :=
  (gammaNum p r : ℚ) / gammaDen p r

end SharpIntermediateSubgroupBounds
