import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.PowerSeriesTrace
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.ExtensionSum
import Tengoku.Seed.RingTheory.PowerSeries.Expand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators Classical

/-- The denominator of the Euler factor attached to a degree-`d`
irreducible with character weight `a`.-/
noncomputable def eulerFactor (d : ℕ) (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X ^ d

theorem eulerFactor_constantCoeff {d : ℕ} (hd : 0 < d) (a : ℂ) :
    PowerSeries.constantCoeff (eulerFactor d a) = 1 := by
  simp [eulerFactor, Nat.ne_of_gt hd]

end MagicSquares.LN97
