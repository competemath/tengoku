import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterZero.PowerBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

/-- The exact cubic numerical inequality holds from `q = 1037` onward.-/
theorem cube_centerZero_inequality {q : ℕ} (hq : 1037 ≤ q) :
    (135 : ℝ) < (q : ℝ) - 28 * Real.sqrt (q : ℝ) := cube_numeric_bound hq

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end MagicSquares
