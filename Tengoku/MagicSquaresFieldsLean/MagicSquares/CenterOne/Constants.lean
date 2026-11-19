import Tengoku.MagicSquaresFieldsLean.MagicSquares.Bounds
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

/-!
# Constants in Sections 7 and 14
-/

/-- The real-valued closed form from Section 14:
`C₁(d) = d^7 (7d - 8) + 1`.-/
def centerOneC1 (d : ℕ) : ℝ :=
  (d : ℝ) ^ 7 * (7 * (d : ℝ) - 8) + 1

/-- Expanded form of `C₁`, matching the contribution grouped by support size
`r = 2,...,8`.-/
theorem centerOneC1_expanded (d : ℕ) :
    centerOneC1 d =
      28 * ((d : ℝ) - 1) ^ 2 +
      112 * ((d : ℝ) - 1) ^ 3 +
      210 * ((d : ℝ) - 1) ^ 4 +
      224 * ((d : ℝ) - 1) ^ 5 +
      140 * ((d : ℝ) - 1) ^ 6 +
      48 * ((d : ℝ) - 1) ^ 7 +
      7 * ((d : ℝ) - 1) ^ 8 := by
  unfold centerOneC1
  ring

@[simp]
theorem centerOneC1_one : centerOneC1 1 = 0 := by
  norm_num [centerOneC1]

@[simp]
theorem centerOneC1_two : centerOneC1 2 = 769 := by
  norm_num [centerOneC1]

/-- The Section 7 optimized square estimate is stronger than simply putting
`d=2` into `C₁`: the 28 quadratic terms are evaluated exactly rather than
bounded by `√q`.-/
noncomputable def centerOneSquareError (q : ℕ) : ℝ :=
  28 + 741 * Real.sqrt (q : ℝ)

end MagicSquares
