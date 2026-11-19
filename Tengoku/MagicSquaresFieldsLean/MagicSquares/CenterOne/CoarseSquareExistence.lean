import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.SquareCount
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.CoarseQuadratic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Square3

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The coarser count suffices at the explicit threshold `11521²`.
@isnad1 id=lt.1h1v.s6.356212dc2419 from=translated src=- shape=87843174 vocab=b134fd7f
-/
theorem centerOne_coarse_numeric_bound {q : ℕ} (hq : 132733441 ≤ q) :
    (2304 : ℝ) < (q : ℝ) - 28 - 11520 * Real.sqrt (q : ℝ) := by
  have hqR : (132733441 : ℝ) ≤ q := by exact_mod_cast hq
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)
  have hs : (11521 : ℝ) ≤ Real.sqrt (q : ℝ) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hs0]

end MagicSquares.Square3
