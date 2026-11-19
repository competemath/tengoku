import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.PowerParameters
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Constants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Analytic interfaces for the center-one character sums

These propositions isolate the only analytic input in Sections 7 and 14:
Weil's bound applied after expanding the eight character-indicator factors.
Everything after these estimates -- removing at most nine parameters,
distinctness, and producing the magic square -- is proved in Lean below.

`CenterOne.SquareCount` now derives the square interface from the corrected
sharp quadratic Weil interface. `CenterOne.PowerCount` proves the
general-power counting interface from the proved sharp multiplicative
bound and the complete character-indicator expansion.

The square version records the sharper Section 7 estimate, where the 28
quadratic character sums are evaluated exactly and only the support-size
`r≥3` terms use Weil.
-/

/-- Section 7, after multiplying the normalized indicator sum by `256`:
`q - 28 - 741√q ≤ 256 * #(power-good t)`.-/
def HasCenterOneSquareCountBound (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ b : F, CenterOneGoodB b →
    (Fintype.card F : ℝ) - 28 -
        741 * Real.sqrt (Fintype.card F : ℝ)
      ≤ 256 * ((centerOnePowerParameters 2 b).card : ℝ)

/-- Section 14 count estimate:
`q - C₁(d)√q ≤ d^8 * #(power-good t)`.

This is the direct counting consequence of the character-indicator expansion;
the exact count dominates the paper's weighted sum at parameters where a
linear factor vanishes.-/
def HasCenterOnePowerCountBound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n d : ℕ) : Prop :=
  ∀ b : F, CenterOneGoodB b →
    (Fintype.card F : ℝ) -
        centerOneC1 d * Real.sqrt (Fintype.card F : ℝ)
      ≤ (d : ℝ) ^ 8 * ((centerOnePowerParameters n b).card : ℝ)

end Square3
end MagicSquares
