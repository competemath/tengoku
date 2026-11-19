import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterForms
import Tengoku.Seed.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Mathlib already contains Lemma 5.3 of the paper.-/
theorem quadraticChar_total_sum_zero (hodd : ringChar F ≠ 2) :
    ∑ x : F, (quadraticChar F) x = 0 := by
  exact quadraticChar_sum_zero hodd

/-- Mathlib already identifies quadratic-character value `1` with being a
nonzero square.-/
theorem quadraticChar_eq_one_iff_isSquare {x : F} (hx : x ≠ 0) :
    (quadraticChar F) x = 1 ↔ IsSquare x := by
  exact quadraticChar_one_iff_isSquare hx

omit [DecidableEq F] in
/-- The finite-field `-1` criterion available in mathlib.  In odd cardinality,
this reduces to the paper's `q ≡ 1 (mod 4)` formulation.-/
theorem neg_one_isSquare_iff_card_mod_four_ne_three :
    IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
  exact FiniteField.isSquare_neg_one_iff

end MagicSquares
