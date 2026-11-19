import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterForms
import Tengoku.Seed.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Mathlib already contains Lemma 5.3 of the paper.
@isnad1 id=eq.1h1v.s6.19f4efa4d292 from=translated src=- shape=61abbfd6 vocab=7ce15d3d
-/
theorem quadraticChar_total_sum_zero (hodd : ringChar F ≠ 2) :
    ∑ x : F, (quadraticChar F) x = 0 := by
  exact quadraticChar_sum_zero hodd

/-- Mathlib already identifies quadratic-character value `1` with being a
nonzero square.
@isnad1 id=iff.1h2v.s6.1e3fcebcf8f2 from=translated src=- shape=322b9653 vocab=a7494800
-/
theorem quadraticChar_eq_one_iff_isSquare {x : F} (hx : x ≠ 0) :
    (quadraticChar F) x = 1 ↔ IsSquare x := by
  exact quadraticChar_one_iff_isSquare hx

omit [DecidableEq F] in
/-- The finite-field `-1` criterion available in mathlib.  In odd cardinality,
this reduces to the paper's `q ≡ 1 (mod 4)` formulation.
@isnad1 id=iff.0h1v.s6.ec238b6492dd from=translated src=- shape=07526d6d vocab=aea6fd13
-/
theorem neg_one_isSquare_iff_card_mod_four_ne_three :
    IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
  exact FiniteField.isSquare_neg_one_iff

end MagicSquares
