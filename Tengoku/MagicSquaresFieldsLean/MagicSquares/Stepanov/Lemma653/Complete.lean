import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.SetBound
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.SpecialPolynomials
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.Abstract

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lidl--Niederreiter Theorem 6.53

The completed Lemmas 6.45 and 6.52 give the point count for the actual
curve `y^m=f(x)`, with no separate counting or auxiliary-polynomial
assumptions.  Applying (6.28) to `X-1` and the geometric polynomial yields
the two bounds used in the numerical proof.
-/

theorem stepanovFullT_B1 (m : ℕ) (f : Polynomial F) :
    stepanovFullT m f theorem653B1 = stepanovT0 f ∪ stepanovT1 m f := by
  ext c
  simp [stepanovFullT, theorem653B1, Polynomial.IsRoot, sub_eq_zero]

theorem stepanovFullT_B2 (m : ℕ) (f : Polynomial F) :
    stepanovFullT m f (theorem653B2 m) = stepanovT0 f ∪ stepanovT2 m f := by
  ext c
  simp [stepanovFullT, theorem653B2, Polynomial.IsRoot]

end LN97
end MagicSquares
