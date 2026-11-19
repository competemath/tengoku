import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.Complete
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma654.SimpleRoot
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.AffineQuadratic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character sum is exactly the error term in the point
count for `y² = f(x)`. Zeros of `f` are included with their correct fiber
cardinality one.
@isnad1 id=eq.1h2v.s6.d4d9505fae45 from=translated src=- shape=c86237c2 vocab=a69246e2
-/
theorem quadratic_sum_eq_solutionCount_sub_card
    (hodd : ringChar F ≠ 2) (f : Polynomial F) :
    (∑ x : F, quadraticChar F (f.eval x)) =
      (stepanovSolutionCount 2 f : ℤ) - Fintype.card F := by
  have hfiber (x : F) :
      ((Finset.univ.filter (fun y : F => y ^ 2 = f.eval x)).card : ℤ) =
        quadraticChar F (f.eval x) + 1 := by
    simpa using quadraticChar_card_sqrts hodd (f.eval x)
  rw [stepanovSolutionCount_eq_sum, Nat.cast_sum]
  simp_rw [hfiber]
  simp [Finset.sum_add_distrib]

end MagicSquares.LN97

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end MagicSquares
