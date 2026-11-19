import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Unknowns
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Core
import Tengoku.Seed.Algebra.Polynomial.OfFn
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Expanding the decoded coefficient blocks

This file turns the compact `blockEval (stepanovDecode v i)` notation
back into the literal finite sum from equation (6.22).
-/

omit [Fintype F] in
/-- Evaluation of a decoded outer polynomial is the expected finite
sum over its `u+1` coefficients.-/
theorem blockEval_stepanovDecode
    {m u D q : ℕ}
    (v : StepanovUnknowns F m u D)
    (i : Fin m) :
    blockEval q (stepanovDecode v i) =
      ∑ j : Fin (u + 1),
        stepanovInnerPolynomial v i j *
          (X ^ q : Polynomial F) ^ (j : ℕ) := by
  unfold blockEval stepanovDecode
  rw [Polynomial.ofFn_eq_sum_monomial]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [stepanovInnerPolynomial]

omit [Fintype F] in
/-- The complete auxiliary polynomial with decoded coefficients is the
literal double sum of (6.22).-/
theorem stepanovAuxiliary_decode_eq_doubleSum
    {m u D q M : ℕ}
    (f g : Polynomial F)
    (v : StepanovUnknowns F m u D) :
    stepanovAuxiliary q M f g (stepanovDecode v) =
      ∑ i : Fin m,
        ∑ j : Fin (u + 1),
          f ^ M *
            stepanovInnerPolynomial v i j *
            g ^ (i : ℕ) *
            (X ^ q : Polynomial F) ^ (j : ℕ) := by
  unfold stepanovAuxiliary stepanovBracket
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [blockEval_stepanovDecode]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end LN97
end MagicSquares
