import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.MonicSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- The untruncated monic generating series is the finite split
L-polynomial, by the coefficient cancellation theorem.
@isnad1 id=eq.2h4v.s7.8ed93786c3c8 from=translated src=- shape=3cdd3452 vocab=03ffaf34
-/
theorem splitLPolynomial_eq_monicSeries {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) :
    (splitLPolynomial roots chars : PowerSeries ℂ) =
      avoidingSeries (fun g => splitDegreeWeight roots chars g.natDegree g) ∅ := by
  ext n
  rw [Polynomial.coeff_coe, splitLPolynomial_coeff roots hinj chars hchars,
    avoidingSeries_coeff]
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    Finset.filter_true_of_mem]
  rw [sum_monicPolynomials]
  simp only [monicOfCoeffs_natDegree, splitLCoeff]

end MagicSquares.LN97
