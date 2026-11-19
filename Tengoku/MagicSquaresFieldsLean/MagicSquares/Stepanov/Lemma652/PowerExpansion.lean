import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.PowerReduction
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# The identity c^i = sum_t b_{t,i} c^t

This is the exact finite-power reduction used on p. 306 of LN97 6.52.
-/

/-- Evaluation form of the power-reduction identity.-/
theorem pow_eq_sum_powerReductionCoeff
    (B : Polynomial F) (i r : ℕ) (c : F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r)
    (hc : B.IsRoot c) :
    c ^ i =
      ∑ t ∈ Finset.range r,
        powerReductionCoeff B i t * c ^ t := by
  have hrem :=
    powerRemainder_eq_sum_range
      (F := F) B i r hB hr hdeg
  have heval :=
    congrArg (fun P : Polynomial F => eval c P) hrem
  rw [eval_powerRemainder_eq_pow_of_isRoot
    (F := F) B i c hc] at heval
  simpa [Polynomial.eval_finsetSum, Polynomial.eval_monomial] using heval

/-- The same identity with the two sides oriented as in the book.-/
theorem sum_powerReductionCoeff_eq_pow
    (B : Polynomial F) (i r : ℕ) (c : F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r)
    (hc : B.IsRoot c) :
    (∑ t ∈ Finset.range r,
        powerReductionCoeff B i t * c ^ t) = c ^ i :=
  (pow_eq_sum_powerReductionCoeff
    (F := F) B i r c hB hr hdeg hc).symm

end LN97
end MagicSquares
