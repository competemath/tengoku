import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.MomentOrthogonality
import Tengoku.Nlalib.NLAlib.Matrix.Functions.HermitianCalculus
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.SquareMeasures
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.FinitePolynomialMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Even and odd moments of the rectangular symmetric dilation

The actual block matrix `[0 B;Bᵀ 0]` at `(u,0)` has the even moments of `BBᵀ` at
`u` and zero odd moments. These finite block identities connect the native squared
measure reduction to rectangular matrix problems, including empty index types.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Every even power of the actual rectangular Hermitian dilation is block diagonal.
Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial)
@isnad1 id=eq.0h4v.s8.fc83df533ab7 from=translated src=- shape=583c46ba vocab=d55998ab
-/
theorem dilation_pow_two_mul (B : Matrix m n ℝ) (k : ℕ) :
    dilation B ^ (2 * k) = fromBlocks ((B * Bᵀ) ^ k) 0 0 ((Bᵀ * B) ^ k) := by
  rw [pow_mul, dilation_sq, fromBlocks_diagonal_pow]
  simp only [conjTranspose_eq_transpose_of_trivial]

/-- Every odd power of the actual rectangular symmetric dilation has zero diagonal
blocks. Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial)
@isnad1 id=eq.0h4v.s8.6051b9b87667 from=translated src=- shape=02ae3c71 vocab=110ee1c5
-/
theorem dilation_pow_two_mul_add_one (B : Matrix m n ℝ) (k : ℕ) :
    dilation B ^ (2 * k + 1) =
      fromBlocks 0 (((B * Bᵀ) ^ k) * B) (((Bᵀ * B) ^ k) * Bᵀ) 0 := by
  rw [pow_succ, dilation_pow_two_mul, dilation, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    conjTranspose_eq_transpose_of_trivial]

end NLAlib
