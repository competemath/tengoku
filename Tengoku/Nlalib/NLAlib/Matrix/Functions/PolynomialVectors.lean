import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.ChebyshevPolynomial
import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.LinearAlgebra.Matrix.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Matrices of normalized polynomial vectors

These are the actual columns evaluated by Chebyshev vector recurrences, before
any spectral-measure interpretation is imposed.
-/

noncomputable section
open scoped Matrix
open Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual matrix of normalized polynomial vectors, including degree zero.-/
def normalizedChebyshevVectorMatrix (H : Matrix n n ℂ) (b : n → ℂ) (M : ℕ) :
    Matrix n (Fin (M+1)) ℂ := fun r j =>
  ((aeval H ((normalizedChebyshevPolynomial j).map Complex.ofRealHom)) *ᵥ b) r

/-- Normalized polynomial vectors are the unnormalized recurrence vectors
multiplied by the exact mode weights.-/
theorem normalizedChebyshevVectorMatrix_apply (H : Matrix n n ℂ) (b : n → ℂ) (M : ℕ)
    (r : n) (j : Fin (M+1)) :
    normalizedChebyshevVectorMatrix H b M r j = (normalizedChebyshevWeight j : ℂ) *
      ((aeval H (Chebyshev.T ℂ (j : ℤ))) *ᵥ b) r := by
  simp only [normalizedChebyshevVectorMatrix, normalizedChebyshevPolynomial,
    Polynomial.map_mul, Polynomial.map_C, Chebyshev.map_T, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Complex.ofRealHom_eq_coe]

end NLAlib
