import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.MonicLanczosCoefficients
import Tengoku.Nlalib.NLAlib.Krylov.Processes.LanczosRecurrence
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.JacobiCoefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Positive Lanczos compressions are the canonical moment Jacobi matrices

Monic recurrence coefficients already identify the diagonals and squared signed
off-diagonals. Nonnegative Lanczos off-diagonals select the canonical square roots,
giving equality of the actual matrices, not only their spectra. The actual three-term
Lanczos process has this sign convention, including empty order.

Source: Gautschi (2004), §§1.3 and 2.2.3.
Atlas: `discrete-measure-jacobi-matrix`.
-/

noncomputable section
open Matrix Polynomial MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Jacobi matrix assembled from the actual Lanczos recursion's coefficients is the
actual compression at every valid order. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial)
@isnad1 id=eq.2h4v.s6.99508dd93fd8 from=translated src=- shape=a3220c8d vocab=b97002c3
-/
theorem jacobiMatrix_lanczosAlpha_lanczosBeta_eq_T
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) {q : ℕ}
    (hq : q ≤ krylovGrade A b) :
    jacobiMatrix (lanczosAlpha A b) (lanczosBeta A b) q =
      LanczosDecomp.T (arnoldiDecomp A b q hq) := by
  rw [LanczosDecomp.T_eq_jacobiMatrix _ hA]
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with hij hupper hlower
  · exact lanczosAlpha_eq_alpha hA b hq i.isLt
  · exact lanczosBeta_eq_beta hA b hq j.isLt
  · exact lanczosBeta_eq_beta hA b hq i.isLt
  · rfl

end NLAlib
