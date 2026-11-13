import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SpectralBounds
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SingularValueInvariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Scaling singular values

Absolute homogeneity `σ_k(cA) = |c| σ_k(A)` on arbitrary finite index types, including zero
scalars and empty matrix dimensions; negation invariance.
Source: Horn–Johnson (2013), §2.6; helpers for the Ky Fan and Schatten norm APIs.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Scaling a rectangular diagonal scales the represented sequence.-/
theorem rectDiag_smul {m n : ℕ} (c : ℝ) (a : ℕ → ℝ) :
    (rectDiag (c • a) : Matrix (Fin m) (Fin n) ℝ) = c • rectDiag a := by
  ext i j
  simp only [rectDiag_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split <;> simp_all

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

end NLAlib
