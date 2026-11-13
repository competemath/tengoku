import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovControllability
import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovStability
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.Complexification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Actual real continuous Lyapunov Gramians -/
noncomputable section
open MeasureTheory Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
set_option backward.isDefEq.respectTransparency false

/-- Entrywise real part, as a continuous real linear map on matrices.-/
def matrixRealPart : Matrix n n ℂ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.map Complex.re
      map_add' := by intro A B; ext i j; simp
      map_smul' := by intro c A; ext i j; simp }

@[simp] theorem matrixRealPart_complexification (A : Matrix n n ℝ) :
    matrixRealPart (realMatrixComplexification A) = A := by ext i j; rfl

/-- Complexification commutes with the actual real matrix exponential.-/
theorem realMatrixComplexification_matrixExp (A : Matrix n n ℝ) :
    (realMatrixComplexification (matrixExp A) : Matrix n n ℂ) =
      matrixExp (realMatrixComplexification A) := by
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) realMatrixComplexification
    continuous_realMatrixComplexification A (by
      rw [NormedSpace.expSeries_radius_eq_top]
      exact edist_lt_top _ _)

/-- The actual real semigroup integrand.-/
def realLyapunovIntegrand (A Q : Matrix n n ℝ) (t : ℝ) : Matrix n n ℝ :=
  matrixExp (t • A) * Q * (matrixExp (t • A))ᴴ

/-- The actual real improper Bochner Gramian.-/
def realLyapunovGramian (A Q : Matrix n n ℝ) : Matrix n n ℝ :=
  ∫ t in Ioi (0 : ℝ), realLyapunovIntegrand A Q t

/-- The actual integrands commute with scalar extension.-/
theorem realMatrixComplexification_lyapunovIntegrand (A Q : Matrix n n ℝ) (t : ℝ) :
    (realMatrixComplexification (realLyapunovIntegrand A Q t) : Matrix n n ℂ) =
      lyapunovIntegrand (realMatrixComplexification A) (realMatrixComplexification Q) t := by
  unfold realLyapunovIntegrand lyapunovIntegrand
  rw [map_mul, map_mul, realMatrixComplexification_matrixExp, map_smul]
  have hstar : (realMatrixComplexification (matrixExp (t • A))ᴴ : Matrix n n ℂ) =
      (realMatrixComplexification (matrixExp (t • A)))ᴴ := map_star realMatrixComplexification _
  rw [hstar, realMatrixComplexification_matrixExp, map_smul]

end NLAlib
