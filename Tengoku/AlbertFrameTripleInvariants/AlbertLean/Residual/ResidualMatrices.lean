import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.TrialitySquares
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residual source matrices and determinant orientations

This module packages the vector-coordinate matrix `X` and covector-coordinate
matrix `A` in the frozen residual-chart order.  The accepted evaluation matrix
is proved to be `A * X`, and the two accepted exterior brackets are identified
with the corresponding determinants with their signs fixed by that order.

These are coordinate identities.  They do not classify the structured source
model, construct a quotient, or identify any involution with a deck action.
-/

namespace AlbertLean.Residual.ResidualMatrices

open Matrix
open AlbertLean.Triality
open ExteriorSix
open AlbertLean.Residual.TrialitySquares

variable {K : Type*} [Field K] [CharZero K]

/-- the vector-coordinate matrix with
columns in the frozen order `p1, p2, q1, q2`.-/
def XMatrix (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i j => ![s1.p i, s2.p i, c1.q i, c2.q i] j

/-- the covector-coordinate matrix with
rows in the frozen order `phi1, phi2, psi1, psi2`.-/
def AMatrix (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i j => ![s1.phi j, s2.phi j, c1.psi j, c2.psi j] i

/-- entrywise evaluation is
exactly matrix multiplication in the frozen row and column orders.-/
theorem momentMatrix_eq_AMatrix_mul_XMatrix
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    momentMatrix s1 s2 c1 c2 =
      AMatrix s1 s2 c1 c2 * XMatrix s1 s2 c1 c2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentMatrix, AMatrix, XMatrix, Matrix.mul_apply, evalU,
      Fin.sum_univ_succ] <;>
    ring

/-- the minus sign in `deltaX`
compensates for the interleaved exterior input order, so the result is the
determinant with columns `p1, p2, q1, q2`.-/
theorem deltaX_eq_det_XMatrix
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    deltaX s1 s2 c1 c2 = Matrix.det (XMatrix s1 s2 c1 c2) := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, XMatrix, deltaX, BW, wedge2,
    Fin.succAbove, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  ring_nf

/-- the minus sign in
`deltaStarA` compensates for the interleaved dual exterior input order, so the
result is the determinant with rows `phi1, phi2, psi1, psi2`.-/
theorem deltaStarA_eq_det_AMatrix
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    deltaStarA s1 s2 c1 c2 = Matrix.det (AMatrix s1 s2 c1 c2) := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, AMatrix, deltaStarA, BW, hodgeStar,
    dualWedge2, Fin.succAbove, Finset.sum_fin_eq_sum_range,
    Finset.sum_range_succ]
  ring_nf

/-- determinant
multiplicativity turns `M = A * X` into the product of the two frozen oriented
four-brackets.-/
theorem det_momentMatrix_eq_deltaX_mul_deltaStarA
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    Matrix.det (momentMatrix s1 s2 c1 c2) =
      deltaX s1 s2 c1 c2 * deltaStarA s1 s2 c1 c2 := by
  rw [momentMatrix_eq_AMatrix_mul_XMatrix, Matrix.det_mul,
    ← deltaStarA_eq_det_AMatrix, ← deltaX_eq_det_XMatrix]
  ring

end AlbertLean.Residual.ResidualMatrices
