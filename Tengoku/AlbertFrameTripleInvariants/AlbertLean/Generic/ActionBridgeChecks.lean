/-
Independent semantic regression fixture for the generic residual action.

These checks cross the ResidualAction and ResidualMatrices APIs, with
independent concrete witnesses for the frozen conventions.
-/

import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.ResidualMatrices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace AlbertLean.Generic.ActionBridgeChecks

open Matrix
open scoped BigOperators
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Generic.ExteriorAction
open AlbertLean.Generic.ResidualAction

variable {K : Type*} [Field K] [CharZero K]

/- Cross the independently imported four-column matrix reader with the new
source action.  A transpose or wrong side of multiplication fails here. -/
/--
@isnad1 id=eq.0h6v.s7.d8396fef428a from=translated src=- shape=fe7919b5 vocab=55b5eb27
-/
theorem XMatrix_actS_actC (G : DetOneMatrix K)
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    XMatrix (actS G s1) (actS G s2) (actC G c1) (actC G c2) =
      G.g * XMatrix s1 s2 c1 c2 := by
  ext i j
  fin_cases j <;>
    simp [XMatrix, actS, actC, vecAct, Matrix.mul_apply,
      Matrix.mulVec, dotProduct]

/- Cross the independently imported four-row matrix reader with the new
dual action.  Using g instead of gInv, or multiplying on the left, fails. -/
/--
@isnad1 id=eq.0h6v.s7.ff97f59420bc from=translated src=- shape=b7a74bc0 vocab=657fe709
-/
theorem AMatrix_actS_actC (G : DetOneMatrix K)
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    AMatrix (actS G s1) (actS G s2) (actC G c1) (actC G c2) =
      AMatrix s1 s2 c1 c2 * G.gInv := by
  ext i j
  fin_cases i <;>
    simp [AMatrix, actS, actC, covAct, Matrix.mul_apply,
      Matrix.vecMul, dotProduct]

def sourcePair (s1 s2 : SCoord K) (c1 c2 : CCoord K) : ResidualPair K where
  A := AMatrix s1 s2 c1 c2
  X := XMatrix s1 s2 c1 c2

/- One bundled statement matching the actual source action to the old
explicit residual-pair action. -/
/--
@isnad1 id=eq.0h6v.s6.291b30f81d6a from=translated src=- shape=cdeefc05 vocab=bcb3b898
-/
theorem sourcePair_act (G : DetOneMatrix K)
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    sourcePair (actS G s1) (actS G s2) (actC G c1) (actC G c2) =
      AlbertLean.Residual.SL4PairAction.act G (sourcePair s1 s2 c1 c2) := by
  apply ResidualPair.ext
  · exact AMatrix_actS_actC G s1 s2 c1 c2
  · exact XMatrix_actS_actC G s1 s2 c1 c2

section ConcreteConventionWitness

/- g = I + E_01 and h = I - E_01. -/
def shear : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![1, 1, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

def shearInv : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![1, -1, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

/--
@isnad1 id=eq.0h0v.s7.1bb8fced6c55 from=translated src=- shape=af6c9ceb vocab=0d8a3800
-/
theorem shear_inverse_left : shearInv * shear = 1 := by
  ext i j
  change (∑ k : Fin 4, shearInv i k * shear k j) = (1 : Matrix (Fin 4) (Fin 4) ℚ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shear, shearInv, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s7.19714e2db613 from=translated src=- shape=af6c9ceb vocab=0d8a3800
-/
theorem shear_inverse_right : shear * shearInv = 1 := by
  ext i j
  change (∑ k : Fin 4, shear i k * shearInv k j) = (1 : Matrix (Fin 4) (Fin 4) ℚ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shear, shearInv, Fin.sum_univ_succ]

/- The expected column action is e1 |-> e1 + e0. -/
/--
@isnad1 id=eq.0h0v.s6.47b719f1a598 from=translated src=- shape=d94934c0 vocab=048c8272
-/
theorem shear_vector_witness :
    vecAct shear (uBasis 1) = uBasis 1 + uBasis 0 := by
  funext i
  fin_cases i <;>
    norm_num [shear, vecAct, uBasis, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/- The expected row-dual action is e0* |-> e0* - e1*. -/
/--
@isnad1 id=eq.0h0v.s6.cbd4fcc1eec6 from=translated src=- shape=d94934c0 vocab=630346a3
-/
theorem shear_covector_witness :
    covAct shearInv (uDualBasis 0) = uDualBasis 0 - uDualBasis 1 := by
  funext i
  fin_cases i <;>
    norm_num [shearInv, covAct, uDualBasis, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]

/- Direct coordinate evaluation, intentionally not an invocation of
evalU_covAct_vecAct. -/
/--
@isnad1 id=eq.0h0v.s6.477461b2727a from=translated src=- shape=36c19878 vocab=d17ad00b
-/
theorem shear_evaluation_witness :
    evalU (covAct shearInv (uDualBasis 0))
        (vecAct shear (uBasis 1)) =
      evalU (uDualBasis 0 : Udual ℚ) (uBasis 1) := by
  norm_num [shear, shearInv, covAct, vecAct, evalU, uBasis, uDualBasis,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> decide +kernel

end ConcreteConventionWitness

section DeterminantAndSigns

local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)

def scaleFirst : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![2, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

def mixedW : W ℚ := wBasis .i12 + wBasis .i34

/- This determinant computation makes clear that the witness is outside
SL4. -/
/--
@isnad1 id=eq.0h0v.s4.6832dbaf05a8 from=translated src=- shape=5ca0a7a0 vocab=86de77cc
-/
theorem scaleFirst_det : Matrix.det scaleFirst = 2 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [scaleFirst, Matrix.det_fin_three, Matrix.submatrix,
    Fin.sum_univ_succ, Fin.succAbove] <;> decide +kernel

/--
@isnad1 id=ne.0h0v.s4.0d484050517e from=translated src=- shape=5ca0a7a0 vocab=86de77cc
-/
theorem scaleFirst_not_det_one : Matrix.det scaleFirst ≠ 1 := by
  rw [scaleFirst_det]
  norm_num

/- Direct source-coordinate calculation: the Pfaffian multiplier is two,
so the determinant-one premise is semantically essential. -/
/--
@isnad1 id=eq.0h0v.s3.4ea102651bbf from=translated src=- shape=3701a056 vocab=3f95edc0
-/
theorem mixedW_pf_before : Pf mixedW = 1 := by
  norm_num [mixedW, Pf, BW, wBasis] <;> decide +kernel

/--
@isnad1 id=eq.0h0v.s4.cf50af67ccf8 from=translated src=- shape=0e11011f vocab=cbc2164a
-/
theorem mixedW_pf_after : Pf (wedgeAct scaleFirst mixedW) = 2 := by
  norm_num [mixedW, scaleFirst, wedgeAct, vecAct, Pf, BW, wedge2, wBasis,
    uBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> decide +kernel

/- Frozen complementary-basis signs.  These restate values, rather than
calling the imported basis lemmas, so a changed convention breaks the test. -/
/--
@isnad1 id=and.0h0v.s5.37961bf5569c from=translated src=- shape=881c6401 vocab=14c20862
-/
theorem complementary_BW_signs :
    BW (wBasis .i12 : W ℚ) (wBasis .i34) = 1 ∧
    BW (wBasis .i13 : W ℚ) (wBasis .i24) = -1 ∧
    BW (wBasis .i14 : W ℚ) (wBasis .i23) = 1 := by
  norm_num [BW, wBasis] <;> decide +kernel

end DeterminantAndSigns

end AlbertLean.Generic.ActionBridgeChecks
