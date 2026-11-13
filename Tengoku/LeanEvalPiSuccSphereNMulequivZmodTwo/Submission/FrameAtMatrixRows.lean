import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SOGramSchmidtSmooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Recovering the intrinsic frame from an explicit special-orthogonal right inverse

For an explicit framed level-set model it is often much easier to exhibit an
`SO(n+1)` row frame on which the differential is zero in the tangent row and
the identity in the remaining normal rows than to calculate gradients and the
generalized cross product separately.  This file packages that argument once.

If the rows of `Q : SO(n+1)` have those differential values, then the gradient
rows are literally the normal rows of `Q`; determinant one fixes the sign of
the generalized cross product, so the oriented kernel row is literally row
zero.  Consequently both `frameAt` and its normalized Gram--Schmidt matrix are
definitionally identified with the rows/matrix of `Q`.
-/

set_option autoImplicit false

noncomputable section

namespace Submission

open Set Function InnerProductSpace
open scoped RealInnerProductSpace Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F" => EuclideanSpace ℝ (Fin n)

/-- The rows of a special-orthogonal matrix, packaged as an orthonormal basis.-/
def matrixRowsONBasis (Q : SOGroup (n + 1)) :
    OrthonormalBasis (Fin (n + 1)) ℝ E :=
  OrthonormalBasis.mk
    (orthonormal_matrixRows_of_mem_orthogonalGroup
      (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1) <| by
    have hspan :=
      (orthonormal_matrixRows_of_mem_orthogonalGroup
        (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1).linearIndependent
        |>.span_eq_top_of_card_eq_finrank (by simp)
    exact hspan.ge

@[simp] theorem matrixRowsONBasis_apply (Q : SOGroup (n + 1))
    (i : Fin (n + 1)) :
    matrixRowsONBasis Q i =
      matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i := by
  simp [matrixRowsONBasis]

/-- For an `SO(n+1)` row frame, the generalized cross product of the final
`n` rows is exactly row zero.  The determinant-one condition fixes the sign.-/
theorem crossVec_matrixRows_succ (Q : SOGroup (n + 1)) :
    crossVec (fun i : Fin n =>
      matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ) =
      matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 := by
  let b := matrixRowsONBasis Q
  apply ext_inner_right_basis b.toBasis
  intro j
  change inner ℝ
      (crossVec (fun i : Fin n =>
        matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ))
      (b j) =
    inner ℝ
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0)
      (b j)
  rw [matrixRowsONBasis_apply]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [inner_crossVec]
    have hrows :
        crossRows
            (fun i : Fin n =>
              matrixRows
                (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ)
            (matrixRows
              (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0) =
          (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
      ext i k
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
        rfl
    rw [crossDet, hrows,
      (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2]
    have horth := orthonormal_matrixRows_of_mem_orthogonalGroup
      (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1
    rw [real_inner_self_eq_norm_sq, horth.1 0]
    norm_num
  · rw [inner_crossVec, crossDet_apply_self]
    have horth := orthonormal_matrixRows_of_mem_orthogonalGroup
      (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1
    simpa [show (0 : Fin (n + 1)) ≠ j.succ by
      exact (Fin.succ_ne_zero j).symm] using
      (orthonormal_iff_ite.mp horth (0 : Fin (n + 1)) j.succ).symm

/-- The normal gradient rows are recovered directly from the values of the
differential on an explicit orthonormal row frame.-/
theorem gradVec_eq_matrixRows_succ_of_rightInverse
    (X : FramedLevelSet n) (x : E) (Q : SOGroup (n + 1))
    (htangent : fderiv ℝ X.g x
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0) = 0)
    (hnormal : ∀ i : Fin n, fderiv ℝ X.g x
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ) =
        EuclideanSpace.single i 1)
    (i : Fin n) :
    gradVec X.g i x =
      matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ := by
  let b := matrixRowsONBasis Q
  apply ext_inner_right_basis b.toBasis
  intro j
  change inner ℝ (gradVec X.g i x) (b j) =
    inner ℝ
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ)
      (b j)
  rw [matrixRowsONBasis_apply]
  have horth := orthonormal_matrixRows_of_mem_orthogonalGroup
    (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [inner_gradVec, htangent]
    simpa using
      (orthonormal_iff_ite.mp horth i.succ (0 : Fin (n + 1))).symm
  · rw [inner_gradVec, hnormal j]
    have hq := orthonormal_iff_ite.mp horth i.succ j.succ
    simpa [PiLp.single_apply, eq_comm] using hq

/-- A differential which is zero on row zero and the identity on the remaining
rows has exactly the explicit `SO` row frame as its intrinsic oriented frame.-/
theorem frameAt_eq_matrixRows_of_SO_rightInverse
    (X : FramedLevelSet n) (x : E) (Q : SOGroup (n + 1))
    (htangent : fderiv ℝ X.g x
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0) = 0)
    (hnormal : ∀ i : Fin n, fderiv ℝ X.g x
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ) =
        EuclideanSpace.single i 1) :
    frameAt X x =
      matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  have hgrad : (fun i : Fin n => gradVec X.g i x) =
      fun i : Fin n =>
        matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ := by
    funext i
    exact gradVec_eq_matrixRows_succ_of_rightInverse X x Q htangent hnormal i
  have horth := orthonormal_matrixRows_of_mem_orthogonalGroup
    (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · change tauField X.g x = _
    rw [tauField, kerCross, hgrad, crossVec_matrixRows_succ Q,
      horth.1 0, inv_one, one_smul]
  · change gradVec X.g j x = _
    exact gradVec_eq_matrixRows_succ_of_rightInverse X x Q htangent hnormal j

/-- The normalized Gram--Schmidt matrix therefore recovers the original
special-orthogonal matrix literally.-/
theorem frameMatrix_eq_of_SO_rightInverse
    (X : FramedLevelSet n) (x : E) (Q : SOGroup (n + 1))
    (htangent : fderiv ℝ X.g x
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0) = 0)
    (hnormal : ∀ i : Fin n, fderiv ℝ X.g x
      (matrixRows (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ) =
        EuclideanSpace.single i 1) :
    rowsMatrix (gramSchmidtNormed ℝ (frameAt X x)) =
      (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  rw [frameAt_eq_matrixRows_of_SO_rightInverse X x Q htangent hnormal]
  have horth := orthonormal_matrixRows_of_mem_orthogonalGroup
    (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1
  rw [gramSchmidtNormed_eq_of_orthonormal horth,
    rowsMatrix_matrixRows]

end Submission
