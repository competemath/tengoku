import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.Preparation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.SwapNaturality

open S3xS3.Naturality

def swapMatrix : Mat6 := Matrix.fromBlocks 0 1 1 0

def swapVec (x : LieVec) : LieVec
  | Sum.inl i => x (Sum.inr i)
  | Sum.inr i => x (Sum.inl i)

@[simp] lemma swapVec_inl (x : LieVec) (i : I3) :
    swapVec x (Sum.inl i) = x (Sum.inr i) := rfl

@[simp] lemma swapVec_inr (x : LieVec) (i : I3) :
    swapVec x (Sum.inr i) = x (Sum.inl i) := rfl

lemma swapMatrix_transpose : swapMatrixᵀ = swapMatrix := by
  rw [swapMatrix, Matrix.fromBlocks_transpose]
  simp

lemma swapMatrix_sq : swapMatrix * swapMatrix = 1 := by
  rw [swapMatrix, Matrix.fromBlocks_multiply]
  simp

lemma swapMatrix_mul_transpose : swapMatrix * swapMatrixᵀ = 1 := by
  rw [swapMatrix_transpose, swapMatrix_sq]

lemma swapVec_involutive (x : LieVec) : swapVec (swapVec x) = x := by
  funext i
  cases i <;> rfl

lemma bracket_swapVec (x y : LieVec) :
    bracket (swapVec x) (swapVec y) = swapVec (bracket x y) := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, swapVec, cross_apply]

noncomputable def swapMetric (g : LeftInvariantMetric) : LeftInvariantMetric where
  gram := swapMatrixᵀ * g.gram * swapMatrix
  posDef := by
    have hunit : IsUnit swapMatrix :=
      IsUnit.of_mul_eq_one swapMatrixᵀ swapMatrix_mul_transpose
    have hinj : Function.Injective swapMatrix.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hunit
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      g.posDef.conjTranspose_mul_mul_same hinj

lemma swapMetric_gram (g : LeftInvariantMetric) :
    (swapMetric g).gram = swapMatrixᵀ * g.gram * swapMatrix := rfl

lemma swapMetric_gram_inv (g : LeftInvariantMetric) :
    (swapMetric g).gram⁻¹ = swapMatrixᵀ * g.gram⁻¹ * swapMatrix := by
  have hJinv : swapMatrix⁻¹ = swapMatrix :=
    Matrix.inv_eq_right_inv swapMatrix_sq
  rw [swapMetric_gram, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    swapMatrix_transpose, hJinv]
  noncomm_ring

lemma swapVec_sub (x y : LieVec) : swapVec (x - y) = swapVec x - swapVec y := by
  funext i
  cases i <;> rfl

lemma swapVec_basis (i : I6) :
    swapVec (basisVec i) = basisVec (Sum.swap i) := by
  funext j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [swapVec, basisVec]

def swapAction (a : InnerAction) : InnerAction := (a.2, a.1)

end S3xS3.Trivial.SwapNaturality
