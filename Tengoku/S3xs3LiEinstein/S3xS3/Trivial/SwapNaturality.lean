import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.Preparation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.SwapNaturality

open S3xS3.Naturality

def swapMatrix : Mat6 := Matrix.fromBlocks 0 1 1 0

def swapVec (x : LieVec) : LieVec
  | Sum.inl i => x (Sum.inr i)
  | Sum.inr i => x (Sum.inl i)

/--
@isnad1 id=eq.0h2v.s4.b812498be5ff from=translated src=- shape=b40807c2 vocab=4368249c
-/
@[simp] lemma swapVec_inl (x : LieVec) (i : I3) :
    swapVec x (Sum.inl i) = x (Sum.inr i) := rfl

/--
@isnad1 id=eq.0h2v.s4.00fb289b7694 from=translated src=- shape=b40807c2 vocab=4368249c
-/
@[simp] lemma swapVec_inr (x : LieVec) (i : I3) :
    swapVec x (Sum.inr i) = x (Sum.inl i) := rfl

/--
@isnad1 id=eq.0h0v.s3.6309d78d5a76 from=translated src=- shape=a7fa1216 vocab=a1741a64
-/
lemma swapMatrix_transpose : swapMatrixᵀ = swapMatrix := by
  rw [swapMatrix, Matrix.fromBlocks_transpose]
  simp

/--
@isnad1 id=eq.0h0v.s6.f9bf3460bcd1 from=translated src=- shape=a44de0d1 vocab=d46eb0b2
-/
lemma swapMatrix_sq : swapMatrix * swapMatrix = 1 := by
  rw [swapMatrix, Matrix.fromBlocks_multiply]
  simp

/--
@isnad1 id=eq.0h0v.s6.a7bd5f7cf87c from=translated src=- shape=492dcbd1 vocab=2535c3bf
-/
lemma swapMatrix_mul_transpose : swapMatrix * swapMatrixᵀ = 1 := by
  rw [swapMatrix_transpose, swapMatrix_sq]

/--
@isnad1 id=eq.0h1v.s3.8a776a413d78 from=translated src=- shape=47dcad53 vocab=d7228740
-/
lemma swapVec_involutive (x : LieVec) : swapVec (swapVec x) = x := by
  funext i
  cases i <;> rfl

/--
@isnad1 id=eq.0h2v.s3.230532788782 from=translated src=- shape=f246b22a vocab=e7fa5d04
-/
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

/--
@isnad1 id=eq.0h1v.s6.d0059888a234 from=translated src=- shape=18cba883 vocab=91c46a51
-/
lemma swapMetric_gram (g : LeftInvariantMetric) :
    (swapMetric g).gram = swapMatrixᵀ * g.gram * swapMatrix := rfl

/--
@isnad1 id=eq.0h1v.s7.d13b258f31a0 from=translated src=- shape=36bb86cb vocab=d53b1d39
-/
lemma swapMetric_gram_inv (g : LeftInvariantMetric) :
    (swapMetric g).gram⁻¹ = swapMatrixᵀ * g.gram⁻¹ * swapMatrix := by
  have hJinv : swapMatrix⁻¹ = swapMatrix :=
    Matrix.inv_eq_right_inv swapMatrix_sq
  rw [swapMetric_gram, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    swapMatrix_transpose, hJinv]
  noncomm_ring

/--
@isnad1 id=eq.0h2v.s5.01e90ae43a41 from=translated src=- shape=a13ca989 vocab=8f97d088
-/
lemma swapVec_sub (x y : LieVec) : swapVec (x - y) = swapVec x - swapVec y := by
  funext i
  cases i <;> rfl

/--
@isnad1 id=eq.0h1v.s3.0bb6b9db4a1b from=translated src=- shape=217f319e vocab=e963107f
-/
lemma swapVec_basis (i : I6) :
    swapVec (basisVec i) = basisVec (Sum.swap i) := by
  funext j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [swapVec, basisVec]

def swapAction (a : InnerAction) : InnerAction := (a.2, a.1)

end S3xS3.Trivial.SwapNaturality
