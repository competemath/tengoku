import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.CStarAlgebra.CStarMatrixBlockSpectra
import Tengoku.Nlalib.NLAlib.Matrix.Basic.Dilation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Actual rectangular dilation spectra over arbitrary C*-algebras

Native C*-matrix spectra retain the full possibly continuous free spectrum.
The nonzero row and column Gram spectra agree by the genuine ambient
product-spectrum identity, rather than a finite eigenvalue enumeration.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace CStarMatrix
variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A]

/-- The actual native C*-matrix adapter of the ordinary rectangular
Hermitian dilation, with the same literal entries.-/
def rectangularDilation (Y : Matrix m n A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  ofMatrix (NLAlib.dilation Y)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The native rectangular dilation is actually self-adjoint.
@isnad1 id=isselfad.0h4v.s6.9ede56f0cfe2 from=translated src=- shape=70b25c98 vocab=570b95ee
-/
theorem isSelfAdjoint_rectangularDilation (Y : Matrix m n A) :
    IsSelfAdjoint (rectangularDilation Y) := by
  change (NLAlib.dilation Y).IsHermitian
  exact NLAlib.isHermitian_dilation Y

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The literal row Gram matrix is actually self-adjoint in its native
C*-matrix algebra, including empty shapes.
@isnad1 id=isselfad.0h4v.s7.8d0fd352c2ee from=translated src=- shape=9e8156ce vocab=64d77bcc
-/
theorem isSelfAdjoint_rowGram (Y : Matrix m n A) :
    IsSelfAdjoint (ofMatrix (Y * Yᴴ)) := by
  change (Y * Yᴴ)ᴴ = Y * Yᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The literal column Gram matrix is actually self-adjoint.
@isnad1 id=isselfad.0h4v.s7.d0ca6bac3888 from=translated src=- shape=d5f1f225 vocab=64d77bcc
-/
theorem isSelfAdjoint_columnGram (Y : Matrix m n A) :
    IsSelfAdjoint (ofMatrix (Yᴴ * Y)) := by
  change (Yᴴ * Y)ᴴ = Yᴴ * Y
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Squaring the actual native dilation gives the literal two Gram blocks.
@isnad1 id=eq.0h4v.s10.a860a98639d2 from=translated src=- shape=5dee8822 vocab=ec8a4c52
-/
theorem rectangularDilation_sq (Y : Matrix m n A) :
    rectangularDilation Y ^ 2 =
      blockDiagonalStarAlgHom (ofMatrix (Y * Yᴴ), ofMatrix (Yᴴ * Y)) := by
  change (NLAlib.dilation Y) ^ 2 = Matrix.fromBlocks (Y * Yᴴ) 0 0 (Yᴴ * Y)
  simp only [NLAlib.dilation, pow_two, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]

end CStarMatrix
