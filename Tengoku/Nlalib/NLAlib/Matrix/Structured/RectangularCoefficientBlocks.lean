import Tengoku.Nlalib.NLAlib.Matrix.Norms.Reindex
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SpectralBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Row, column, and entry blocks of rectangular coefficient families

These are ordinary finite matrices. Their Gram matrices are exactly the row,
column, and entry covariances used by linear matrix-series estimates and by
the finite-array recursion for matrix chaos.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {ι m n 𝕜 : Type*}

/-- Put a coefficient label next to the matrix column label.-/
def coefficientRow (A : ι → Matrix m n 𝕜) : Matrix m (ι × n) 𝕜 :=
  fun a jb => A jb.1 a jb.2

/-- Put a coefficient label next to the matrix row label.-/
def coefficientColumn (A : ι → Matrix m n 𝕜) : Matrix (ι × m) n 𝕜 :=
  fun ia b => A ia.1 ia.2 b

/-- Put each vectorized coefficient in a row. Both original matrix labels
are on the column side; no coordinate appears on both sides.-/
def coefficientEntryRows (A : ι → Matrix m n 𝕜) : Matrix ι (m × n) 𝕜 :=
  fun i ab => A i ab.1 ab.2

variable [Fintype ι] [Fintype m] [Fintype n] [RCLike 𝕜]

/-- The horizontal block Gram matrix is the sum of row variances.
@isnad1 id=eq.0h5v.s8.4e8d9404e1ee from=translated src=- shape=58ee69a4 vocab=84e1542c
-/
theorem coefficientRow_mul_conjTranspose (A : ι → Matrix m n 𝕜) :
    coefficientRow A * (coefficientRow A)ᴴ = ∑ i, A i * (A i)ᴴ := by
  ext a b
  simp [coefficientRow, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]

/-- The vertical block Gram matrix is the sum of column variances.
@isnad1 id=eq.0h5v.s8.f78556c13299 from=translated src=- shape=9fbccfcb vocab=24cc352d
-/
theorem coefficientColumn_conjTranspose_mul (A : ι → Matrix m n 𝕜) :
    (coefficientColumn A)ᴴ * coefficientColumn A = ∑ i, (A i)ᴴ * A i := by
  ext a b
  simp [coefficientColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]

variable [DecidableEq ι] [DecidableEq m] [DecidableEq n]

/-- The horizontal block norm is the square root of the row-variance norm.
Source: finite block multiplication.
atlas: matrix-chaos-flattenings-def (partial)
@isnad1 id=eq.0h5v.s7.75d2f5417c29 from=translated src=- shape=28d318e7 vocab=950659a3
-/
theorem specNorm_coefficientRow_sq (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientRow A) ^ 2 = specNorm (∑ i, A i * (A i)ᴴ) := by
  rw [← specNorm_mul_conjTranspose_self, coefficientRow_mul_conjTranspose]

/-- The vertical block norm is the square root of the column-variance norm.
Source: finite block multiplication.
atlas: matrix-chaos-flattenings-def (partial)
@isnad1 id=eq.0h5v.s7.ff7f3bb6eeab from=translated src=- shape=29ca1608 vocab=24ed41f1
-/
theorem specNorm_coefficientColumn_sq (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientColumn A) ^ 2 = specNorm (∑ i, (A i)ᴴ * A i) := by
  rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self, coefficientColumn_conjTranspose_mul]

/-- The row block norm equals the square root of the row-variance norm.
@isnad1 id=eq.0h5v.s7.0537acc2f606 from=translated src=- shape=f16aeaab vocab=b983ecfa
-/
theorem specNorm_coefficientRow (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientRow A) = Real.sqrt (specNorm (∑ i, A i * (A i)ᴴ)) := by
  rw [← specNorm_coefficientRow_sq, Real.sqrt_sq (specNorm_nonneg _)]

/-- The column block norm equals the square root of the column-variance norm.
@isnad1 id=eq.0h5v.s7.15ae6637b142 from=translated src=- shape=99244237 vocab=0809641c
-/
theorem specNorm_coefficientColumn (A : ι → Matrix m n 𝕜) :
    specNorm (coefficientColumn A) = Real.sqrt (specNorm (∑ i, (A i)ᴴ * A i)) := by
  rw [← specNorm_coefficientColumn_sq, Real.sqrt_sq (specNorm_nonneg _)]

end NLAlib
