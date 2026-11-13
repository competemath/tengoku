import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SpectralBounds
import Tengoku.Seed.Data.Matrix.ColumnRowPartitioned

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spectral and Frobenius bounds for matrix blocks

Squared horizontal/vertical norm bounds and the upper-block residual estimate
needed for the exact strong RRQR constants. Horn–Johnson 2013, Section 5.6;
Gu–Eisenstat 1996, Theorem 3.2.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Concatenating column blocks bounds the squared operator norm by the sum
of squared block norms. Horn–Johnson 2013, Section 5.6.
@isnad1 id=le.0h5v.s7.4de5c3e20338 from=translated src=- shape=fa550846 vocab=2e1e04bc
-/
theorem specNorm_fromCols_sq_le {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℝ) (B : Matrix m p ℝ) :
    specNorm (Matrix.fromCols A B) ^ 2 ≤ specNorm A ^ 2 + specNorm B ^ 2 := by
  rw [← specNorm_mul_conjTranspose_self, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows,
    ← specNorm_mul_conjTranspose_self A, ← specNorm_mul_conjTranspose_self B,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact specNorm_add_le _ _

/-- Concatenating row blocks bounds the squared operator norm by the sum
of squared block norms. Horn–Johnson 2013, Section 5.6.
@isnad1 id=le.0h5v.s7.c9de5ea10bde from=translated src=- shape=9896b484 vocab=9ab26a88
-/
theorem specNorm_fromRows_sq_le {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix m p ℝ) (B : Matrix n p ℝ) :
    specNorm (Matrix.fromRows A B) ^ 2 ≤ specNorm A ^ 2 + specNorm B ^ 2 := by
  have h := specNorm_fromCols_sq_le Aᵀ Bᵀ
  rw [← Matrix.transpose_fromRows, specNorm_transpose, specNorm_transpose,
    specNorm_transpose] at h
  exact h

/-- Appending zero rows leaves the squared spectral norm unchanged.
Horn–Johnson 2013, Section 5.6; includes empty dimensions.
@isnad1 id=eq.0h4v.s6.c832d0cbcb81 from=translated src=- shape=e08da5e4 vocab=5622f3bc
-/
theorem specNorm_fromRows_zero_sq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix m p ℝ) :
    specNorm (Matrix.fromRows A (0 : Matrix n p ℝ)) ^ 2 = specNorm A ^ 2 := by
  rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, Matrix.transpose_zero,
    Matrix.zero_mul, add_zero, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    ← specNorm_sq_eq_specNorm_conjTranspose_mul_self]

/-- The Frobenius square of vertical blocks is the sum of their squares.
Horn–Johnson 2013, Section 5.6.
@isnad1 id=eq.0h5v.s6.d63872215270 from=translated src=- shape=1f7d2d26 vocab=982986d7
-/
theorem frobSq_fromRows {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m p ℝ) (B : Matrix n p ℝ) :
    frobSq (Matrix.fromRows A B) = frobSq A + frobSq B := by
  simp only [frobSq_eq_sum_sq, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr]

/-- The Frobenius square of horizontal blocks is the sum of their squares.
Horn–Johnson 2013, Section 5.6.
@isnad1 id=eq.0h5v.s6.7f7753fbd951 from=translated src=- shape=c2568f10 vocab=bae29fd4
-/
theorem frobSq_fromCols {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n ℝ) (B : Matrix m p ℝ) :
    frobSq (Matrix.fromCols A B) = frobSq A + frobSq B := by
  rw [← frobSq_transpose, Matrix.transpose_fromCols, frobSq_fromRows,
    frobSq_transpose, frobSq_transpose]

/-- An upper-block residual has squared spectral norm at most
`‖F‖₂²(1+‖T‖F²)+‖D‖F²`. This keeps the shared RRQR budget intact.
Gu–Eisenstat 1996, Theorem 3.2; derivations §alg:rrqr.
@isnad1 id=le.0h6v.s7.3314dae92aa9 from=translated src=- shape=a50fd2f8 vocab=948be87a
-/
theorem specNorm_upper_block_sq_le {p q r : Type*}
    [Fintype p] [Fintype q] [Fintype r] [DecidableEq p] [DecidableEq q] [DecidableEq r]
    (F : Matrix p p ℝ) (T : Matrix p q ℝ) (D : Matrix r q ℝ) :
    specNorm (Matrix.fromBlocks F (F * T) 0 D) ^ 2 ≤
      specNorm F ^ 2 * (1 + frobSq T) + frobSq D := by
  have h := specNorm_fromCols_sq_le
    (Matrix.fromRows F (0 : Matrix r p ℝ)) (Matrix.fromRows (F * T) D)
  rw [Matrix.fromCols_fromRows_eq_fromBlocks, specNorm_fromRows_zero_sq] at h
  have hF := specNorm_sq_le_frobSq (Matrix.fromRows (F * T) D)
  rw [frobSq_fromRows] at hF
  have hFT := frobSq_mul_le_specNorm_sq_mul_frobSq F T
  nlinarith

end NLAlib
