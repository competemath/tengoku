import Tengoku.Nlalib.NLAlib.Matrix.Basic.Orthonormal
import Tengoku.Seed.Data.Complex.BigOperators
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Block
import Tengoku.Seed.LinearAlgebra.Matrix.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Realification of complex matrices

The real matrix of a complex-linear map in real and imaginary coordinates is
`[[Re A,-Im A],[Im A,Re A]]`. This construction preserves multiplication and
adjoints and doubles the real trace. It supports transporting real Schatten
inequalities and orthogonal Gaussian invariance to complex matrices.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n p : Type*}

/-- The real matrix of a complex matrix acting on real and imaginary parts.-/
def matrixRealification (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (fun i j => (A i j).re) (fun i j => -(A i j).im)
    (fun i j => (A i j).im) (fun i j => (A i j).re)

/-- Realification preserves addition.
@isnad1 id=eq.0h4v.s6.66f14fdd5b25 from=translated src=- shape=7fa00c50 vocab=cc42caca
-/
@[simp] theorem matrixRealification_add (A B : Matrix m n ℂ) :
    matrixRealification (A+B) = matrixRealification A + matrixRealification B := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm]

/-- Realification sends zero to zero.
@isnad1 id=eq.0h2v.s5.bbf572bbb6ab from=translated src=- shape=84dcfed4 vocab=35ae5c2a
-/
@[simp] theorem matrixRealification_zero : matrixRealification (0 : Matrix m n ℂ) = 0 := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm]

/-- Realification preserves negation.
@isnad1 id=eq.0h3v.s5.dbd66d9e84df from=translated src=- shape=fb6d492d vocab=d81159f6
-/
@[simp] theorem matrixRealification_neg (A : Matrix m n ℂ) :
    matrixRealification (-A) = -matrixRealification A := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm]

/-- Realification preserves subtraction.
@isnad1 id=eq.0h4v.s6.a71f823f488c from=translated src=- shape=7fa00c50 vocab=a3bfaca2
-/
@[simp] theorem matrixRealification_sub (A B : Matrix m n ℂ) :
    matrixRealification (A-B) = matrixRealification A - matrixRealification B := by
  rw [sub_eq_add_neg,matrixRealification_add,matrixRealification_neg,←sub_eq_add_neg]

/-- Realification commutes with real scalar multiplication.
@isnad1 id=eq.0h4v.s6.15adabc646ed from=translated src=- shape=b42196bc vocab=2c8afdd3
-/
@[simp] theorem matrixRealification_smul (r : ℝ) (A : Matrix m n ℂ) :
    matrixRealification (r • A) = r • matrixRealification A := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, add_comm] <;> ring

/-- Realification sends the complex identity matrix to the real identity.
@isnad1 id=eq.0h1v.s6.ebd70324aded from=translated src=- shape=26de6651 vocab=cb0a0dde
-/
@[simp] theorem matrixRealification_one [DecidableEq n] :
    matrixRealification (1 : Matrix n n ℂ) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, Matrix.one_apply, apply_ite]

/-- The real matrix of a product is the product of the real matrices.
@isnad1 id=eq.0h5v.s6.6690663c44b3 from=translated src=- shape=2c6718f2 vocab=191af6d7
-/
@[simp] theorem matrixRealification_mul [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    matrixRealification (A*B) = matrixRealification A * matrixRealification B := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, matrixRealification, Matrix.mul_apply, Fintype.sum_sum_type,
      Complex.mul_re, Complex.mul_im, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, mul_neg, neg_mul, add_comm, sub_eq_add_neg]

/-- The complex adjoint becomes real transposition under realification.
@isnad1 id=eq.0h3v.s5.08ac4ea4f308 from=translated src=- shape=849d105f vocab=6cc1d40b
-/
@[simp] theorem matrixRealification_conjTranspose (A : Matrix m n ℂ) :
    matrixRealification Aᴴ = (matrixRealification A)ᵀ := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, matrixRealification, Matrix.conjTranspose_apply]

/-- A unitary matrix realifies to a real matrix with orthonormal columns.
@isnad1 id=hasortho.1h3v.s5.2a661788a241 from=translated src=- shape=eebfe0cb vocab=d94620bf
-/
theorem HasOrthonormalCols.realification [Fintype m] [DecidableEq n]
    {A : Matrix m n ℂ} (hA : HasOrthonormalCols A) :
    HasOrthonormalCols (matrixRealification A) := by
  change (matrixRealification A)ᴴ * matrixRealification A = 1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,←matrixRealification_conjTranspose,
    ←matrixRealification_mul,hA.conjTranspose_mul_self,matrixRealification_one]

/-- The real trace of a realification is twice the real part of the complex
trace, including the zero-dimensional case.
@isnad1 id=eq.0h2v.s5.9766a7e780b8 from=translated src=- shape=2f711b76 vocab=5845ebae
-/
theorem trace_matrixRealification [Fintype n] (A : Matrix n n ℂ) :
    (matrixRealification A).trace = 2 * A.trace.re := by
  simp [Matrix.fromBlocks, matrixRealification, Matrix.trace, Fintype.sum_sum_type, map_sum]
  ring

/-- Realification commutes with simultaneous relabeling of the two coordinate
copies on each side.
@isnad1 id=eq.0h7v.s7.b6e70bbb83cf from=translated src=- shape=4e3ab043 vocab=c6c7ad88
-/
theorem matrixRealification_reindex {r s : Type*} (A : Matrix m n ℂ)
    (em : m ≃ r) (en : n ≃ s) :
    matrixRealification (A.reindex em en) =
      (matrixRealification A).reindex (Equiv.sumCongr em em) (Equiv.sumCongr en en) := by
  ext i j
  cases i <;> cases j <;> simp [matrixRealification, Matrix.fromBlocks, Matrix.reindex_apply]

/-- Realification of a real diagonal is the diagonal with every real entry
repeated on its real and imaginary coordinate copies.
@isnad1 id=eq.0h2v.s5.a8d328846935 from=translated src=- shape=1b9b011e vocab=6079e901
-/
theorem matrixRealification_diagonal_ofReal [DecidableEq n] (d : n → ℝ) :
    matrixRealification (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (Sum.elim d d) := by
  ext i j
  cases i <;> cases j <;>
    simp [matrixRealification, Matrix.fromBlocks, Matrix.diagonal_apply, apply_ite] <;>
      split_ifs <;> simp_all

end NLAlib
