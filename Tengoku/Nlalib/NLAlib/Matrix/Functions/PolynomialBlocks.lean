import Tengoku.Nlalib.NLAlib.Matrix.Functions.PolynomialIntertwining
import Tengoku.Seed.LinearAlgebra.Matrix.SchurComplement
import Tengoku.Seed.Data.Matrix.ColumnRowPartitioned

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial triangular block differences

Finite insertion sums compute polynomial evaluation on triangular matrices.
Source: matrix-toolkit derivations, F16--F18; helpers for
`matrix-function-block-divided-differences`.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {𝕜 m n o : Type*} [CommRing 𝕜]
variable [Fintype m] [Fintype n] [Fintype o]
variable [DecidableEq m] [DecidableEq n] [DecidableEq o]

/-- The upper triangular two-block matrix.-/
def upperBlockTwo (A : Matrix m m 𝕜) (H : Matrix m n 𝕜) (B : Matrix n n 𝕜) :=
  Matrix.fromBlocks A H 0 B

/-- The finite one-insertion sum for a monomial.-/
def monomialBlockDifference (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  ∑ j ∈ Finset.range k, A ^ (k.pred - j) * H * B ^ j

/--
@isnad1 id=eq.0h7v.s7.642568b56515 from=translated src=- shape=3e487f99 vocab=16d0444f
-/
theorem monomialBlockDifference_succ (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) (k : ℕ) :
    monomialBlockDifference A B H (k + 1) =
      A ^ k * H + monomialBlockDifference A B H k * B := by
  simp only [monomialBlockDifference, Nat.pred_succ]
  rw [Finset.sum_range_succ', add_comm]
  simp only [tsub_zero, pow_zero, Matrix.mul_one, Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have he : k - (j + 1) = k.pred - j := by
    simp [Nat.pred_eq_sub_one, Nat.sub_sub, Nat.add_comm]
  rw [he, pow_succ]
  simp only [Matrix.mul_assoc]

/-- Actual powers of triangular matrices have the insertion sum as their upper block.
@isnad1 id=eq.0h7v.s8.9b5047bb53a8 from=translated src=- shape=f880fa1c vocab=380c124b
-/
theorem upperBlockTwo_pow (A : Matrix m m 𝕜) (H : Matrix m n 𝕜)
    (B : Matrix n n 𝕜) (k : ℕ) :
    upperBlockTwo A H B ^ k =
      Matrix.fromBlocks (A ^ k) (monomialBlockDifference A B H k) 0 (B ^ k) := by
  induction k with
  | zero => simp [upperBlockTwo, monomialBlockDifference, Matrix.fromBlocks_one]
  | succ k hk =>
    rw [pow_succ, hk, upperBlockTwo, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← pow_succ,
      monomialBlockDifference_succ]

/-- The first polynomial block difference, written as a finite insertion sum.-/
def polynomialBlockDifference (p : 𝕜[X]) (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • monomialBlockDifference A B H k

/-- Polynomial evaluation on an actual triangular matrix.
@isnad1 id=eq.0h7v.s9.b6eb2d0b662b from=translated src=- shape=6a6c3c4e vocab=5d8ab886
-/
theorem aeval_upperBlockTwo (p : 𝕜[X]) (A : Matrix m m 𝕜) (H : Matrix m n 𝕜)
    (B : Matrix n n 𝕜) :
    aeval (upperBlockTwo A H B) p =
      Matrix.fromBlocks (aeval A p) (polynomialBlockDifference p A B H) 0 (aeval B p) := by
  simp only [aeval_eq_sum_range, upperBlockTwo_pow, polynomialBlockDifference]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.sum_apply, Matrix.smul_apply]

/-- The ordered second polynomial difference: two insertions in their given order.-/
def polynomialSecondBlockDifference (p : 𝕜[X]) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) (C : Matrix o o 𝕜) (G : Matrix m n 𝕜) (H : Matrix n o 𝕜) :
    Matrix m o 𝕜 :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k, monomialBlockDifference A B G (k.pred - j) * H * C ^ j

/-- A three-block triangular matrix with a zero direct first-to-third block.-/
def upperBlockThree (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) : Matrix ((m ⊕ n) ⊕ o) ((m ⊕ n) ⊕ o) 𝕜 :=
  upperBlockTwo (upperBlockTwo A G B) (Matrix.fromRows 0 H) C

/--
@isnad1 id=eq.0h10v.s7.207ac8bcf72a from=translated src=- shape=fb495fe2 vocab=b56faf5c
-/
theorem polynomialBlockDifference_upperBlockTwo (p : 𝕜[X])
    (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) :
    polynomialBlockDifference p (upperBlockTwo A G B) C (Matrix.fromRows 0 H) =
      Matrix.fromRows (polynomialSecondBlockDifference p A B C G H)
        (polynomialBlockDifference p B C H) := by
  simp only [polynomialBlockDifference, monomialBlockDifference, upperBlockTwo_pow,
    Matrix.fromBlocks_mul_fromRows, Matrix.mul_zero, zero_add,
    Matrix.fromRows_mul]
  ext i j
  rcases i with i | i <;>
    simp only [polynomialSecondBlockDifference, monomialBlockDifference,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, smul_eq_mul]

/-- The ordered second difference is the actual first-to-third block of the
polynomial of a three-block triangular matrix.
@isnad1 id=eq.0h10v.s10.afb596413861 from=translated src=- shape=fd793800 vocab=3c0b512a
-/
theorem aeval_upperBlockThree (p : 𝕜[X])
    (A : Matrix m m 𝕜) (G : Matrix m n 𝕜) (B : Matrix n n 𝕜)
    (H : Matrix n o 𝕜) (C : Matrix o o 𝕜) :
    aeval (upperBlockThree A G B H C) p =
      Matrix.fromBlocks
        (Matrix.fromBlocks (aeval A p) (polynomialBlockDifference p A B G) 0 (aeval B p))
        (Matrix.fromRows (polynomialSecondBlockDifference p A B C G H)
          (polynomialBlockDifference p B C H)) 0 (aeval C p) := by
  simp only [upperBlockThree, aeval_upperBlockTwo, polynomialBlockDifference_upperBlockTwo]

end NLAlib
