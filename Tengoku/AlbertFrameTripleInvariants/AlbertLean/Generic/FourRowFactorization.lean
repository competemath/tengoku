import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Basic
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFactorization.quadraticPolynomial_eq_charpoly_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFactorization.quadraticPolynomial_eval_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFactorization.quadraticPolynomial_eval_neg_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFactorization.complementary_charpoly_endpoints` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Direct quadratic-matrix factorization

This module factors the matrix polynomial attached to a solution of
`X² + XU + V = 0` directly into two characteristic matrices.  No companion
matrix or coordinate expansion is used.
-/

noncomputable section

namespace AlbertLean.Generic.FourRowFactorization

open Polynomial

section AbstractRing

variable {A : Type*} [Ring A]

/-- The ordered noncommutative factorization behind the characteristic
polynomial argument.  Only the displayed commutation with `r` is needed.-/
theorem quadratic_factor_of_right_quadratic
    (r X U V : A) (hrX : r * X = X * r)
    (hquad : X ^ 2 + X * U + V = 0) :
    (r - X) * (r + U + X) = r ^ 2 + r * U + V := by
  rw [← sub_eq_zero]
  calc
    (r - X) * (r + U + X) - (r ^ 2 + r * U + V) =
        -(X ^ 2 + X * U + V) + (r * X - X * r) := by
      simp only [pow_two, mul_add, sub_mul]
      abel
    _ = 0 := by rw [hquad, hrX, neg_zero, sub_self, zero_add]

end AbstractRing

section PolynomialMatrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The polynomial matrix `z²I + zU + V`.-/
def quadraticMatrix (U V : Matrix n n R) : Matrix n n R[X] :=
  let z := Matrix.scalar n (X : R[X])
  let cMat : Matrix n n R →+* Matrix n n R[X] :=
    (C : R →+* R[X]).mapMatrix
  z ^ 2 + z * cMat U + cMat V

/-- The determinant polynomial `det(z²I + zU + V)`.-/
def quadraticPolynomial (U V : Matrix n n R) : R[X] :=
  (quadraticMatrix U V).det

/-- A right-quadratic solution factors its polynomial matrix into the
characteristic matrices of `X` and its complement `-U-X`.-/
theorem quadraticMatrix_eq_charmatrix_mul_charmatrix
    (X U V : Matrix n n R)
    (hquad : X ^ 2 + X * U + V = 0) :
    quadraticMatrix U V =
      Matrix.charmatrix X * Matrix.charmatrix (-U - X) := by
  let z := Matrix.scalar n (Polynomial.X : R[X])
  let cMat : Matrix n n R →+* Matrix n n R[X] :=
    (Polynomial.C : R →+* R[X]).mapMatrix
  have hquadC : cMat X ^ 2 + cMat X * cMat U + cMat V = 0 := by
    calc
      cMat X ^ 2 + cMat X * cMat U + cMat V =
          cMat (X ^ 2 + X * U + V) := by
        simp only [map_add, map_mul, map_pow]
      _ = cMat 0 := congrArg cMat hquad
      _ = 0 := map_zero cMat
  have hzX : z * cMat X = cMat X * z := by
    exact Matrix.scalar_commute _ (fun _ ↦ Commute.all _ _) _
  have hfactor :=
    quadratic_factor_of_right_quadratic z (cMat X) (cMat U) (cMat V) hzX hquadC
  have hcomplement : z + cMat U + cMat X = z - cMat (-U - X) := by
    rw [map_sub, map_neg]
    abel
  change z ^ 2 + z * cMat U + cMat V =
    (z - cMat X) * (z - cMat (-U - X))
  rw [← hcomplement]
  exact hfactor.symm

/-- Determinant multiplicativity turns the direct matrix factorization into
the desired product of characteristic polynomials.-/
theorem quadraticPolynomial_eq_charpoly_mul
    (X U V : Matrix n n R)
    (hquad : X ^ 2 + X * U + V = 0) :
    quadraticPolynomial U V = X.charpoly * (-U - X).charpoly := by
  rw [quadraticPolynomial,
    quadraticMatrix_eq_charmatrix_mul_charmatrix X U V hquad,
    Matrix.det_mul]
  rfl

/-- Evaluation at zero recovers the constant determinant.-/
theorem quadraticPolynomial_eval_zero (U V : Matrix n n R) :
    (quadraticPolynomial U V).eval 0 = V.det := by
  rw [quadraticPolynomial, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  by_cases hij : i = j <;>
    simp [quadraticMatrix, Matrix.scalar_apply, pow_two,
      Matrix.diagonal_mul_diagonal, hij]

/-- Evaluation at minus one gives `det(I-U+V)`.-/
theorem quadraticPolynomial_eval_neg_one (U V : Matrix n n R) :
    (quadraticPolynomial U V).eval (-1) = (1 - U + V).det := by
  rw [quadraticPolynomial, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  by_cases hij : i = j <;>
    simp [quadraticMatrix, Matrix.scalar_apply, pow_two,
      Matrix.diagonal_mul_diagonal, sub_eq_add_neg, hij]

end PolynomialMatrix

section ThreeByThree

variable {R : Type*} [CommRing R]

/-- For a three-by-three matrix, the characteristic polynomial at zero is
minus the determinant.-/
theorem charpoly_eval_zero_three (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly.eval 0 = -M.det := by
  rw [Matrix.eval_charpoly]
  have hmatrix : Matrix.scalar (Fin 3) (0 : R) - M = -M := by simp
  rw [hmatrix, Matrix.det_neg]
  simp [pow_succ]

/-- For a three-by-three matrix, evaluation at minus one is
`-det(I+M)`.-/
theorem charpoly_eval_neg_one_three (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly.eval (-1) = -(1 + M).det := by
  rw [Matrix.eval_charpoly]
  have hmatrix : Matrix.scalar (Fin 3) (-1 : R) - M = -(1 + M) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.scalar_apply, sub_eq_add_neg, add_comm, hij]
  rw [hmatrix, Matrix.det_neg]
  simp [pow_succ]

end ThreeByThree

section ComplementaryEndpoints

variable {K : Type*} [Field K]

/-- Under the two determinant constraints, the complementary characteristic
factor has the same values at zero and minus one as the original factor.
The nonzero hypotheses are precisely the cancellation assumptions.-/
theorem complementary_charpoly_endpoints
    (X U V : Matrix (Fin 3) (Fin 3) K) (c d : K)
    (hquad : X ^ 2 + X * U + V = 0)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hdetX : X.det = c) (hdetOneX : (1 + X).det = -d)
    (hdetV : V.det = c ^ 2)
    (hdetNegOne : (1 - U + V).det = d ^ 2) :
    let Z := -U - X
    Z.charpoly.eval 0 = -c ∧ Z.charpoly.eval (-1) = d := by
  dsimp only
  have hfactor := quadraticPolynomial_eq_charpoly_mul X U V hquad
  constructor
  · have hzero := congrArg (Polynomial.eval 0) hfactor
    have hprod : c ^ 2 = (-c) * (-U - X).charpoly.eval 0 := by
      simpa [Polynomial.eval_mul, quadraticPolynomial_eval_zero,
        charpoly_eval_zero_three, hdetV, hdetX] using hzero
    apply mul_left_cancel₀ (neg_ne_zero.mpr hc)
    calc
      (-c) * (-U - X).charpoly.eval 0 = c ^ 2 := hprod.symm
      _ = (-c) * (-c) := by simp [pow_two]
  · have hneg := congrArg (Polynomial.eval (-1)) hfactor
    have hprod : d ^ 2 = d * (-U - X).charpoly.eval (-1) := by
      simpa [Polynomial.eval_mul, quadraticPolynomial_eval_neg_one,
        charpoly_eval_neg_one_three, hdetNegOne, hdetOneX] using hneg
    apply mul_left_cancel₀ hd
    calc
      d * (-U - X).charpoly.eval (-1) = d ^ 2 := hprod.symm
      _ = d * d := by rw [pow_two]

end ComplementaryEndpoints

end AlbertLean.Generic.FourRowFactorization
