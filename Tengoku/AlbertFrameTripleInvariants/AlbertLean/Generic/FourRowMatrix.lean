import Tengoku.Seed.LinearAlgebra.Matrix.Invertible
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms cube_eq_of_right_quadratic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reconstruction_of_right_quadratic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrix_reconstruction_of_right_quadratic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sylvester_branch_package` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Abstract matrix identities for the four-row reconstruction pilot

The polynomial identities are proved in an arbitrary (possibly
noncommutative) ring.  They therefore apply to square matrices without any
coordinate expansion.  The final two lemmas specialize only the trace
calculation to finite matrices over a commutative ring.
-/

namespace AlbertLean.Generic.FourRowMatrix

section Ring

variable {R : Type*} [Ring R]

/-- A solution of the right quadratic `X² + XU + V = 0` has the displayed
cubic reduction.  Multiplication order is part of the conclusion.-/
theorem cube_eq_of_right_quadratic (X U V : R)
    (hquad : X ^ 2 + X * U + V = 0) :
    X ^ 3 = X * (U ^ 2 - V) + V * U := by
  rw [← sub_eq_zero]
  calc
    X ^ 3 - (X * (U ^ 2 - V) + V * U) =
        X * (X ^ 2 + X * U + V) - (X ^ 2 + X * U + V) * U := by
      simp only [pow_three, pow_two, mul_add, add_mul, mul_sub, mul_assoc]
      abel
    _ = 0 := by rw [hquad, mul_zero, zero_mul, sub_self]

/-- Cayley--Hamilton data combined with the right quadratic gives the
division-free reconstruction certificate.  `t` and `u` are stated as ring
elements; the two visible commutation hypotheses are exactly what is used for
scalar coefficients.-/
theorem mul_reconstruction_of_right_quadratic
    (X U V t u v : R)
    (hquad : X ^ 2 + X * U + V = 0)
    (hcubic : X ^ 3 - t * X ^ 2 + u * X - v = 0)
    (ht : t * X = X * t) (hu : u * X = X * u) :
    X * (U ^ 2 - V + t * U + u) = v - V * U - t * V := by
  have hcube := cube_eq_of_right_quadratic X U V hquad
  have htsq : t * X ^ 2 = X * t * X := by
    rw [pow_two, ← mul_assoc, ht]
  have htU : t * (X * U) = X * (t * U) := by
    rw [← mul_assoc, ht, mul_assoc]
  rw [← sub_eq_zero]
  calc
    X * (U ^ 2 - V + t * U + u) - (v - V * U - t * V) =
        (X ^ 3 - t * X ^ 2 + u * X - v) +
          t * (X ^ 2 + X * U + V) := by
      rw [hcube]
      simp only [mul_add, mul_sub]
      rw [htsq, htU, hu]
      simp only [mul_assoc]
      abel
    _ = 0 := by rw [hcubic, hquad, mul_zero, add_zero]

/-- If the reconstruction denominator is invertible, the certificate solves
for `X` by a single right multiplication.-/
theorem reconstruction_of_right_quadratic
    (X U V t u v : R)
    (hquad : X ^ 2 + X * U + V = 0)
    (hcubic : X ^ 3 - t * X ^ 2 + u * X - v = 0)
    (ht : t * X = X * t) (hu : u * X = X * u)
    [Invertible (U ^ 2 - V + t * U + u)] :
    X = (v - V * U - t * V) * ⅟(U ^ 2 - V + t * U + u) := by
  let E := U ^ 2 - V + t * U + u
  have hmul : X * E = v - V * U - t * V := by
    simpa [E] using
      mul_reconstruction_of_right_quadratic X U V t u v hquad hcubic ht hu
  calc
    X = X * E * ⅟E := by rw [mul_assoc, mul_invOf_self, mul_one]
    _ = (v - V * U - t * V) * ⅟E := by rw [hmul]

/-- The Sylvester equation identifies conjugation by `L` with the explicit
additive formula used by the branch construction.-/
theorem sylvester_conjugate_eq_add_invOf
    (X U L : R) [Invertible L]
    (hsylvester : (-U - X) * L - L * X = 1) :
    ⅟L * (-U - X) * L = X + ⅟L := by
  rw [← sub_eq_zero]
  calc
    ⅟L * (-U - X) * L - (X + ⅟L) =
        ⅟L * (((-U - X) * L - L * X) - 1) := by
      simp only [mul_sub, ← mul_assoc, invOf_mul_self, one_mul, mul_one]
      abel
    _ = 0 := by rw [hsylvester, sub_self, mul_zero]

/-- Multiplying the Sylvester equation on both sides by `L⁻¹` gives the
inverse relation used to verify the branch quadratic.-/
theorem sylvester_invOf_relation
    (X U L : R) [Invertible L]
    (hsylvester : (-U - X) * L - L * X = 1) :
    X * ⅟L + ⅟L * X + ⅟L * U + ⅟L * ⅟L = 0 := by
  have hsylvester' : (-U - X) * L = L * X + 1 :=
    (sub_eq_iff_eq_add.mp hsylvester).trans (add_comm 1 (L * X))
  have hright : -U - X = L * X * ⅟L + ⅟L := by
    calc
      -U - X = (-U - X) * (L * ⅟L) := by rw [mul_invOf_self, mul_one]
      _ = ((-U - X) * L) * ⅟L := by rw [mul_assoc]
      _ = (L * X + 1) * ⅟L := by rw [hsylvester']
      _ = L * X * ⅟L + ⅟L := by rw [add_mul, one_mul]
  have hleft : ⅟L * (-U - X) = X * ⅟L + ⅟L * ⅟L := by
    calc
      ⅟L * (-U - X) = ⅟L * (L * X * ⅟L + ⅟L) := by rw [hright]
      _ = X * ⅟L + ⅟L * ⅟L := by
        simp only [mul_add, ← mul_assoc, invOf_mul_self, one_mul]
  calc
    X * ⅟L + ⅟L * X + ⅟L * U + ⅟L * ⅟L =
        (X * ⅟L + ⅟L * ⅟L) - ⅟L * (-U - X) := by
      simp only [mul_sub, mul_neg]
      abel
    _ = 0 := by rw [hleft, sub_self]

/-- An invertible solution of the Sylvester equation constructs another
solution of the same right quadratic.-/
theorem sylvester_branch_right_quadratic
    (X U V L : R) [Invertible L]
    (hquad : X ^ 2 + X * U + V = 0)
    (hsylvester : (-U - X) * L - L * X = 1) :
    let Y := ⅟L * (-U - X) * L
    Y ^ 2 + Y * U + V = 0 := by
  dsimp only
  rw [sylvester_conjugate_eq_add_invOf X U L hsylvester]
  have hinv := sylvester_invOf_relation X U L hsylvester
  calc
    (X + ⅟L) ^ 2 + (X + ⅟L) * U + V =
        (X ^ 2 + X * U + V) +
          (X * ⅟L + ⅟L * X + ⅟L * U + ⅟L * ⅟L) := by
      simp only [pow_two, add_mul, mul_add]
      abel
    _ = 0 := by rw [hquad, hinv, add_zero]

/-- The branch matrix is `X + L⁻¹`, useful independently of its quadratic
equation.-/
theorem sylvester_branch_eq_add_invOf
    (X U L : R) [Invertible L]
    (hsylvester : (-U - X) * L - L * X = 1) :
    ⅟L * (-U - X) * L = X + ⅟L :=
  sylvester_conjugate_eq_add_invOf X U L hsylvester

end Ring

section MatrixTrace

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- Matrix form of the division-free reconstruction certificate, with the
Cayley--Hamilton coefficients displayed as scalars times the identity.-/
theorem matrix_mul_reconstruction_of_right_quadratic
    (X U V : Matrix n n K) (t u v : K)
    (hquad : X ^ 2 + X * U + V = 0)
    (hcubic : X ^ 3 - t • X ^ 2 + u • X - v • 1 = 0) :
    X * (U ^ 2 - V + t • U + u • 1) =
      v • 1 - V * U - t • V := by
  have ht : (t • (1 : Matrix n n K)) * X = X * (t • 1) := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  have hu : (u • (1 : Matrix n n K)) * X = X * (u • 1) := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  simpa [Matrix.smul_mul, Matrix.mul_smul] using
    mul_reconstruction_of_right_quadratic
      X U V (t • (1 : Matrix n n K)) (u • 1) (v • 1)
      hquad (by simpa [Matrix.smul_mul] using hcubic) ht hu

/-- Matrix reconstruction from scalar Cayley--Hamilton data when the displayed
denominator is invertible.-/
theorem matrix_reconstruction_of_right_quadratic
    (X U V : Matrix n n K) (t u v : K)
    (hquad : X ^ 2 + X * U + V = 0)
    (hcubic : X ^ 3 - t • X ^ 2 + u • X - v • 1 = 0)
    [Invertible (U ^ 2 - V + t • U + u • 1)] :
    X = (v • 1 - V * U - t • V) *
      ⅟(U ^ 2 - V + t • U + u • 1) := by
  let E := U ^ 2 - V + t • U + u • (1 : Matrix n n K)
  have hmul : X * E = v • 1 - V * U - t • V := by
    simpa [E] using
      matrix_mul_reconstruction_of_right_quadratic X U V t u v hquad hcubic
  calc
    X = X * E * ⅟E := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]
    _ = (v • 1 - V * U - t • V) * ⅟E := by rw [hmul]

/-- Trace is unchanged by conjugation using an `Invertible` matrix.-/
theorem trace_invOf_mul_mul
    (Z L : Matrix n n K) [Invertible L] :
    Matrix.trace (⅟L * Z * L) = Matrix.trace Z := by
  calc
    Matrix.trace (⅟L * Z * L) = Matrix.trace (L * (⅟L * Z)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace Z := by
      rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

/-- For the complementary matrix `Z = -U-X`, the Sylvester branch has the
complementary trace.-/
theorem trace_sylvester_branch
    (X U L : Matrix n n K) [Invertible L] :
    Matrix.trace (⅟L * (-U - X) * L) =
      -Matrix.trace U - Matrix.trace X := by
  rw [trace_invOf_mul_mul]
  simp

/-- The useful branch package: the Sylvester construction satisfies the same
right quadratic, has its explicit additive form, and has complementary trace.-/
theorem sylvester_branch_package
    (X U V L : Matrix n n K) [Invertible L]
    (hquad : X ^ 2 + X * U + V = 0)
    (hsylvester : (-U - X) * L - L * X = 1) :
    let Y := ⅟L * (-U - X) * L
    (Y ^ 2 + Y * U + V = 0) ∧
      (Y = X + ⅟L) ∧
      (Matrix.trace Y = -Matrix.trace U - Matrix.trace X) := by
  dsimp only
  exact ⟨sylvester_branch_right_quadratic X U V L hquad hsylvester,
    sylvester_branch_eq_add_invOf X U L hsylvester,
    trace_sylvester_branch X U L⟩

end MatrixTrace

end AlbertLean.Generic.FourRowMatrix
