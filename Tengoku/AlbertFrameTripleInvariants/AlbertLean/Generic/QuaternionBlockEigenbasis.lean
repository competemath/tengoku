import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms determinant_affine` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms trace_eq_of_two_determinants` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms characteristic_roots` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eigenbasis_det` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eigenbasis_intertwines` (it only prints; the queue checks the axioms of every declaration). -/

/-! Explicit two-dimensional algebra for the quaternionic second-frame route.
This supplies the common-block eigenbasis step; it does not assert that an
arbitrary pair of quaternionic frames has already reached these blocks. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.BlockEigenbasis

variable {K : Type*} [Field K] [CharZero K]

abbrev Mat2 (K : Type*) := Matrix (Fin 2) (Fin 2) K

def matrix (a b c d : K) : Mat2 K := !![a, b; c, d]
def trace2 (X : Mat2 K) : K := X 0 0 + X 1 1
def determinant (X : Mat2 K) : K := X 0 0 * X 1 1 - X 0 1 * X 1 0

theorem determinant_eq_det (X : Mat2 K) : determinant X = X.det := by
  simp [determinant, Matrix.det_fin_two]

def affine (s t : K) (X : Mat2 K) : Mat2 K := s • (1 : Mat2 K) + t • X

theorem determinant_affine (s t : K) (X : Mat2 K) :
    determinant (affine s t X) = s ^ 2 + s * t * trace2 X + t ^ 2 * determinant X := by
  simp [determinant, affine, trace2, Matrix.one_apply, smul_eq_mul]
  ring

/-- Once the first row and column are scalar blocks, a second block determinant
recovers the remaining block trace.-/
theorem trace_eq_of_two_determinants (s t : K) (hs : s ≠ 0) (ht : t ≠ 0)
    (X Y : Mat2 K) (hdet : determinant X = determinant Y)
    (haffine : determinant (affine s t X) = determinant (affine s t Y)) :
    trace2 X = trace2 Y := by
  rw [determinant_affine, determinant_affine, hdet] at haffine
  have hmul : (s * t) * (trace2 X - trace2 Y) = 0 := by
    linear_combination haffine
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hs ht))

def lambdaPlus (X : Mat2 K) (sigma : K) : K := (trace2 X + sigma) / 2
def lambdaMinus (X : Mat2 K) (sigma : K) : K := (trace2 X - sigma) / 2

theorem characteristic_roots (X : Mat2 K) (sigma : K)
    (hroot : sigma ^ 2 = trace2 X ^ 2 - 4 * determinant X) :
    (lambdaPlus X sigma) ^ 2 - trace2 X * lambdaPlus X sigma + determinant X = 0 ∧
    (lambdaMinus X sigma) ^ 2 - trace2 X * lambdaMinus X sigma + determinant X = 0 := by
  constructor <;> dsimp [lambdaPlus, lambdaMinus] <;>
    linear_combination hroot / 4

def eigenbasis (X : Mat2 K) (sigma : K) : Mat2 K :=
  let delta := -(X 0 1 * sigma)
  matrix (X 0 1 / delta) (X 0 1)
    ((lambdaPlus X sigma - X 0 0) / delta) (lambdaMinus X sigma - X 0 0)

def eigenvalues (X : Mat2 K) (sigma : K) : Mat2 K :=
  matrix (lambdaPlus X sigma) 0 0 (lambdaMinus X sigma)

/-- Rescaling one eigenvector gives determinant one, without adjoining
another square root.-/
theorem eigenbasis_det (X : Mat2 K) (sigma : K)
    (hb : X 0 1 ≠ 0) (hs : sigma ≠ 0) :
    determinant (eigenbasis X sigma) = 1 := by
  dsimp [determinant, eigenbasis, matrix, lambdaPlus, lambdaMinus]
  field_simp [hb, hs]
  <;> ring

/-- An explicit SL2 eigenbasis on the nonzero off-diagonal discriminant chart.-/
theorem eigenbasis_intertwines (X : Mat2 K) (sigma : K)
    (hb : X 0 1 ≠ 0) (hs : sigma ≠ 0)
    (hroot : sigma ^ 2 = trace2 X ^ 2 - 4 * determinant X) :
    X * eigenbasis X sigma = eigenbasis X sigma * eigenvalues X sigma := by
  obtain ⟨hp, hm⟩ := characteristic_roots X sigma hroot
  have hdelta : -(X 0 1 * sigma) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hb hs)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp only [eigenbasis, eigenvalues, matrix, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero',
    Matrix.cons_val_succ', mul_zero, zero_mul, add_zero, zero_add]
  · change X 0 0 * (X 0 1 / -(X 0 1 * sigma)) +
        X 0 1 * ((lambdaPlus X sigma - X 0 0) / -(X 0 1 * sigma)) =
      (X 0 1 / -(X 0 1 * sigma)) * lambdaPlus X sigma
    field_simp [hdelta]
    ring
  · change X 0 0 * X 0 1 + X 0 1 * (lambdaMinus X sigma - X 0 0) =
      X 0 1 * lambdaMinus X sigma
    ring
  · change X 1 0 * (X 0 1 / -(X 0 1 * sigma)) +
        X 1 1 * ((lambdaPlus X sigma - X 0 0) / -(X 0 1 * sigma)) =
      ((lambdaPlus X sigma - X 0 0) / -(X 0 1 * sigma)) *
        lambdaPlus X sigma
    field_simp [hdelta]
    dsimp [trace2, determinant] at hp
    linear_combination hp
  · change X 1 0 * X 0 1 + X 1 1 * (lambdaMinus X sigma - X 0 0) =
      (lambdaMinus X sigma - X 0 0) * lambdaMinus X sigma
    dsimp [trace2, determinant] at hm
    linear_combination -hm

end AlbertLean.Generic.QuaternionRow.BlockEigenbasis
