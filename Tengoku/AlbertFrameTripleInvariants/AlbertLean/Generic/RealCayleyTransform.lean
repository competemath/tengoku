import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.OrthogonalConjugation
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms cayley_cayley` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms cayley_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms cayley_skew_of_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/

/-! The matrix Cayley transform, with every inverse cancellation justified by
its determinant. This interface does not assert geometric density. -/

noncomputable section
namespace AlbertLean.Generic.RealRow.Cayley

open C1Coordinates

universe u
variable {K : Type u} [Field K] [CharZero K]

local notation "I₃" => (1 : Mat3 K)

def cayley (A : Mat3 K) : Mat3 K := (I₃ - A) * (I₃ + A)⁻¹

def IsSkew (A : Mat3 K) : Prop := Matrix.transpose A = -A

private theorem detUnit {M : Mat3 K} (hM : Matrix.det M ≠ 0) :
    IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr hM

private theorem cancel_right {L R M : Mat3 K}
    (hM : IsUnit (Matrix.det M)) (h : L * M = R * M) : L = R := by
  have h' := congrArg (fun X => X * M⁻¹) h
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one] using h'

private theorem cancel_left {L R M : Mat3 K}
    (hM : IsUnit (Matrix.det M)) (h : M * L = M * R) : L = R := by
  have h' := congrArg (fun X => M⁻¹ * X) h
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul] using h'

theorem cayley_mul {A : Mat3 K} (hplus : Matrix.det (I₃ + A) ≠ 0) :
    cayley A * (I₃ + A) = I₃ - A := by
  simp only [cayley, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (detUnit hplus),
    Matrix.mul_one]

theorem one_add_cayley_mul {A : Mat3 K}
    (hplus : Matrix.det (I₃ + A) ≠ 0) :
    (I₃ + cayley A) * (I₃ + A) = (2 : K) • I₃ := by
  rw [Matrix.add_mul, Matrix.one_mul, cayley_mul hplus]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring

theorem one_sub_cayley_mul {A : Mat3 K}
    (hplus : Matrix.det (I₃ + A) ≠ 0) :
    (I₃ - cayley A) * (I₃ + A) = (2 : K) • A := by
  rw [Matrix.sub_mul, Matrix.one_mul, cayley_mul hplus]
  ext i j
  simp [Matrix.one_apply]
  ring

theorem det_one_add_cayley_ne_zero {A : Mat3 K}
    (hplus : Matrix.det (I₃ + A) ≠ 0) :
    Matrix.det (I₃ + cayley A) ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det (one_add_cayley_mul (A := A) hplus)
  rw [Matrix.det_mul, hzero, zero_mul] at hdet
  norm_num [Matrix.det_smul, Fintype.card_fin] at hdet

theorem cayley_cayley {A : Mat3 K}
    (hplus : Matrix.det (I₃ + A) ≠ 0) : cayley (cayley A) = A := by
  apply cancel_right (detUnit (det_one_add_cayley_ne_zero hplus))
  rw [cayley_mul (det_one_add_cayley_ne_zero hplus)]
  apply cancel_right (detUnit hplus)
  rw [one_sub_cayley_mul hplus, Matrix.mul_assoc, one_add_cayley_mul hplus]
  simp

theorem cayley_orthogonal {A : Mat3 K} (hA : IsSkew A)
    (hplus : Matrix.det (I₃ + A) ≠ 0) : IsOrthogonal (cayley A) := by
  have hu := detUnit hplus
  have huT : IsUnit (Matrix.det (Matrix.transpose (I₃ + A))) := by
    rwa [Matrix.det_transpose]
  have horth : Matrix.transpose (cayley A) * cayley A = I₃ := by
    apply cancel_left huT
    apply cancel_right hu
    calc
      (Matrix.transpose (I₃ + A) *
          (Matrix.transpose (cayley A) * cayley A)) * (I₃ + A) =
          Matrix.transpose (cayley A * (I₃ + A)) * (cayley A * (I₃ + A)) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Matrix.transpose (I₃ - A) * (I₃ - A) := by rw [cayley_mul hplus]
      _ = (Matrix.transpose (I₃ + A) * I₃) * (I₃ + A) := by
        simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
          show Matrix.transpose A = -A from hA, Matrix.mul_one]
        noncomm_ring
  exact ⟨horth, mul_eq_one_comm.mp horth⟩

theorem cayley_skew_of_orthogonal {Q : Mat3 K} (hQ : IsOrthogonal Q)
    (hplus : Matrix.det (I₃ + Q) ≠ 0) : IsSkew (cayley Q) := by
  have hu := detUnit hplus
  have huT : IsUnit (Matrix.det (Matrix.transpose (I₃ + Q))) := by
    rwa [Matrix.det_transpose]
  change Matrix.transpose (cayley Q) = -cayley Q
  apply cancel_left huT
  apply cancel_right hu
  calc
    (Matrix.transpose (I₃ + Q) * Matrix.transpose (cayley Q)) * (I₃ + Q) =
        Matrix.transpose (I₃ - Q) * (I₃ + Q) := by
          rw [← Matrix.transpose_mul, cayley_mul hplus]
    _ = -(Matrix.transpose (I₃ + Q) * (I₃ - Q)) := by
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
      noncomm_ring [hQ.transpose_mul]
    _ = (Matrix.transpose (I₃ + Q) * (-cayley Q)) * (I₃ + Q) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, cayley_mul hplus]

end AlbertLean.Generic.RealRow.Cayley
