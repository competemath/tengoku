import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowProbeTrace
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.C1Coordinates
import Tengoku.Seed.LinearAlgebra.Matrix.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms orthogonalConjugate_symmetric` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms orthogonalConjugate_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms orthogonalConjugate_trace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frameOfOrthogonal_idempotent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frameOfOrthogonal_sum` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Orthogonal conjugation for the normalized real-row chart

These are group-action lemmas only.  They do not assert that every projector
frame admits an orthogonal basis matrix; that existence/coverage theorem is a
separate geometric obligation.
-/

namespace AlbertLean.Generic.RealRow

open C1Coordinates
open FourRowProbeTrace (diagonalUnit)

variable {K : Type*} [Field K]

/-- Two-sided orthogonality, stated without choosing a bundled group API.-/
structure IsOrthogonal (q : Mat3 K) : Prop where
  transpose_mul : Matrix.transpose q * q = 1
  mul_transpose : q * Matrix.transpose q = 1

/-- The real-row action.-/
def orthogonalConjugate (q A : Mat3 K) : Mat3 K :=
  q * A * Matrix.transpose q

theorem orthogonalConjugate_symmetric (q A : Mat3 K)
    (hA : Matrix.transpose A = A) :
    Matrix.transpose (orthogonalConjugate q A) = orthogonalConjugate q A := by
  simp only [orthogonalConjugate, Matrix.transpose_mul, Matrix.transpose_transpose,
    hA, Matrix.mul_assoc]

theorem orthogonalConjugate_mul (q A B : Mat3 K) (hq : IsOrthogonal q) :
    orthogonalConjugate q (A * B) =
      orthogonalConjugate q A * orthogonalConjugate q B := by
  simp only [orthogonalConjugate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.transpose q) q (B * Matrix.transpose q), hq.transpose_mul,
    Matrix.one_mul]

theorem orthogonalConjugate_one (q : Mat3 K) (hq : IsOrthogonal q) :
    orthogonalConjugate q 1 = 1 := by
  simp [orthogonalConjugate, hq.mul_transpose]

theorem orthogonalConjugate_add (q A B : Mat3 K) :
    orthogonalConjugate q (A + B) =
      orthogonalConjugate q A + orthogonalConjugate q B := by
  simp [orthogonalConjugate, Matrix.mul_add, Matrix.add_mul]

theorem orthogonalConjugate_trace (q A : Mat3 K) (hq : IsOrthogonal q) :
    Matrix.trace (orthogonalConjugate q A) = Matrix.trace A := by
  calc
    Matrix.trace (q * A * Matrix.transpose q) =
        Matrix.trace (Matrix.transpose q * (q * A)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace A := by rw [← Matrix.mul_assoc, hq.transpose_mul, Matrix.one_mul]

/-- An orthogonal basis matrix produces an ordered symmetric projector frame
from the diagonal frame.  This is the forward normalization construction; the
converse existence theorem is intentionally not assumed.-/
def frameOfOrthogonal (q : Mat3 K) : Fin 3 → Mat3 K :=
  fun i => orthogonalConjugate q (diagonalUnit i)

theorem frameOfOrthogonal_symmetric (q : Mat3 K) (i : Fin 3) :
    Matrix.transpose (frameOfOrthogonal q i) = frameOfOrthogonal q i := by
  apply orthogonalConjugate_symmetric
  ext r c
  simp [diagonalUnit, Matrix.transpose_apply, and_comm]

theorem frameOfOrthogonal_idempotent (q : Mat3 K) (hq : IsOrthogonal q)
    (i : Fin 3) : frameOfOrthogonal q i * frameOfOrthogonal q i =
      frameOfOrthogonal q i := by
  unfold frameOfOrthogonal
  rw [← orthogonalConjugate_mul q _ _ hq]
  congr 1
  ext r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [diagonalUnit, Matrix.mul_apply, Fin.sum_univ_succ]

theorem frameOfOrthogonal_sum (q : Mat3 K) (hq : IsOrthogonal q) :
    frameOfOrthogonal q 0 + frameOfOrthogonal q 1 + frameOfOrthogonal q 2 = 1 := by
  unfold frameOfOrthogonal
  rw [← orthogonalConjugate_add, ← orthogonalConjugate_add,
    show diagonalUnit 0 + diagonalUnit 1 + diagonalUnit 2 = (1 : Mat3 K) by
      ext r c
      fin_cases r <;> fin_cases c <;> simp [diagonalUnit]]
  exact orthogonalConjugate_one q hq

end AlbertLean.Generic.RealRow
