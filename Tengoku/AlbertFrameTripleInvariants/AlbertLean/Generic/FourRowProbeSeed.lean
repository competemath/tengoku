import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowLabelledProbes
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms P_mul_Q` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Q_mul_P` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_trace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_encoder_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_commutator_det` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms frame_commutator_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
An explicit pair of ordinary matrix frames on the commutator-determinant open.
Conjugation proves the frame laws; only the fixed conjugator and determinant
are evaluated in coordinates. This is a derived matrix example, not a generic
coverage or invariant-field assertion.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowProbeSeed

open FourRowProbeTrace FourRowLabelledProbes

variable {K : Type*} [Field K] [CharZero K]
abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

def P : Mat3 K := !![1, 1, 0; 0, 1, 1; 1, 0, 1]
def Q : Mat3 K := (1 / 2 : K) • !![1, -1, 1; 1, 1, -1; -1, 1, 1]

theorem P_mul_Q : (P : Mat3 K) * Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Q, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Q_mul_P : (Q : Mat3 K) * P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Q, Matrix.mul_apply, Fin.sum_univ_succ]

def conjugate (A : Mat3 K) : Mat3 K := P * A * Q

theorem conjugate_mul (A B : Mat3 K) :
    conjugate (A * B) = conjugate A * conjugate B := by
  simp only [conjugate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q P, Q_mul_P, Matrix.one_mul]

theorem trace_conjugate (A : Mat3 K) :
    Matrix.trace (conjugate A) = Matrix.trace A := by
  rw [conjugate, Matrix.trace_mul_cycle, Q_mul_P, Matrix.one_mul]

theorem diagonalUnit_sum :
    (diagonalUnit 0 : Mat3 K) + diagonalUnit 1 + diagonalUnit 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diagonalUnit, Fin.ext_iff]

theorem diagonalUnit_mul (i j : Fin 3) :
    (diagonalUnit i : Mat3 K) * diagonalUnit j =
      if i = j then diagonalUnit i else 0 := by
  fin_cases i <;> fin_cases j <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [diagonalUnit, Matrix.mul_apply, Fin.sum_univ_succ]

theorem diagonalUnit_trace (i : Fin 3) :
    Matrix.trace (diagonalUnit i : Mat3 K) = 1 := by
  fin_cases i <;> norm_num [diagonalUnit, Matrix.trace_fin_three, Fin.ext_iff]

def frame (i : Fin 3) : Mat3 K := conjugate (diagonalUnit i)

theorem frame_sum : (frame 0 : Mat3 K) + frame 1 + frame 2 = 1 := by
  simp only [frame, conjugate, ← Matrix.add_mul, ← Matrix.mul_add]
  rw [diagonalUnit_sum, Matrix.mul_one, P_mul_Q]

theorem frame_mul (i j : Fin 3) :
    (frame i : Mat3 K) * frame j = if i = j then frame i else 0 := by
  rw [frame, frame, ← conjugate_mul, diagonalUnit_mul]
  split_ifs <;> simp [frame, conjugate]

theorem frame_trace (i : Fin 3) : Matrix.trace (frame i : Mat3 K) = 1 := by
  rw [frame, trace_conjugate, diagonalUnit_trace]

theorem frame_encoder_square :
    encoder (frame 0 : Mat3 K) (frame 2) * encoder (frame 0) (frame 2) =
      frame 0 + frame 2 := by
  apply encoder_square_of_orthogonal <;> norm_num [frame_mul, Fin.ext_iff]

theorem frame_encoder : encoder (frame 0 : Mat3 K) (frame 2) =
    (1 / 2 : K) • !![-1, 1, -1; -1, 1, 1; -2, 2, 0] := by
  have hg : (diagonalUnit 2 : Mat3 K) - diagonalUnit 0 = grading := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagonalUnit, grading, Fin.ext_iff]
  simp only [encoder, frame, conjugate, ← Matrix.sub_mul, ← Matrix.mul_sub, hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P, Q, grading, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecMul_diagonal, Fin.ext_iff]

theorem frame_commutator_det :
    Matrix.det (grading * encoder (frame 0 : Mat3 K) (frame 2) -
      encoder (frame 0) (frame 2) * grading) = -1 := by
  rw [frame_encoder, det_grading_commutator]
  norm_num [FourRowProbeSeparation.cycleDifference, Matrix.cons_val_two]

theorem frame_commutator_ne_zero :
    Matrix.det (grading * encoder (frame 0 : Mat3 K) (frame 2) -
      encoder (frame 0) (frame 2) * grading) ≠ 0 := by
  rw [frame_commutator_det]
  exact neg_ne_zero.mpr one_ne_zero

end AlbertLean.Generic.FourRowProbeSeed
