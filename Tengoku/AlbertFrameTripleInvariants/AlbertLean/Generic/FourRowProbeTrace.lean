import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowProbeSeparation
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms trace_diagonalUnit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms trace_symmetricProbe` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms det_grading_commutator` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eq_of_trace_probes` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Trace interpretation of the symmetric-row probes

The literal trace probes reuse the separation theorem and its cycle scalar.
No Albert-model or labelled-frame dictionary is assumed.
-/

namespace AlbertLean.Generic.FourRowProbeTrace

open FourRowProbeSeparation

variable {K : Type*} [Field K]

/-- The ordinary matrix unit `E_ii`.-/
def diagonalUnit (i : Fin 3) : Mat3 K :=
  fun r c => if r = i ∧ c = i then 1 else 0

theorem trace_diagonalUnit (A : Mat3 K) (i : Fin 3) :
    Matrix.trace (diagonalUnit i * A) = A i i := by
  fin_cases i <;>
    simp [Matrix.trace_fin_three, Matrix.mul_apply, diagonalUnit, Fin.sum_univ_succ]

/-- A symmetric-row measurement is exactly the trace of the division-free
probe `(E_ii F + F E_ii) A`.-/
theorem trace_symmetricProbe (F A : Mat3 K) (i : Fin 3) :
    Matrix.trace ((diagonalUnit i * F + F * diagonalUnit i) * A) =
      rowSymMeasurements F A i := by
  fin_cases i <;>
    simp [Matrix.trace_fin_three, Matrix.mul_apply, diagonalUnit,
      rowSymMeasurements, Fin.sum_univ_succ] <;> ring

/-- The diagonal grading used in the three-row commutator test.-/
def grading : Mat3 K := Matrix.diagonal ![-1, 0, 1]

/-- The commutator determinant packages the same open condition as the three
pairwise `2 x 2` systems.-/
theorem det_grading_commutator (F : Mat3 K) :
    Matrix.det (grading * F - F * grading) = 2 * cycleDifference F := by
  rw [Matrix.det_fin_three]
  simp [grading, cycleDifference, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Nine literal trace measurements separate matrices on the displayed
commutator open. Its nonvanishing also supplies characteristic not two.-/
theorem eq_of_trace_probes (F A B : Mat3 K)
    (hdet : Matrix.det (grading * F - F * grading) ≠ 0)
    (hDiag : ∀ i, Matrix.trace (diagonalUnit i * A) = Matrix.trace (diagonalUnit i * B))
    (hFirst : ∀ i,
      Matrix.trace ((diagonalUnit i * F + F * diagonalUnit i) * A) =
        Matrix.trace ((diagonalUnit i * F + F * diagonalUnit i) * B))
    (hSecond : ∀ i,
      Matrix.trace ((diagonalUnit i * (F * F) + (F * F) * diagonalUnit i) * A) =
        Matrix.trace ((diagonalUnit i * (F * F) + (F * F) * diagonalUnit i) * B)) :
    A = B := by
  rw [det_grading_commutator] at hdet
  apply rowSymMeasurements_injective F A B
    (left_ne_zero_of_mul hdet) (right_ne_zero_of_mul hdet)
  · intro i
    simpa only [trace_diagonalUnit] using hDiag i
  · funext i
    simpa only [trace_symmetricProbe] using hFirst i
  · funext i
    simpa only [trace_symmetricProbe] using hSecond i

end AlbertLean.Generic.FourRowProbeTrace
