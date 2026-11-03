import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.OrthogonalConjugation
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms diagonalSign_orthogonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gaugeOverlap_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrix_gauge_eq_of_entrywise` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gaugeOverlap_neg_neg` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Matrix realization of the real-row sign gauge

The vertex signs from `SignGaugeCocycle` become diagonal orthogonal matrices.
This is the exact three-sided action on overlap matrices.
-/

namespace AlbertLean.Generic.RealRow

open C1Coordinates

variable {K : Type*} [Field K]

def diagonalSign (e : Fin 3 → K) : Mat3 K := Matrix.diagonal e

theorem diagonalSign_transpose (e : Fin 3 → K) :
    Matrix.transpose (diagonalSign e) = diagonalSign e := by
  exact Matrix.diagonal_transpose e

theorem diagonalSign_orthogonal (e : Fin 3 → K)
    (he : ∀ i, (e i) ^ 2 = 1) : IsOrthogonal (diagonalSign e) := by
  constructor <;> rw [diagonalSign_transpose]
  all_goals
    simp only [diagonalSign, Matrix.diagonal_mul_diagonal]
    simp only [← pow_two, he, Matrix.diagonal_one]

def gaugeOverlap (left right : Fin 3 → K) (U : Mat3 K) : Mat3 K :=
  diagonalSign left * U * diagonalSign right

theorem gaugeOverlap_apply (left right : Fin 3 → K) (U : Mat3 K) (i j : Fin 3) :
    gaugeOverlap left right U i j = left i * U i j * right j := by
  simp only [gaugeOverlap, diagonalSign, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The entrywise conclusion of overlap reconstruction is exactly equality
under the matrix sign-gauge action.-/
theorem matrix_gauge_eq_of_entrywise
    (U U' : Mat3 K) (left right : Fin 3 → K)
    (h : ∀ i j, U' i j = left i * U i j * right j) :
    U' = gaugeOverlap left right U := by
  ext i j
  rw [gaugeOverlap_apply]
  exact h i j

/-- Simultaneous negation acts trivially on a single two-sided overlap.  This
is one inclusion in the expected kernel statement; no exact-kernel claim is
made here.-/
theorem gaugeOverlap_neg_neg (left right : Fin 3 → K) (U : Mat3 K) :
    gaugeOverlap (-left) (-right) U = gaugeOverlap left right U := by
  ext i j
  simp [gaugeOverlap_apply]

end AlbertLean.Generic.RealRow
