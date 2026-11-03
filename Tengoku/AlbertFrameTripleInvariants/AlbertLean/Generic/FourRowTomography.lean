import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.LinearAlgebra.Matrix.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTomography.measurements_eq_mulVec` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTomography.transposeVector_eq_inverse_measurements` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTomography.eq_of_measurements_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTomography.eq_of_centered_measurements_eq` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Recovering a matrix from trace measurements

The measurement matrix has a literal row for each probe matrix, and columns
in paired index order.  Its inverse recovers the transpose-vectorized unknown.
This is ordinary finite-dimensional linear algebra; an Albert application must
separately identify its probes and ledger cells with these trace measurements.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowTomography

variable {K n : Type*} [Field K] [Fintype n]

/-- Transpose vectorization, the order forced by `trace (Z * A)`.-/
def transposeVector (A : Matrix n n K) : n × n → K := fun ij => A ij.2 ij.1

/-- Rows contain the entries of the probe matrices without a permutation.-/
def measurementMatrix (Z : n × n → Matrix n n K) : Matrix (n × n) (n × n) K :=
  fun p ij => Z p ij.1 ij.2

/-- The measured scalar associated to each probe.-/
def measurements (Z : n × n → Matrix n n K) (A : Matrix n n K) : n × n → K :=
  fun p => Matrix.trace (Z p * A)

/-- The trace pairing is the stated linear system in literal index order.-/
theorem measurements_eq_mulVec (Z : n × n → Matrix n n K) (A : Matrix n n K) :
    measurements Z A = (measurementMatrix Z).mulVec (transposeVector A) := by
  funext p
  simp [measurements, measurementMatrix, transposeVector, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

variable [DecidableEq n]

/-- On the nonzero determinant open, all entries are recovered by one inverse.-/
theorem transposeVector_eq_inverse_measurements
    (Z : n × n → Matrix n n K) (hZ : (measurementMatrix Z).det ≠ 0)
    (A : Matrix n n K) :
    transposeVector A = (measurementMatrix Z)⁻¹.mulVec (measurements Z A) := by
  rw [measurements_eq_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hZ), Matrix.one_mulVec]

/-- No two different matrices have the same measurements on this open.-/
theorem eq_of_measurements_eq
    (Z : n × n → Matrix n n K) (hZ : (measurementMatrix Z).det ≠ 0)
    {A B : Matrix n n K} (h : measurements Z A = measurements Z B) : A = B := by
  have hv : transposeVector A = transposeVector B := by
    rw [transposeVector_eq_inverse_measurements Z hZ A,
      transposeVector_eq_inverse_measurements Z hZ B, h]
  ext i j
  exact congrFun hv (j, i)

/-- Known centering terms do not change injectivity of the measurement map.-/
theorem eq_of_centered_measurements_eq
    (Z : n × n → Matrix n n K) (hZ : (measurementMatrix Z).det ≠ 0)
    (offset : n × n → K) {A B : Matrix n n K}
    (h : measurements Z A - offset = measurements Z B - offset) : A = B := by
  exact eq_of_measurements_eq Z hZ (sub_left_inj.mp h)

end AlbertLean.Generic.FourRowTomography
