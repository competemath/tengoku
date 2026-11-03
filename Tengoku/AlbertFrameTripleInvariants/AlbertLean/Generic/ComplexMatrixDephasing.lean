import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ComplexDephasedPair
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms dephase_eq_diagonal_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms overlap_diagonal_scale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms overlap_dephase` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms overlap_inverseTranspose` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms entries_ne_zero_of_overlap_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.ComplexMatrixDephasing

open C1Coordinates

universe u
variable {K : Type u} [Field K]

def overlapOf (X : Mat3 K) (i j : Fin 3) : K := X i j * X⁻¹ j i

def dephase (X : Mat3 K) : Mat3 K :=
  fun i j => X 0 0 * X i j / (X i 0 * X 0 j)

def leftScale (X : Mat3 K) : Fin 3 → K := fun i => X 0 0 / X i 0
def rightScale (X : Mat3 K) : Fin 3 → K := fun j => (X 0 j)⁻¹

/--
@isnad1 id=eq.0h2v.s7.f90b6017af87 from=translated src=- shape=733fee43 vocab=20d79538
-/
theorem dephase_eq_diagonal_mul (X : Mat3 K) :
    dephase X = Matrix.diagonal (leftScale X) * X * Matrix.diagonal (rightScale X) := by
  ext i j
  simp [dephase, leftScale, rightScale, Matrix.mul_apply,
    Matrix.diagonal_apply, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
@isnad1 id=eq.2h3v.s7.d765a041733e from=translated src=- shape=c27265a5 vocab=1622e8ae
-/
theorem dephase_first_row (X : Mat3 K) (h00 : X 0 0 ≠ 0)
    (hrow : ∀ j, X 0 j ≠ 0) (j : Fin 3) : dephase X 0 j = 1 := by
  simp [dephase, h00, hrow j]

/--
@isnad1 id=eq.2h3v.s7.24fa9067d885 from=translated src=- shape=7b81a7d7 vocab=1622e8ae
-/
theorem dephase_first_col (X : Mat3 K) (h00 : X 0 0 ≠ 0)
    (hcol : ∀ i, X i 0 ≠ 0) (i : Fin 3) : dephase X i 0 = 1 := by
  simp [dephase, h00, hcol i, mul_comm]

/--
@isnad1 id=eq.3h5v.s9.54a4cf1ff261 from=translated src=- shape=2bfc6a82 vocab=e9c2e625
-/
theorem scaled_inverse
    (X Y : Mat3 K) (l r : Fin 3 → K)
    (hl : ∀ i, l i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hYX : Y * X = 1) :
    (Matrix.diagonal l * X * Matrix.diagonal r)⁻¹ =
      Matrix.diagonal (fun i => (r i)⁻¹) * Y *
        Matrix.diagonal (fun i => (l i)⁻¹) := by
  have hL : Matrix.diagonal (fun i => (l i)⁻¹) * Matrix.diagonal l =
      (1 : Mat3 K) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [hl]
    · simp [Matrix.diagonal_apply, h]
  have hR : Matrix.diagonal (fun i => (r i)⁻¹) * Matrix.diagonal r =
      (1 : Mat3 K) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [hr]
    · simp [Matrix.diagonal_apply, h]
  apply Matrix.inv_eq_left_inv
  calc
    (Matrix.diagonal (fun i => (r i)⁻¹) * Y * Matrix.diagonal (fun i => (l i)⁻¹)) *
        (Matrix.diagonal l * X * Matrix.diagonal r) =
      Matrix.diagonal (fun i => (r i)⁻¹) *
        (Y * (Matrix.diagonal (fun i => (l i)⁻¹) * Matrix.diagonal l) * X) *
          Matrix.diagonal r := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hL, Matrix.mul_one, hYX, Matrix.mul_one, hR]

/--
@isnad1 id=eq.3h6v.s8.2c139ce2daa2 from=translated src=- shape=c89840e5 vocab=fd4c86a2
-/
theorem overlap_diagonal_scale
    (X : Mat3 K) (l r : Fin 3 → K)
    (hl : ∀ i, l i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hdet : Matrix.det X ≠ 0) (i j : Fin 3) :
    overlapOf (Matrix.diagonal l * X * Matrix.diagonal r) i j = overlapOf X i j := by
  have hYX := Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hdet)
  rw [overlapOf, overlapOf,
    scaled_inverse X X⁻¹ l r hl hr hYX]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]
  field_simp [hl i, hr j]

/--
@isnad1 id=eq.2h4v.s6.bcb1298ad8b2 from=translated src=- shape=73d4a65f vocab=e2660e8f
-/
theorem overlap_dephase (X : Mat3 K)
    (hentries : ∀ i j, X i j ≠ 0) (hdet : Matrix.det X ≠ 0) (i j : Fin 3) :
    overlapOf (dephase X) i j = overlapOf X i j := by
  rw [dephase_eq_diagonal_mul]
  apply overlap_diagonal_scale
  · intro q
    exact div_ne_zero (hentries 0 0) (hentries q 0)
  · intro q
    exact inv_ne_zero (hentries 0 q)
  · exact hdet

/--
@isnad1 id=eq.1h4v.s7.7c55de5d1e4b from=translated src=- shape=9ffe61b4 vocab=5b8859f7
-/
theorem overlap_inverseTranspose (X : Mat3 K)
    (hdet : Matrix.det X ≠ 0) (i j : Fin 3) :
    overlapOf (Matrix.transpose X⁻¹) i j = overlapOf X i j := by
  have hu : IsUnit (Matrix.det X) := isUnit_iff_ne_zero.mpr hdet
  have hi : (Matrix.transpose X⁻¹)⁻¹ = Matrix.transpose X := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv X hu]
  simp only [overlapOf, hi, Matrix.transpose_apply]
  exact mul_comm _ _

/-- On the all-nine overlap open, every entry of `X` and every transposed
inverse entry needed for dephasing is nonzero.
@isnad1 id=and.1h2v.s7.a8ffd1bfe380 from=translated src=- shape=193f1db1 vocab=adf563e5
-/
theorem entries_ne_zero_of_overlap_ne_zero (X : Mat3 K)
    (hopen : ∀ i j, overlapOf X i j ≠ 0) :
    (∀ i j, X i j ≠ 0) ∧ (∀ i j, X⁻¹ j i ≠ 0) := by
  constructor <;> intro i j
  · exact (mul_ne_zero_iff.mp (hopen i j)).1
  · exact (mul_ne_zero_iff.mp (hopen i j)).2

/--
@isnad1 id=ne.1h4v.s7.4689255e1643 from=translated src=- shape=e9494c5d vocab=e5ba1b4d
-/
theorem inverseTranspose_entries_ne_zero_of_overlap_ne_zero (X : Mat3 K)
    (hopen : ∀ i j, overlapOf X i j ≠ 0) :
    ∀ i j, Matrix.transpose X⁻¹ i j ≠ 0 := by
  intro i j
  exact (entries_ne_zero_of_overlap_ne_zero X hopen).2 i j

end AlbertLean.Generic.ComplexMatrixDephasing
