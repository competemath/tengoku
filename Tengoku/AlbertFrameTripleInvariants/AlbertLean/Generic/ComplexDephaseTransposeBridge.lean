import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ComplexDephasingAdapter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms dephase_diagonal_scale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverseTranspose_dephase_eq_diagonal_scale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms dephase_inverseTranspose_dephase` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.ComplexDephaseTransposeBridge

open C1Coordinates ComplexMatrixDephasing

universe u
variable {K : Type u} [Field K]

/-- Dephasing forgets arbitrary invertible diagonal row and column scalings.-/
theorem dephase_diagonal_scale (X : Mat3 K) (l r : Fin 3 → K)
    (hl : ∀ i, l i ≠ 0) (hr : ∀ j, r j ≠ 0) :
    dephase (Matrix.diagonal l * X * Matrix.diagonal r) = dephase X := by
  ext i j
  simp only [dephase, Matrix.mul_apply, Matrix.diagonal_apply]
  simp
  field_simp [hl 0, hl i, hr 0, hr j]

private theorem transpose_diagonal (d : Fin 3 → K) :
    Matrix.transpose (Matrix.diagonal d) = Matrix.diagonal d := by
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.transpose_apply, Matrix.diagonal_apply, h, Ne.symm h]

/-- The inverse transpose of the normalized matrix differs from the inverse
transpose of the original matrix only by invertible diagonal factors.-/
theorem inverseTranspose_dephase_eq_diagonal_scale (X : Mat3 K)
    (hentries : ∀ i j, X i j ≠ 0) (hdet : Matrix.det X ≠ 0) :
    Matrix.transpose (dephase X)⁻¹ =
      Matrix.diagonal (fun i => (leftScale X i)⁻¹) *
        Matrix.transpose X⁻¹ *
          Matrix.diagonal (fun j => (rightScale X j)⁻¹) := by
  have hl : ∀ i, leftScale X i ≠ 0 := fun i =>
    div_ne_zero (hentries 0 0) (hentries i 0)
  have hr : ∀ j, rightScale X j ≠ 0 := fun j =>
    inv_ne_zero (hentries 0 j)
  have hYX : X⁻¹ * X = 1 :=
    Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hdet)
  rw [dephase_eq_diagonal_mul,
    scaled_inverse X X⁻¹ (leftScale X) (rightScale X) hl hr hYX]
  simp only [Matrix.transpose_mul]
  rw [transpose_diagonal, transpose_diagonal]
  simp only [Matrix.mul_assoc]

/-- Dephasing is compatible with the inverse-transpose branch of the
normalized-pair classification.-/
theorem dephase_inverseTranspose_dephase (X : Mat3 K)
    (hentries : ∀ i j, X i j ≠ 0) (hdet : Matrix.det X ≠ 0) :
    dephase (Matrix.transpose (dephase X)⁻¹) =
      dephase (Matrix.transpose X⁻¹) := by
  rw [inverseTranspose_dephase_eq_diagonal_scale X hentries hdet]
  apply dephase_diagonal_scale
  · intro i
    exact inv_ne_zero (div_ne_zero (hentries 0 0) (hentries i 0))
  · intro j
    exact inv_ne_zero (inv_ne_zero (hentries 0 j))

end AlbertLean.Generic.ComplexDephaseTransposeBridge
