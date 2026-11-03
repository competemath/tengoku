import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericReorientationBase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms rationalM_reorient` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weightedTranspose_det` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_det_rationalM` (it only prints; the queue checks the axioms of every declaration). -/

/-! The solved diagonal entries respect the concrete base reorientation.
This optional attachment is separate so the field-map construction can be
checked independently. No frame-coverage claim occurs here. -/

noncomputable section

namespace AlbertLean.Generic.GenericReorientationBase

open Matrix
open AlbertLean.Generic.GenericDeterminantOpen

universe u
variable (k : Type u) [Field k] [CharZero k]

private theorem reorient_dA2 : reorient k (ι k (dA2 k)) = ι k (dA2 k) := by
  simp [dA2, dA0, dA1]

private theorem reorient_dB2 : reorient k (ι k (dB2 k)) = ι k (dB2 k) := by
  simp [dB2, dB0, dB1]

private theorem reorient_PA : reorient k (ι k (PA k)) = ι k (PA k) := by
  simp [PA, dA1, reorient_dA2]

private theorem reorient_PB : reorient k (ι k (PB k)) = ι k (PB k) := by
  simp [PB, dB1, reorient_dB2]

private theorem reorient_SA : reorient k (ι k (SA k)) = ι k (SA k) := by
  simp [SA, dA0, dA1, reorient_dA2]

private theorem reorient_SB : reorient k (ι k (SB k)) = ι k (SB k) := by
  simp [SB, dB0, dB1, reorient_dB2] <;>
    field_simp [base_a_ne_zero k] <;> ring

private theorem reorient_TA : reorient k (ι k (TA k)) = ι k (TA k) := by
  simp [TA, dA0, dA1, reorient_dA2, off, weight, swapOff] <;>
    field_simp [base_a_ne_zero k] <;> ring

private theorem reorient_TB : reorient k (ι k (TB k)) = ι k (TB k) := by
  simp [TB, dB0, dB1, reorient_dB2, off, weight, swapOff] <;>
    field_simp [base_a_ne_zero k] <;> ring

private theorem reorient_nA0 : reorient k (ι k (nA0 k)) = ι k (nA0 k) := by
  simp [nA0, reorient_TA, reorient_dA2, reorient_SA]

private theorem reorient_nA2 : reorient k (ι k (nA2 k)) = ι k (nA2 k) := by
  simp [nA2, reorient_PA, reorient_SA, reorient_nA0]

private theorem reorient_nB1 : reorient k (ι k (nB1 k)) = ι k (nB1 k) := by
  simp [nB1, reorient_TB, reorient_dB2, reorient_SB]

private theorem reorient_nB3 : reorient k (ι k (nB3 k)) = ι k (nB3 k) := by
  simp [nB3, reorient_PB, reorient_SB, reorient_nB1]

def weightedTranspose (M : Matrix (Fin 4) (Fin 4) (B k)) :
    Matrix (Fin 4) (Fin 4) (B k) := fun i j =>
  (weight k i)⁻¹ * weight k j * M j i

/-- This includes the four dependent diagonal entries, not only the twelve
independent off-diagonal generators.
@isnad1 id=eq.0h1v.s9.de91c59f5269 from=translated src=- shape=aa8c3b5c vocab=e503dc56
-/
theorem rationalM_reorient :
    (rationalM k).map (reorient k).toRingHom = weightedTranspose k (rationalM k) := by
  ext i j
  change reorient k (rationalM k i j) = (weight k i)⁻¹ * weight k j * rationalM k j i
  by_cases hij : i = j
  · subst j
    rw [inv_mul_cancel₀ (weight_ne_zero k i), one_mul]
    fin_cases i <;>
      simp [rationalM, reorient_nA0, reorient_nA2, reorient_nB1, reorient_nB3,
        reorient_PA, reorient_PB, map_div₀]
  · simp only [rationalM, dite_eq_right hij, dite_eq_right (Ne.symm hij)]
    exact reorient_off k ⟨(i,j), hij⟩

private theorem weightedTranspose_eq (M : Matrix (Fin 4) (Fin 4) (B k)) :
    weightedTranspose k M =
      Matrix.diagonal (fun i => (weight k i)⁻¹) * M.transpose * Matrix.diagonal (weight k) := by
  ext i j
  simp [weightedTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring

/-- Weighted transposition preserves every matrix determinant.
@isnad1 id=eq.0h2v.s8.36e3616f1a8e from=translated src=- shape=8058ac8a vocab=eb3545dc
-/
theorem weightedTranspose_det (M : Matrix (Fin 4) (Fin 4) (B k)) :
    Matrix.det (weightedTranspose k M) = Matrix.det M := by
  have hd : Matrix.diagonal (fun i => (weight k i)⁻¹) *
      Matrix.diagonal (weight k) = (1 : Matrix (Fin 4) (Fin 4) (B k)) := by
    rw [Matrix.diagonal_mul_diagonal]
    have hw : (fun i => (weight k i)⁻¹ * weight k i) = (fun _ : Fin 4 => (1 : B k)) := by
      funext i
      exact inv_mul_cancel₀ (weight_ne_zero k i)
    rw [hw]
    simp
  rw [weightedTranspose_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc
    _ = (Matrix.det (Matrix.diagonal (fun i => (weight k i)⁻¹)) *
        Matrix.det (Matrix.diagonal (weight k))) * Matrix.det M := by ring
    _ = Matrix.det M := by rw [← Matrix.det_mul, hd, Matrix.det_one, one_mul]

/--
@isnad1 id=eq.0h1v.s11.bdba9f1c9a66 from=translated src=- shape=850b23c5 vocab=0ba03ec6
-/
@[simp] theorem reorient_det_rationalM :
    reorient k (Matrix.det (rationalM k)) = Matrix.det (rationalM k) := by
  change (reorient k).toRingHom (Matrix.det (rationalM k)) = _
  rw [RingHom.map_det]
  change Matrix.det ((rationalM k).map (reorient k).toRingHom) = _
  rw [rationalM_reorient, weightedTranspose_det]

end AlbertLean.Generic.GenericReorientationBase
