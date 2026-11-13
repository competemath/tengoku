import Tengoku.Nlalib.NLAlib.Matrix.Nonnegative.MMatrixPrincipal
import Tengoku.Seed.LinearAlgebra.Matrix.SchurComplement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Schur complements of nonsingular M-matrices

The Schur inverse formula and the signs of the off-diagonal blocks prove
closure in both directions. The result does not require irreducibility.
Source: Berman–Plemmons, Nonnegative Matrices, Chapter 6.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace Matrix
variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

omit [Fintype ι] [Fintype η] in
/-- Entrywise nonnegativity is preserved by rectangular matrix multiplication.
@isnad1 id=le.2h7v.s6.b13c3366982e from=translated src=- shape=35e80eea vocab=6791fbbe
-/
theorem mul_apply_nonneg_of_nonneg {A : Matrix ι κ ℝ} {B : Matrix κ η ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (i : ι) (j : η) :
    0 ≤ (A * B) i j :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hB k j)

variable [DecidableEq ι] [DecidableEq κ]

/-- The bottom-right inverse block is the inverse of the Schur complement.
Both inverses are nonsingular; empty blocks are allowed.
@isnad1 id=eq.2h6v.s8.4cded0c16018 from=translated src=- shape=5789c76d vocab=c2daaa40
-/
theorem inverse_fromBlocks_bottomRight_of_isUnit
    (E : Matrix ι ι ℝ) (F : Matrix ι κ ℝ) (G : Matrix κ ι ℝ) (H : Matrix κ κ ℝ)
    (hE : IsUnit E) (hA : IsUnit (Matrix.fromBlocks E F G H)) :
    (Matrix.fromBlocks E F G H)⁻¹.toBlocks₂₂ = (H - G * E⁻¹ * F)⁻¹ := by
  let := E.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det E).mp hE)
  have hS : IsUnit (H - G * E⁻¹ * F) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using
      Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mp hA
  let := (H - G * E⁻¹ * F).invertibleOfIsUnitDet
    ((Matrix.isUnit_iff_isUnit_det _).mp hS)
  let := (Matrix.fromBlocks E F G H).invertibleOfIsUnitDet
    ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have h := Matrix.invOf_fromBlocks₁₁_eq E F G H
  simp only [Matrix.invOf_eq_nonsing_inv] at h
  rw [h]
  rfl

omit [Fintype κ] [DecidableEq κ] in
/-- The Schur complement of a Z-matrix with an inverse-positive leading block
is again a Z-matrix.
@isnad1 id=iszmatri.2h6v.s7.48995f826e17 from=translated src=- shape=8f7de61c vocab=56af87b3
-/
theorem IsZMatrix.schurComplement {E : Matrix ι ι ℝ} {F : Matrix ι κ ℝ}
    {G : Matrix κ ι ℝ} {H : Matrix κ κ ℝ}
    (hA : (Matrix.fromBlocks E F G H).IsZMatrix) (hE : E.IsNonsingularMMatrix) :
    (H - G * E⁻¹ * F).IsZMatrix := by
  have hF : ∀ i j, 0 ≤ (-F) i j := fun i j => neg_nonneg.mpr
    (hA (Sum.inl i) (Sum.inr j) (by simp))
  have hG : ∀ i j, 0 ≤ (-G) i j := fun i j => neg_nonneg.mpr
    (hA (Sum.inr i) (Sum.inl j) (by simp))
  have hprod : ∀ i j, 0 ≤ (G * E⁻¹ * F) i j := by
    have h := mul_apply_nonneg_of_nonneg
      (mul_apply_nonneg_of_nonneg hG hE.2.2) hF
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using h
  intro i j hij
  exact sub_nonpos.mpr ((hA (Sum.inr i) (Sum.inr j) (by simpa using hij)).trans (hprod i j))

/-- A Z-matrix is a nonsingular M-matrix exactly when an invertible leading
principal block and its Schur complement are nonsingular M-matrices.
The statement includes arbitrary finite index sets and empty blocks.
Source: Berman–Plemmons, Chapter 6.
atlas: m-matrix-schur-complement (partial)
@isnad1 id=iff.2h6v.s7.b66536e76a76 from=translated src=- shape=453fcba7 vocab=feedf176
-/
theorem isNonsingularMMatrix_fromBlocks_iff
    (E : Matrix ι ι ℝ) (F : Matrix ι κ ℝ) (G : Matrix κ ι ℝ) (H : Matrix κ κ ℝ)
    (hA : (Matrix.fromBlocks E F G H).IsZMatrix) (hEunit : IsUnit E) :
    (Matrix.fromBlocks E F G H).IsNonsingularMMatrix ↔
      E.IsNonsingularMMatrix ∧ (H - G * E⁻¹ * F).IsNonsingularMMatrix := by
  let := E.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det E).mp hEunit)
  constructor
  · intro hM
    have hE : E.IsNonsingularMMatrix := by
      exact hM.submatrix Sum.inl Sum.inl_injective
    have hSunit : IsUnit (H - G * E⁻¹ * F) := by
      simpa only [Matrix.invOf_eq_nonsing_inv] using
        Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mp hM.2.1
    refine ⟨hE, hA.schurComplement hE, hSunit, fun i j => ?_⟩
    rw [← inverse_fromBlocks_bottomRight_of_isUnit E F G H hEunit hM.2.1]
    exact hM.2.2 (Sum.inr i) (Sum.inr j)
  · rintro ⟨hE, hS⟩
    have hMunit : IsUnit (Matrix.fromBlocks E F G H) := by
      apply Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr
      simpa only [Matrix.invOf_eq_nonsing_inv] using hS.2.1
    let := (H - G * E⁻¹ * F).invertibleOfIsUnitDet
      ((Matrix.isUnit_iff_isUnit_det _).mp hS.2.1)
    let := (Matrix.fromBlocks E F G H).invertibleOfIsUnitDet
      ((Matrix.isUnit_iff_isUnit_det _).mp hMunit)
    have hInv := Matrix.invOf_fromBlocks₁₁_eq E F G H
    simp only [Matrix.invOf_eq_nonsing_inv] at hInv
    have hF : ∀ i j, 0 ≤ (-F) i j := fun i j => neg_nonneg.mpr
      (hA (Sum.inl i) (Sum.inr j) (by simp))
    have hG : ∀ i j, 0 ≤ (-G) i j := fun i j => neg_nonneg.mpr
      (hA (Sum.inr i) (Sum.inl j) (by simp))
    have hEF : ∀ i j, 0 ≤ (E⁻¹ * (-F)) i j :=
      mul_apply_nonneg_of_nonneg hE.2.2 hF
    have hSG : ∀ i j, 0 ≤ ((H - G * E⁻¹ * F)⁻¹ * (-G)) i j :=
      mul_apply_nonneg_of_nonneg hS.2.2 hG
    have hEFSG : ∀ i j, 0 ≤ (E⁻¹ * F * (H - G * E⁻¹ * F)⁻¹ * G * E⁻¹) i j := by
      have h := mul_apply_nonneg_of_nonneg
        (mul_apply_nonneg_of_nonneg (mul_apply_nonneg_of_nonneg hEF hS.2.2) hG) hE.2.2
      simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_neg] using h
    refine ⟨hA, hMunit, fun i j => ?_⟩
    rw [hInv]
    cases i with
    | inl i =>
      cases j with
      | inl j => exact add_nonneg (hE.2.2 i j) (hEFSG i j)
      | inr j =>
        have h := mul_apply_nonneg_of_nonneg hEF hS.2.2 i j
        change 0 ≤ (-(E⁻¹ * F * (H - G * E⁻¹ * F)⁻¹)) i j
        simpa only [Matrix.mul_neg, Matrix.neg_mul] using h
    | inr i =>
      cases j with
      | inl j =>
        have h := mul_apply_nonneg_of_nonneg hSG hE.2.2 i j
        change 0 ≤ (-((H - G * E⁻¹ * F)⁻¹ * G * E⁻¹)) i j
        simpa only [Matrix.mul_neg, Matrix.neg_mul] using h
      | inr j => exact hS.2.2 i j

end Matrix
