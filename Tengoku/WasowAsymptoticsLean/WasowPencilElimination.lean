import Tengoku.WasowAsymptoticsLean.WasowLeadingBlocks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowPencilElimination.localB_lowerTriangular` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPencilElimination.localB_det` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPencilElimination.localB_isUnit_det` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPencilElimination.auxiliary_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPencilElimination.elimination_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPencilElimination.elimination_mul` (it only prints; the queue checks the axioms of every declaration). -/

/-! Actual polynomial inverses for the auxiliary blocks of a Jordan pencil,
and explicit invertible elimination of the lower-left block. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace WasowPencilElimination

def localB (m : ℕ) : Matrix (Fin m) (Fin m) (Polynomial ℂ) := fun i j =>
  (if i.val = j.val + 1 then X else 0) - (if i = j then 1 else 0)

/--
@isnad1 id=islowert.0h1v.s3.5479654b7613 from=translated src=- shape=995c1cb5 vocab=ff357a3e
-/
theorem localB_lowerTriangular (m : ℕ) : (localB m).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  have hn : i.val ≠ j.val + 1 := by omega
  have he : i ≠ j := ne_of_lt hij
  simp [localB,hn,he]

/--
@isnad1 id=eq.0h1v.s6.7144f74b636a from=translated src=- shape=d16e7404 vocab=46114e50
-/
theorem localB_det (m : ℕ) : (localB m).det = (-1 : Polynomial ℂ) ^ m := by
  rw [Matrix.det_of_isLowerTriangular (localB m) (localB_lowerTriangular m)]
  have hd (i : Fin m) : localB m i i = -1 := by
    simp [localB]
  simp only [hd, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/--
@isnad1 id=isunit.0h1v.s4.6fe9dce69041 from=translated src=- shape=684e7f3e vocab=5baa6d9d
-/
theorem localB_isUnit_det (m : ℕ) : IsUnit (localB m).det := by
  rw [localB_det]
  exact (IsUnit.neg isUnit_one).pow m

/-- Every auxiliary polynomial block has an actual two-sided matrix inverse.
@isnad1 id=other.0h2v.s9.bae4d9dfabc5 from=translated src=- shape=6ed784e1 vocab=37a7f29c
-/
theorem auxiliary_inverse {σ : Type*} [Fintype σ] [DecidableEq σ] (h : σ → ℕ) :
    let B := Matrix.blockDiagonal' (fun a => localB (h a))
    B⁻¹ * B = 1 ∧ B * B⁻¹ = 1 := by
  dsimp
  have hu : IsUnit (Matrix.blockDiagonal' (fun a => localB (h a))).det := by
    have hl : Matrix.blockDiagonal' (fun a => (localB (h a))⁻¹) *
        Matrix.blockDiagonal' (fun a => localB (h a)) = 1 := by
      rw [← Matrix.blockDiagonal'_mul]
      simp only [Matrix.nonsing_inv_mul _ (localB_isUnit_det _)]
      exact Matrix.blockDiagonal'_one
    exact Matrix.isUnit_det_of_left_inverse hl
  exact ⟨Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu⟩

section Eliminate
variable {R κ σ : Type*} [CommRing R]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

def elimination (BInv : Matrix κ κ R) (F : Matrix σ κ R) : Matrix (κ ⊕ σ) (κ ⊕ σ) R :=
  Matrix.fromBlocks BInv 0 (-(F*BInv)) 1

def eliminationInverse (B : Matrix κ κ R) (F : Matrix σ κ R) : Matrix (κ ⊕ σ) (κ ⊕ σ) R :=
  Matrix.fromBlocks B 0 F 1

/-- The elimination is a genuine invertible polynomial row transformation.
@isnad1 id=and.2h6v.s8.70fecd10b79c from=translated src=- shape=0bd46ae6 vocab=34021022
-/
theorem elimination_inverse (B BInv : Matrix κ κ R) (F : Matrix σ κ R)
    (hl : BInv*B=1) (hr : B*BInv=1) :
    eliminationInverse B F * elimination BInv F = 1 ∧
      elimination BInv F * eliminationInverse B F = 1 := by
  constructor
  · simp [eliminationInverse,elimination,Matrix.fromBlocks_multiply,hr,
      ← Matrix.fromBlocks_one]
  · simp [eliminationInverse,elimination,Matrix.fromBlocks_multiply,hl,
      Matrix.mul_assoc, ← Matrix.fromBlocks_one]

/-- Exact elimination of the coupling block, without changing the reduced
characteristic polynomial matrix in the lower-right corner.
@isnad1 id=eq.1h7v.s8.c0cf7fb10150 from=translated src=- shape=b502968e vocab=3f0e4aa9
-/
theorem elimination_mul (B BInv : Matrix κ κ R) (F : Matrix σ κ R) (T : Matrix σ σ R)
    (hl : BInv*B=1) :
    elimination BInv F * Matrix.fromBlocks B 0 F T = Matrix.fromBlocks 1 0 0 T := by
  simp [elimination,Matrix.fromBlocks_multiply,hl,Matrix.mul_assoc]

end Eliminate
end WasowPencilElimination
