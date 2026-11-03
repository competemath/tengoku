import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedBlockSpectralData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms cyclic_intertwines` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms cyclic_mul_inv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms cyclic_inv_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rational_intertwiner` (it only prints; the queue checks the axioms of every declaration). -/

/-! A rational common-block normalizer. For the Q1 similitude route the
cyclic basis removes the eigenvalue square root entirely. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.CyclicBlockNormalizer
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
variable {K : Type*} [Field K] [CharZero K]

def cyclicBasis (X : Mat2 K) : Mat2 K := matrix 0 (X 0 1) 1 (X 1 1)
def cyclicBasisInv (X : Mat2 K) : Mat2 K :=
  matrix (-X 1 1 / X 0 1) 1 ((X 0 1)⁻¹) 0
def companion (X : Mat2 K) : Mat2 K := matrix 0 (-determinant X) 1 (trace2 X)

theorem cyclic_intertwines (X : Mat2 K) :
    X * cyclicBasis X = cyclicBasis X * companion X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicBasis, companion, matrix, trace2, determinant,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cyclic_mul_inv (X : Mat2 K) (h : X 0 1 ≠ 0) :
    cyclicBasis X * cyclicBasisInv X = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicBasis, cyclicBasisInv, matrix, Matrix.mul_apply,
      Fin.sum_univ_two, h] <;> field_simp <;> ring

theorem cyclic_inv_mul (X : Mat2 K) (h : X 0 1 ≠ 0) :
    cyclicBasisInv X * cyclicBasis X = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicBasis, cyclicBasisInv, matrix, Matrix.mul_apply,
      Fin.sum_univ_two, h] <;> field_simp <;> ring

/-- Equal trace and determinant yield an explicit GL2 intertwiner, with no
field extension. Its use on all three planes is a symplectic similitude.-/
theorem rational_intertwiner (X Y : Mat2 K)
    (hx : X 0 1 ≠ 0) (hy : Y 0 1 ≠ 0)
    (ht : trace2 X = trace2 Y) (hd : determinant X = determinant Y) :
    let T := cyclicBasis X * cyclicBasisInv Y
    let S := cyclicBasis Y * cyclicBasisInv X
    T * S = 1 ∧ S * T = 1 ∧ X * T = T * Y := by
  have hc : companion X = companion Y := by simp only [companion, ht, hd]
  have hi : companion Y * cyclicBasisInv Y = cyclicBasisInv Y * Y := by
    calc
      companion Y * cyclicBasisInv Y =
          (cyclicBasisInv Y * cyclicBasis Y) * companion Y * cyclicBasisInv Y := by
            rw [cyclic_inv_mul Y hy, one_mul]
      _ = cyclicBasisInv Y * (cyclicBasis Y * companion Y) * cyclicBasisInv Y := by
        simp only [Matrix.mul_assoc]
      _ = cyclicBasisInv Y * (Y * cyclicBasis Y) * cyclicBasisInv Y := by
        rw [← cyclic_intertwines]
      _ = cyclicBasisInv Y * Y := by
        simp only [Matrix.mul_assoc, cyclic_mul_inv Y hy, Matrix.mul_one]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = cyclicBasis X * (cyclicBasisInv Y * cyclicBasis Y) * cyclicBasisInv X := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [cyclic_inv_mul Y hy, Matrix.mul_one, cyclic_mul_inv X hx]
  · calc
      _ = cyclicBasis Y * (cyclicBasisInv X * cyclicBasis X) * cyclicBasisInv Y := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [cyclic_inv_mul X hx, Matrix.mul_one, cyclic_mul_inv Y hy]
  · calc
      _ = (X * cyclicBasis X) * cyclicBasisInv Y := by simp only [Matrix.mul_assoc]
      _ = (cyclicBasis X * companion Y) * cyclicBasisInv Y := by rw [cyclic_intertwines, hc]
      _ = cyclicBasis X * (cyclicBasisInv Y * Y) := by rw [Matrix.mul_assoc, hi]
      _ = _ := by simp only [Matrix.mul_assoc]

end AlbertLean.Generic.QuaternionRow.CyclicBlockNormalizer
