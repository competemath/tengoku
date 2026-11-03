import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedBlockConjugacy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms rational_intertwiner_of_nonscalar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nonscalar_of_discriminant_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_all_blocks_conjugate` (it only prints; the queue checks the axioms of every declaration). -/

/-! A three-vector cyclic construction removes the coordinate-chart hypothesis
from the rational two-by-two block normalizer. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.NonscalarBlockNormalizer

open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.CyclicBlockNormalizer
open AlbertLean.Generic.QuaternionRow.WeightedBlockConjugacy

variable {K : Type*} [Field K] [CharZero K]

abbrev Vec2 (K : Type*) := Fin 2 → K

def e0 : Vec2 K := ![1, 0]
def e1 : Vec2 K := ![0, 1]

def cyclicBasisAt (X : Mat2 K) (v : Vec2 K) : Mat2 K :=
  fun i j => if j = 0 then v i else (Matrix.mulVec X v) i

def cyclicDet (X : Mat2 K) (v : Vec2 K) : K :=
  cyclicBasisAt X v 0 0 * cyclicBasisAt X v 1 1 -
    cyclicBasisAt X v 0 1 * cyclicBasisAt X v 1 0

def cyclicBasisAtInv (X : Mat2 K) (v : Vec2 K) : Mat2 K :=
  (cyclicDet X v)⁻¹ •
    !![cyclicBasisAt X v 1 1, -cyclicBasisAt X v 0 1;
       -cyclicBasisAt X v 1 0, cyclicBasisAt X v 0 0]

theorem cyclicBasisAt_mul_inv (X : Mat2 K) (v : Vec2 K)
    (hv : cyclicDet X v ≠ 0) :
    cyclicBasisAt X v * cyclicBasisAtInv X v = 1 := by
  dsimp only [cyclicDet] at hv
  have hn : -(cyclicBasisAt X v 1 0 * cyclicBasisAt X v 0 1) +
      cyclicBasisAt X v 0 0 * cyclicBasisAt X v 1 1 ≠ 0 := by
    convert hv using 1 <;> ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicBasisAtInv, cyclicDet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> field_simp [hv, hn] <;> ring
  linear_combination mul_inv_cancel₀ hn

theorem cyclicBasisAt_inv_mul (X : Mat2 K) (v : Vec2 K)
    (hv : cyclicDet X v ≠ 0) :
    cyclicBasisAtInv X v * cyclicBasisAt X v = 1 := by
  dsimp only [cyclicDet] at hv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicBasisAtInv, cyclicDet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> field_simp [hv] <;> ring

theorem cyclicBasisAt_intertwines (X : Mat2 K) (v : Vec2 K) :
    X * cyclicBasisAt X v = cyclicBasisAt X v * companion X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicBasisAt, companion, matrix, trace2, determinant,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

@[simp] theorem cyclicDet_e0 (X : Mat2 K) : cyclicDet X e0 = X 1 0 := by
  simp [cyclicDet, cyclicBasisAt, e0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

@[simp] theorem cyclicDet_e1 (X : Mat2 K) : cyclicDet X e1 = -X 0 1 := by
  simp [cyclicDet, cyclicBasisAt, e1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

@[simp] theorem cyclicDet_e0_add_e1 (X : Mat2 K) :
    cyclicDet X (e0 + e1) = X 1 0 + X 1 1 - X 0 0 - X 0 1 := by
  simp [cyclicDet, cyclicBasisAt, e0, e1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- One of `e₀,e₁,e₀+e₁` is cyclic for every nonscalar matrix.-/
theorem exists_three_cyclic (X : Mat2 K)
    (hX : ¬ ∃ a : K, X = a • (1 : Mat2 K)) :
    ∃ v : Vec2 K, (v = e0 ∨ v = e1 ∨ v = e0 + e1) ∧ cyclicDet X v ≠ 0 := by
  by_cases h10 : X 1 0 = 0
  · by_cases h01 : X 0 1 = 0
    · have hdiag : X 1 1 - X 0 0 ≠ 0 := by
        intro heq
        apply hX
        refine ⟨X 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.one_apply, h10, h01] at heq ⊢ <;> linear_combination heq
      refine ⟨e0 + e1, Or.inr (Or.inr rfl), ?_⟩
      simp [h10, h01]
      exact hdiag
    · exact ⟨e1, Or.inr (Or.inl rfl), by simpa using neg_ne_zero.mpr h01⟩
  · exact ⟨e0, Or.inl rfl, by simpa using h10⟩

/-- Nonscalar equal-trace/equal-determinant matrices have explicit mutually
inverse rational intertwiners, selected from three fixed cyclic vectors.-/
theorem rational_intertwiner_of_nonscalar (X Y : Mat2 K)
    (hX : ¬ ∃ a : K, X = a • (1 : Mat2 K))
    (hY : ¬ ∃ a : K, Y = a • (1 : Mat2 K))
    (ht : trace2 X = trace2 Y) (hd : determinant X = determinant Y) :
    ∃ vx vy : Vec2 K,
      (vx = e0 ∨ vx = e1 ∨ vx = e0 + e1) ∧
      (vy = e0 ∨ vy = e1 ∨ vy = e0 + e1) ∧
      let T := cyclicBasisAt X vx * cyclicBasisAtInv Y vy
      let S := cyclicBasisAt Y vy * cyclicBasisAtInv X vx
      T * S = 1 ∧ S * T = 1 ∧ X * T = T * Y := by
  obtain ⟨vx, hvxmem, hvx⟩ := exists_three_cyclic X hX
  obtain ⟨vy, hvymem, hvy⟩ := exists_three_cyclic Y hY
  refine ⟨vx, vy, hvxmem, hvymem, ?_⟩
  have hc : companion X = companion Y := by simp only [companion, ht, hd]
  have hi : companion Y * cyclicBasisAtInv Y vy = cyclicBasisAtInv Y vy * Y := by
    calc
      companion Y * cyclicBasisAtInv Y vy =
          (cyclicBasisAtInv Y vy * cyclicBasisAt Y vy) * companion Y *
            cyclicBasisAtInv Y vy := by rw [cyclicBasisAt_inv_mul Y vy hvy, Matrix.one_mul]
      _ = cyclicBasisAtInv Y vy * (cyclicBasisAt Y vy * companion Y) *
            cyclicBasisAtInv Y vy := by simp only [Matrix.mul_assoc]
      _ = cyclicBasisAtInv Y vy * (Y * cyclicBasisAt Y vy) *
            cyclicBasisAtInv Y vy := by rw [← cyclicBasisAt_intertwines]
      _ = cyclicBasisAtInv Y vy * Y := by
        simp only [Matrix.mul_assoc, cyclicBasisAt_mul_inv Y vy hvy, Matrix.mul_one]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = cyclicBasisAt X vx * (cyclicBasisAtInv Y vy * cyclicBasisAt Y vy) *
          cyclicBasisAtInv X vx := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [cyclicBasisAt_inv_mul Y vy hvy, Matrix.mul_one,
        cyclicBasisAt_mul_inv X vx hvx]
  · calc
      _ = cyclicBasisAt Y vy * (cyclicBasisAtInv X vx * cyclicBasisAt X vx) *
          cyclicBasisAtInv Y vy := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [cyclicBasisAt_inv_mul X vx hvx, Matrix.mul_one,
        cyclicBasisAt_mul_inv Y vy hvy]
  · calc
      _ = (X * cyclicBasisAt X vx) * cyclicBasisAtInv Y vy := by
        simp only [Matrix.mul_assoc]
      _ = (cyclicBasisAt X vx * companion Y) * cyclicBasisAtInv Y vy := by
        rw [cyclicBasisAt_intertwines, hc]
      _ = cyclicBasisAt X vx * (cyclicBasisAtInv Y vy * Y) := by rw [Matrix.mul_assoc, hi]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- A nonzero characteristic discriminant excludes scalar matrices.-/
theorem nonscalar_of_discriminant_ne_zero (X : Mat2 K)
    (hdisc : trace2 X ^ 2 - 4 * determinant X ≠ 0) :
    ¬ ∃ a : K, X = a • (1 : Mat2 K) := by
  rintro ⟨a, rfl⟩
  apply hdisc
  simp [trace2, determinant, Matrix.one_apply]
  ring

/-- Direct chart-free consumer for the accepted propagation theorem.-/
theorem exists_all_blocks_conjugate (B C : Fin 3 → Fin 3 → Mat2 K)
    (p q : Fin 3 → K) (hp1 : p 1 ≠ 0) (hp2 : p 2 ≠ 0)
    (hdB : ∀ i, B i i = q i • (1 : Mat2 K))
    (hrB : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hcB : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (hdC : ∀ i, C i i = q i • (1 : Mat2 K))
    (hrC : ∀ i, C i 0 + C i 1 + C i 2 = 0)
    (hcC : ∀ j, p 0 • C 0 j + p 1 • C 1 j + p 2 • C 2 j = 0)
    (hB : ¬ ∃ a : K, B 0 1 = a • (1 : Mat2 K))
    (hC : ¬ ∃ a : K, C 0 1 = a • (1 : Mat2 K))
    (ht : trace2 (B 0 1) = trace2 (C 0 1))
    (hd : determinant (B 0 1) = determinant (C 0 1)) :
    ∃ T S : Mat2 K, T * S = 1 ∧ S * T = 1 ∧
      ∀ i j, B i j = T * C i j * S := by
  obtain ⟨vx, vy, _, _, hTS, hST, hX⟩ :=
    rational_intertwiner_of_nonscalar (B 0 1) (C 0 1) hB hC ht hd
  exact ⟨_, _, hTS, hST,
    all_blocks_conjugate B C p q hp1 hp2 hdB hrB hcB hdC hrC hcC _ _ hTS hX⟩

end AlbertLean.Generic.QuaternionRow.NonscalarBlockNormalizer
