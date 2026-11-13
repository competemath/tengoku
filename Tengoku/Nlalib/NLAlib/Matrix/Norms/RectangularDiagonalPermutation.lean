import Tengoku.Nlalib.NLAlib.Matrix.Norms.RectangularDiagonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Permuting rectangular diagonals with orthogonal matrices

The same thin permutation is extended separately to rows and columns, while
unused coordinates stay fixed. This realizes gauge permutations on the fixed rectangular matrix shape. Source: Bhatia (1997), Theorem IV.2.1.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- A rectangular diagonal vanishes in any row outside the thin diagonal range.
@isnad1 id=eq.1h5v.s5.5db1b536eea4 from=translated src=- shape=c2f21a6f vocab=18a8d046
-/
theorem rectangularDiagonal_apply_eq_zero_of_not_lt_left {m n : ℕ}
    (x : Fin (min m n) → ℝ) (i : Fin m) (j : Fin n) (hi : ¬ i.val < min m n) :
    rectangularDiagonal x i j = 0 := by
  simp only [rectangularDiagonal, rectDiag_apply]
  rw [dite_eq_right hi]
  split_ifs <;> rfl

/-- A rectangular diagonal vanishes in any column outside the thin diagonal range.
@isnad1 id=eq.1h5v.s5.787b9ff79f57 from=translated src=- shape=1a45ac24 vocab=18a8d046
-/
theorem rectangularDiagonal_apply_eq_zero_of_not_lt_right {m n : ℕ}
    (x : Fin (min m n) → ℝ) (i : Fin m) (j : Fin n) (hj : ¬ j.val < min m n) :
    rectangularDiagonal x i j = 0 := by
  by_cases hij : i.val = j.val
  · exact rectangularDiagonal_apply_eq_zero_of_not_lt_left x i j (by omega)
  · simp [rectangularDiagonal, rectDiag_apply, hij]

/-- Extending a thin permutation preserves membership in the prefix.
@isnad1 id=iff.1h4v.s5.cf296ac999b1 from=translated src=- shape=27258211 vocab=ebc1c55c
-/
theorem prefixPermutation_apply_lt_iff {k m : ℕ} (σ : Equiv.Perm (Fin k)) (hk : k ≤ m)
    (i : Fin m) : (prefixPermutation σ hk i).val < k ↔ i.val < k := by
  by_cases hi : i.val < k
  · rw [prefixPermutation_apply_of_lt σ hk i hi]
    exact ⟨fun _ => hi, fun _ => (σ ⟨i.val, hi⟩).isLt⟩
  · rw [prefixPermutation_apply_of_not_lt σ hk i hi]

/-- Applying the same thin permutation to rectangular row and column coordinates
permutes exactly the represented vector and leaves all padding zero.
@isnad1 id=eq.0h4v.s7.b630f0e5f24c from=translated src=- shape=6b78231b vocab=54818417
-/
theorem rectangularDiagonal_submatrix_prefixPermutation {m n : ℕ}
    (x : Fin (min m n) → ℝ) (σ : Equiv.Perm (Fin (min m n))) :
    (rectangularDiagonal x).submatrix (prefixPermutation σ (min_le_left m n))
      (prefixPermutation σ (min_le_right m n)) = rectangularDiagonal (x ∘ σ) := by
  ext i j
  by_cases hi : i.val < min m n
  · by_cases hj : j.val < min m n
    · let i0 : Fin (min m n) := ⟨i.val, hi⟩
      let j0 : Fin (min m n) := ⟨j.val, hj⟩
      have hie : i = Fin.castLE (min_le_left m n) i0 := Fin.ext rfl
      have hje : j = Fin.castLE (min_le_right m n) j0 := Fin.ext rfl
      simp only [Matrix.submatrix_apply, prefixPermutation_apply_of_lt σ (min_le_left m n) i hi,
        prefixPermutation_apply_of_lt σ (min_le_right m n) j hj]
      rw [rectangularDiagonal_apply_castLE]
      conv_rhs => rw [hie, hje, rectangularDiagonal_apply_castLE]
      simp only [Function.comp_apply, σ.injective.eq_iff]
      rfl
    · rw [Matrix.submatrix_apply, rectangularDiagonal_apply_eq_zero_of_not_lt_right
        x _ _ (by simpa only [prefixPermutation_apply_lt_iff] using hj),
        rectangularDiagonal_apply_eq_zero_of_not_lt_right (x ∘ σ) i j hj]
  · rw [Matrix.submatrix_apply, rectangularDiagonal_apply_eq_zero_of_not_lt_left
      x _ _ (by simpa only [prefixPermutation_apply_lt_iff] using hi),
      rectangularDiagonal_apply_eq_zero_of_not_lt_left (x ∘ σ) i j hi]

/-- Thin coordinate permutations are implemented by left and right
orthogonal matrices on the original rectangular shape.
@isnad1 id=ex.0h4v.s7.24c9c07d5fc7 from=translated src=- shape=3daba966 vocab=4043454c
-/
theorem exists_orthogonal_rectangularDiagonal_perm {m n : ℕ}
    (x : Fin (min m n) → ℝ) (σ : Equiv.Perm (Fin (min m n))) :
    ∃ (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ),
      HasOrthonormalCols U ∧ HasOrthonormalCols V ∧ U * rectangularDiagonal x * V =
        rectangularDiagonal (x ∘ σ) := by
  let α := prefixPermutation σ (min_le_left m n)
  let β := prefixPermutation σ (min_le_right m n)
  have hβ := hasOrthonormalCols_permMatrix β
  have hβt : HasOrthonormalCols (β.permMatrix ℝ)ᵀ := by
    change ((β.permMatrix ℝ)ᵀ)ᵀ * (β.permMatrix ℝ)ᵀ = 1
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hβ
  refine ⟨α.permMatrix ℝ, (β.permMatrix ℝ)ᵀ, hasOrthonormalCols_permMatrix α, hβt, ?_⟩
  rw [Matrix.transpose_permMatrix]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix, Function.id_comp,
    Function.comp_id, Equiv.Perm.inv_def, Equiv.symm_symm]
  exact rectangularDiagonal_submatrix_prefixPermutation x σ

end NLAlib
