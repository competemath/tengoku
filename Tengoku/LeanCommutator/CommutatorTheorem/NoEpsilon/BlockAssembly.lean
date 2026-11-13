import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.Sylvester
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.BlockCompression
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.GridCenters
import Tengoku.Seed.Data.Matrix.Block

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/WuProver/lean-commutator@2f197491d436, `CommutatorTheorem/NoEpsilon/BlockAssembly.lean`: removed 19 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Finite block assembly in the Euclidean operator norm

The blocks have arbitrary finite index types, and may have different dimensions.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NoEpsilon
namespace BlockAssembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
/-- A rectangular block of a matrix indexed by a dependent disjoint union.-/
def block (A : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) : Matrix (d i) (d j) ℂ :=
  A.submatrix (Sigma.mk i) (Sigma.mk j)

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
/-- Restrict a Euclidean vector to one block.-/
def vectorBlock (x : EuclideanSpace ℂ (Sigma d)) (i : ι) : EuclideanSpace ℂ (d i) :=
  WithLp.toLp 2 (fun a ↦ x ⟨i, a⟩)

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
-- Preserve the existing parameter list for downstream callers.
theorem norm_sq_eq_sum_vectorBlock (x : EuclideanSpace ℂ (Sigma d)) :
    ‖x‖ ^ 2 = ∑ i, ‖vectorBlock x i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, vectorBlock]
  exact Fintype.sum_sigma _

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
theorem block_mulVec (A : Matrix (Sigma d) (Sigma d) ℂ)
    (x : EuclideanSpace ℂ (Sigma d)) (i : ι) :
    vectorBlock (Matrix.toEuclideanLin A x) i =
      ∑ j, Matrix.toEuclideanLin (block A i j) (vectorBlock x j) := by
  ext a
  simp only [vectorBlock, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    Matrix.toLpLin_apply, block, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  exact Fintype.sum_sigma _

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
theorem diagonal_mulVec (D : ∀ i, Matrix (d i) (d i) ℂ)
    (x : EuclideanSpace ℂ (Sigma d)) (i : ι) :
    vectorBlock (Matrix.toEuclideanLin (Matrix.blockDiagonal' D) x) i =
      Matrix.toEuclideanLin (D i) (vectorBlock x i) := by
  ext a
  simp only [vectorBlock, PiLp.toLp_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    apply Finset.sum_eq_zero
    intro b _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hji.symm, zero_mul]

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
/-- A block diagonal matrix is bounded by a common bound for its diagonal blocks.-/
theorem norm_blockDiagonal_le (D : ∀ i, Matrix (d i) (d i) ℂ)
    (q : ℝ) (hq : 0 ≤ q) (hD : ∀ i, ‖D i‖ ≤ q) :
    ‖Matrix.blockDiagonal' D‖ ≤ q := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro x
  change ‖Matrix.toEuclideanLin (Matrix.blockDiagonal' D) x‖ ≤ q * ‖x‖
  apply le_of_sq_le_sq _ (mul_nonneg hq (norm_nonneg _))
  rw [norm_sq_eq_sum_vectorBlock, mul_pow, norm_sq_eq_sum_vectorBlock]
  simp_rw [diagonal_mulVec]
  calc
    ∑ i, ‖Matrix.toEuclideanLin (D i) (vectorBlock x i)‖ ^ 2 ≤
        ∑ i, q ^ 2 * ‖vectorBlock x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := Matrix.l2_opNorm_mulVec (D i) (vectorBlock x i)
      have h' : ‖Matrix.toEuclideanLin (D i) (vectorBlock x i)‖ ≤
          q * ‖vectorBlock x i‖ :=
        h.trans (mul_le_mul_of_nonneg_right (hD i) (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = q ^ 2 * ∑ i, ‖vectorBlock x i‖ ^ 2 := by rw [Finset.mul_sum]

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
/-- A common bound for all rectangular blocks gives a bound linear in the block count.-/
theorem norm_le_card_mul_block_bound (A : Matrix (Sigma d) (Sigma d) ℂ)
    (q : ℝ) (hq : 0 ≤ q) (hA : ∀ i j, ‖block A i j‖ ≤ q) :
    ‖A‖ ≤ Fintype.card ι * q := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hq)
  intro x
  change ‖Matrix.toEuclideanLin A x‖ ≤ (Fintype.card ι : ℝ) * q * ‖x‖
  have hrow (i : ι) : ‖vectorBlock (Matrix.toEuclideanLin A x) i‖ ≤
      q * ∑ j, ‖vectorBlock x j‖ := by
    rw [block_mulVec]
    calc
      ‖∑ j, Matrix.toEuclideanLin (block A i j) (vectorBlock x j)‖ ≤
          ∑ j, ‖Matrix.toEuclideanLin (block A i j) (vectorBlock x j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, q * ‖vectorBlock x j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (Matrix.l2_opNorm_mulVec (block A i j) (vectorBlock x j)).trans
          (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _))
      _ = q * ∑ j, ‖vectorBlock x j‖ := (Finset.mul_sum _ _ _).symm
  have hCS : (∑ j, ‖vectorBlock x j‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ j, ‖vectorBlock x j‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : ι ↦ (1 : ℝ)) (fun j ↦ ‖vectorBlock x j‖)
  apply le_of_sq_le_sq _ (by positivity)
  rw [norm_sq_eq_sum_vectorBlock]
  calc
    ∑ i, ‖vectorBlock (Matrix.toEuclideanLin A x) i‖ ^ 2 ≤
        ∑ _i : ι, (q * ∑ j, ‖vectorBlock x j‖) ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2)
    _ = (Fintype.card ι : ℝ) * q ^ 2 * (∑ j, ‖vectorBlock x j‖) ^ 2 := by
      simp [mul_pow, mul_assoc]
    _ ≤ (Fintype.card ι : ℝ) * q ^ 2 *
        ((Fintype.card ι : ℝ) * ∑ j, ‖vectorBlock x j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = ((Fintype.card ι : ℝ) * q * ‖x‖) ^ 2 := by
      rw [← norm_sq_eq_sum_vectorBlock]
      ring

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
-- Preserve the existing parameter list for downstream callers.
theorem block_diagonal_mul (D : ∀ i, Matrix (d i) (d i) ℂ)
    (A : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (Matrix.blockDiagonal' D * A) i j = D i * block A i j := by
  ext a b
  simp only [block, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single i]
  · simp
  · intro k hki
    apply Finset.sum_eq_zero
    intro c _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hki.symm, zero_mul]

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
-- Preserve the existing parameter list for downstream callers.
theorem block_mul_diagonal (D : ∀ i, Matrix (d i) (d i) ℂ)
    (A : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (A * Matrix.blockDiagonal' D) i j = block A i j * D j := by
  ext a b
  simp only [block, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single j]
  · simp
  · intro k hkj
    apply Finset.sum_eq_zero
    intro c _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkj, mul_zero]

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
-- Preserve the existing parameter list for downstream callers.
@[simp]
theorem block_add (A B : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (A + B) i j = block A i j + block B i j := rfl

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
-- Preserve the existing parameter list for downstream callers.
@[simp]
theorem block_sub (A B : Matrix (Sigma d) (Sigma d) ℂ) (i j : ι) :
    block (A - B) i j = block A i j - block B i j := rfl

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
-- Preserve the existing parameter list for downstream callers.
@[simp]
theorem block_diagonal_same (D : ∀ i, Matrix (d i) (d i) ℂ) (i : ι) :
    block (Matrix.blockDiagonal' D) i i = D i := by
  ext a b
  exact Matrix.blockDiagonal'_apply_eq D i a b

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
-- Preserve the existing parameter list for downstream callers.
theorem block_diagonal_ne (D : ∀ i, Matrix (d i) (d i) ℂ) (i j : ι) (h : i ≠ j) :
    block (Matrix.blockDiagonal' D) i j = 0 := by
  ext a b
  exact Matrix.blockDiagonal'_apply_ne D a b h

set_option maxHeartbeats 2000000 in
-- Retain the original elaboration budget locally for this declaration.
/-- Inverse rescaling makes the first commutator factor small at no product cost.-/
theorem normalize_factors {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℂ) (p : ℝ) (hp : 0 ≤ p) (hcost : ‖U‖ * ‖V‖ ≤ p) :
    ∃ U' V' : Matrix n n ℂ,
      U' * V' - V' * U' = U * V - V * U ∧ ‖U'‖ ≤ 1 / 4 ∧ ‖V'‖ ≤ 4 * p := by
  by_cases hU : U = 0
  · refine ⟨0, 0, by simp [hU], by norm_num, ?_⟩
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hp
  have hUn : 0 < ‖U‖ := norm_pos_iff.mpr hU
  let c : ℂ := (4 * ‖U‖ : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 4) hUn)
  have hcnorm : ‖c‖ = 4 * ‖U‖ := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  refine ⟨c⁻¹ • U, c • V, ?_, ?_, ?_⟩
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, one_smul, one_smul]
  · rw [norm_smul, norm_inv, hcnorm]
    have hne : ‖U‖ ≠ 0 := ne_of_gt hUn
    field_simp
    nlinarith
  · rw [norm_smul, hcnorm]
    nlinarith

end BlockAssembly
end NoEpsilon
