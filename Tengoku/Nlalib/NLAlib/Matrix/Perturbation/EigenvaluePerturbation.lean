import Tengoku.Nlalib.NLAlib.Matrix.Spectral.CourantFischer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Signed eigenvalue perturbation bounds

Weyl's two-sided eigenvalue bounds preserve the signs of the sorted eigenvalues.
Source: Horn–Johnson 2013, Theorem 4.3.1 and Corollary 4.3.15.
Atlas: `eigenvalue-perturbation-symmetric`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Every signed eigenvalue of a real symmetric matrix is bounded in absolute
value by its spectral norm. Horn–Johnson 2013, Section 5.6.
@isnad1 id=le.1h3v.s6.c746bf4a915c from=translated src=- shape=86b65610 vocab=ae10774a
-/
theorem abs_eigenvalues_le_specNorm {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    |hA.eigenvalues i| ≤ specNorm A := by
  have h := Matrix.l2_opNorm_mulVec A (hA.eigenvectorBasis i)
  have hm : (EuclideanSpace.equiv n ℝ).symm (A *ᵥ ⇑(hA.eigenvectorBasis i)) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    rw [hA.mulVec_eigenvectorBasis]
    rfl
  simpa only [hm, norm_smul, Real.norm_eq_abs, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, specNorm] using h

open scoped Matrix.Norms.L2Operator in
/-- Sorted signed eigenvalues have absolute value at most the spectral norm.
Horn–Johnson 2013, Section 5.6; supports `eigenvalue-perturbation-symmetric`.
@isnad1 id=le.1h3v.s6.e61e950bd4e4 from=translated src=- shape=1ec8ed31 vocab=436cba3a
-/
theorem abs_eigenvalues₀_le_specNorm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card n)) : |hA.eigenvalues₀ i| ≤ specNorm A := by
  have h := abs_eigenvalues_le_specNorm hA
    (Fintype.equivOfCardEq (Fintype.card_fin _) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

/-- A symmetric quadratic form is bounded above by its largest eigenvalue.
Horn–Johnson 2013, Theorem 4.2.2; supports signed eigenvalue perturbation.
@isnad1 id=le.2h3v.s6.2b5841a870b4 from=translated src=- shape=3a6bbf21 vocab=b1a631be
-/
theorem dotProduct_mulVec_le_eigenvalues₀_zero_mul {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hcard : 0 < Fintype.card n) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ ⟨0, hcard⟩ * (x ⬝ᵥ x) := by
  rw [show x ⬝ᵥ (A *ᵥ x) = quadForm A x from rfl, quadForm_eq_sum_eigenvalues hA,
    ← sum_sq_eigenvectorBasis_dotProduct hA x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact hA.eigenvalues₀_antitone (show (⟨0, hcard⟩ : Fin (Fintype.card n)) ≤
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i from Nat.zero_le _)

/-- A symmetric quadratic form is bounded below by its smallest eigenvalue.
Horn–Johnson 2013, Theorem 4.2.2; no sign condition on the matrix.
@isnad1 id=le.2h3v.s7.f0592ed40c94 from=translated src=- shape=8a62f7d0 vocab=e8bdd453
-/
theorem eigenvalues₀_last_mul_le_dotProduct_mulVec {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hcard : 0 < Fintype.card n) (x : n → ℝ) :
    hA.eigenvalues₀ ⟨Fintype.card n - 1, by omega⟩ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rw [show x ⬝ᵥ (A *ᵥ x) = quadForm A x from rfl, quadForm_eq_sum_eigenvalues hA,
    ← sum_sq_eigenvectorBasis_dotProduct hA x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply hA.eigenvalues₀_antitone
  exact Nat.le_pred_of_lt ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).isLt

open scoped Matrix.Norms.L2Operator in
/-- Weyl's signed eigenvalue perturbation bound, upper side.
Horn–Johnson 2013, Theorem 4.3.1. Indices are decreasing and zero-indexed.
atlas: eigenvalue-perturbation-symmetric
@isnad1 id=le.2h4v.s7.58a1d57b5801 from=translated src=- shape=9602980e vocab=6bdf845e
-/
theorem eigenvalues₀_add_le_add_eigenvalues₀_zero {A E : Matrix n n ℝ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (i : Fin (Fintype.card n)) :
    (hA.add hE).eigenvalues₀ i ≤ hA.eigenvalues₀ i +
      hE.eigenvalues₀ ⟨0, by have := i.isLt; omega⟩ := by
  simpa only [Nat.add_zero, Fin.eta] using
    Matrix.IsHermitian.eigenvalues₀_add_le hA hE i ⟨0, by have := i.isLt; omega⟩
      (by have := i.isLt; omega)

open scoped Matrix.Norms.L2Operator in
/-- Weyl's signed eigenvalue perturbation bound, lower side.
Horn–Johnson 2013, Theorem 4.3.1. No positivity or simple-spectrum assumption.
atlas: eigenvalue-perturbation-symmetric
@isnad1 id=le.2h4v.s7.42d4bce40dbb from=translated src=- shape=8aef4d90 vocab=42081b15
-/
theorem add_eigenvalues₀_last_le_eigenvalues₀_add {A E : Matrix n n ℝ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i + hE.eigenvalues₀ ⟨Fintype.card n - 1, by have := i.isLt; omega⟩ ≤
      (hA.add hE).eigenvalues₀ i := by
  obtain ⟨S, hS, hAS⟩ := Matrix.IsHermitian.exists_submodule_eigenvalues₀_mul_le hA i
  refine Matrix.IsHermitian.le_eigenvalues₀_of_forall_mem (hA.add hE) i S hS fun x hx => ?_
  have h₁ := hAS x hx
  have h₂ := eigenvalues₀_last_mul_le_dotProduct_mulVec hE (by have := i.isLt; omega) x
  simp only [quadForm_def, RCLike.re_to_real, star_trivial] at h₁ ⊢
  rw [Matrix.add_mulVec, dotProduct_add]
  nlinarith

open scoped Matrix.Norms.L2Operator in
/-- Signed sorted eigenvalues are 1-Lipschitz for the spectral norm.
Horn–Johnson 2013, Corollary 4.3.15; arbitrary finite real symmetric matrices.
atlas: eigenvalue-perturbation-symmetric
@isnad1 id=le.2h4v.s7.b52756956ebf from=translated src=- shape=cc3cbd22 vocab=cc4f8a64
-/
theorem abs_eigenvalues₀_add_sub_le_specNorm {A E : Matrix n n ℝ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (i : Fin (Fintype.card n)) :
    |(hA.add hE).eigenvalues₀ i - hA.eigenvalues₀ i| ≤ specNorm E := by
  have hu := eigenvalues₀_add_le_add_eigenvalues₀_zero hA hE i
  have hl := add_eigenvalues₀_last_le_eigenvalues₀_add hA hE i
  have hmax := abs_eigenvalues₀_le_specNorm hE ⟨0, by have := i.isLt; omega⟩
  have hmin := abs_eigenvalues₀_le_specNorm hE ⟨Fintype.card n - 1,
    by have := i.isLt; omega⟩
  rw [abs_le] at hmax hmin ⊢
  constructor <;> linarith

open scoped Matrix.Norms.L2Operator in
/-- Eigenvalues at the same decreasing index differ by at most the spectral norm
of the matrix difference. Horn–Johnson 2013, Corollary 4.3.15.
atlas: eigenvalue-perturbation-symmetric (partial)
@isnad1 id=le.2h4v.s7.37cfcba2e4df from=translated src=- shape=0acd852d vocab=a7600bca
-/
theorem abs_eigenvalues₀_sub_le_specNorm_sub {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    |hB.eigenvalues₀ i - hA.eigenvalues₀ i| ≤ specNorm (B - A) := by
  have h := abs_eigenvalues₀_add_sub_le_specNorm hA (hB.sub hA) i
  simpa only [add_sub_cancel] using h

end NLAlib
