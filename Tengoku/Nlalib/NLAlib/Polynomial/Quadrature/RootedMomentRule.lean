import Tengoku.Nlalib.NLAlib.Polynomial.Quadrature.MeasureExactness
import Tengoku.Nlalib.NLAlib.Matrix.Functions.CFCQuadratic
import Tengoku.Nlalib.NLAlib.Matrix.Structured.TridiagonalSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Polynomial exactness and weights from rooted matrix moments

A real Hermitian matrix with the prescribed first-coordinate moments supplies the
actual spectral quadrature rule. Polynomial exactness is deduced from those moments;
unreduced tridiagonal structure proves its node simplicity and strict weights.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

/-- The diagonal entry of the actual functional calculus is its first-coordinate
spectral rule, without any regularity requirement on the sampled function.
@isnad1 id=eq.2h3v.s9.f1bccf99f1e5 from=translated src=- shape=15d32af2 vocab=ed6807bd
-/
theorem cfc_apply_zero_zero_eq_sum {N : ℕ} (hn : 0 < N)
    {J : Matrix (Fin N) (Fin N) ℝ} (hJ : J.IsHermitian) (f : ℝ → ℝ) :
    cfc f J ⟨0, hn⟩ ⟨0, hn⟩ =
      ∑ i, (hJ.eigenvectorBasis i ⟨0, hn⟩) ^ 2 * f (hJ.eigenvalues i) := by
  have h := dotProduct_cfc_mulVec_eq_sum hJ f (Pi.single ⟨0, hn⟩ 1)
  simpa only [dotProduct_single, single_dotProduct, one_mul, Matrix.mulVec_single,
    dotProduct_smul, op_smul_eq_mul, Matrix.col_apply, one_mul, mul_one, mul_comm] using h

/-- Rooted matrix moments imply polynomial exactness of the actual Hermitian matrix
rule, rather than being assumptions of polynomial exactness themselves.
Source: focused mathematical reroutes, Section 3 (BL3), (BL5), (BL10).
atlas: gauss-radau-lobatto (partial)
@isnad1 id=eq.5h5v.s8.25e044e33868 from=translated src=- shape=76106a60 vocab=84d6b6b4
-/
theorem integral_eval_eq_mass_mul_cfc_of_rooted_moments {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {N : ℕ} (hn : 0 < N)
    {J : Matrix (Fin N) (Fin N) ℝ} (hJ : J.IsHermitian) (d : ℕ)
    (hm : ∀ k < d, (∫ x : ℝ, x ^ k ∂μ) =
      (∫ _ : ℝ, (1 : ℝ) ∂μ) * (J ^ k) ⟨0, hn⟩ ⟨0, hn⟩)
    {p : ℝ[X]} (hp : p.degree < d) :
    (∫ x, p.eval x ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) * cfc p.eval J ⟨0, hn⟩ ⟨0, hn⟩ := by
  let L := polynomialIntegral μ hμ
  let Q : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := fun p => (∫ _ : ℝ, (1 : ℝ) ∂μ) * (aeval J p) ⟨0, hn⟩ ⟨0, hn⟩
      map_add' := by intro p q; simp [mul_add]
      map_smul' := by
        intro c p
        simp only [map_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have heq := (Polynomial.linearMap_eq_of_degree_lt_iff_pow L Q d).mpr (by
    intro k hk
    simpa only [L, Q, polynomialIntegral_apply, eval_pow, eval_X, LinearMap.coe_mk,
      AddHom.coe_mk, map_pow, aeval_X] using hm k hk)
  have h := heq p hp
  simpa only [L, Q, polynomialIntegral_apply, LinearMap.coe_mk, AddHom.coe_mk,
    cfc_polynomial p J hJ.isSelfAdjoint] using h

/-- The actual rooted spectral rule of an unreduced real Hermitian tridiagonal
matrix has distinct nodes and positive mass-scaled first-coordinate weights.
Source: focused mathematical reroutes, Section 3 (BL11).
atlas: gauss-radau-lobatto (partial)
@isnad1 id=and.5h3v.s8.cbe831287282 from=translated src=- shape=c689c9e3 vocab=9b05d050
-/
theorem rootedMatrixRule_nodes_injective_and_weights_pos {N : ℕ} (hn : 0 < N)
    {J : Matrix (Fin N) (Fin N) ℝ} (hJ : J.IsHermitian) (htri : IsTridiagonal J)
    (hsub : ∀ i j : Fin N, i.val + 1 = j.val → J i j ≠ 0)
    {mass : ℝ} (hmass : 0 < mass) :
    Function.Injective hJ.eigenvalues ∧
      ∀ i, 0 < mass * (hJ.eigenvectorBasis i ⟨0, hn⟩) ^ 2 := by
  exact ⟨hJ.eigenvalues_injective_of_unreduced htri.2 hsub,
    fun i => mul_pos hmass (sq_pos_of_ne_zero (hJ.eigenvectorBasis_apply_zero_ne_zero htri.2 hsub hn i))⟩

/-- The actual normalized first-coordinate spectral weights sum to one.
@isnad1 id=eq.2h2v.s8.a5a9ba7aa805 from=translated src=- shape=cb8feb63 vocab=b7f9b651
-/
theorem sum_sq_eigenvectorBasis_apply_zero {N : ℕ} (hn : 0 < N)
    {J : Matrix (Fin N) (Fin N) ℝ} (hJ : J.IsHermitian) :
    (∑ i, (hJ.eigenvectorBasis i ⟨0, hn⟩) ^ 2) = 1 := by
  have h := sum_sq_eigenvectorBasis_dotProduct hJ (Pi.single ⟨0, hn⟩ 1)
  simpa only [dotProduct_single, mul_one, single_dotProduct, Pi.single_eq_same,
    one_mul, one_pow] using h

/-- A positive measure with at least one support point has strictly positive mass.
Every polynomial moment is finite in the stated moment interface.
@isnad1 id=lt.2h1v.s5.e554e3a9b96e from=translated src=- shape=d386be70 vocab=a0922652
-/
theorem integral_one_pos_of_one_le_support_encard {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (hs : (1 : ℕ∞) ≤ μ.support.encard) :
    0 < ∫ _ : ℝ, (1 : ℝ) ∂μ := by
  simpa only [eval_one, one_pow] using integral_sq_eval_pos_of_le_support_encard hs
    (p := 1) one_ne_zero (by norm_num) (hμ.integrable_sq 1)

end NLAlib
