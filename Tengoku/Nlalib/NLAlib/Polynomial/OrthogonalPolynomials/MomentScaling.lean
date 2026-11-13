import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.FiniteMomentSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scaling a polynomial moment functional

A nonzero scalar changes its mass and squared bilinear norms but preserves
its canonical monic polynomials. This permits normalization of numerator and
denominator leading coefficients without assuming that they are positive.
-/

noncomputable section
open Polynomial
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- Scaling a functional scales every entry of its finite Hankel matrix.
@isnad1 id=eq.0h4v.s9.2b4a95480f68 from=translated src=- shape=e9ebb0ff vocab=0ef2028b
-/
theorem hankelMomentMatrix_smul (c : 𝕜) (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    hankelMomentMatrix (c • L) n = c • hankelMomentMatrix L n := by
  ext i j
  simp [hankelMomentMatrix]

/-- The Hankel determinant scales by the dimension's power of the scalar.
@isnad1 id=eq.0h4v.s9.b650c4ca1151 from=translated src=- shape=9806796c vocab=3583a0a2
-/
theorem hankelMomentDet_smul (c : 𝕜) (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    hankelMomentDet (c • L) n = c^n * hankelMomentDet L n := by
  rw [hankelMomentDet, hankelMomentMatrix_smul, Matrix.det_smul]
  simp only [Fintype.card_fin, hankelMomentDet]

/-- Nonzero scaling preserves the finite canonical monic polynomial.
@isnad1 id=eq.2h4v.s9.89fb71a98c7b from=translated src=- shape=18de191b vocab=34a446ce
-/
theorem monicOrthogonalPolynomial_smul (c : 𝕜) (hc : c ≠ 0) (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {n : ℕ} (hn : hankelMomentDet L n ≠ 0) :
    monicOrthogonalPolynomial (c • L) n = monicOrthogonalPolynomial L n := by
  have hcn : hankelMomentDet (c • L) n ≠ 0 := by
    rw [hankelMomentDet_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hn
  have hp := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hn
  apply (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (c • L) hcn).eq_of_hankelMomentDet_ne_zero _ hcn
  refine ⟨hp.monic, hp.natDegree_eq, ?_⟩
  intro q hq
  simp only [LinearMap.smul_apply, smul_eq_mul, hp.orthogonal q hq, mul_zero]

end NLAlib
