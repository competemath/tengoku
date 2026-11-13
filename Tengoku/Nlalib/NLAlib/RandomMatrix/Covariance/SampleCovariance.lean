import Tengoku.Nlalib.NLAlib.Matrix.Structured.RankOneCovariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sample covariance and whitening

The empirical second-moment matrix of a finite vector family is positive
semidefinite and transforms by congruence. Positive-definite covariance can be
whitened by its actual inverse square root, and a lower Loewner bound transports
back exactly. These deterministic bridges support fourth-moment covariance
estimation, Tropp (2026), Theorem 3.3.
-/

noncomputable section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-- The empirical second moment of a finite vector family, normalized by
its sample count. For an empty sample family the value is zero.-/
def sampleCovariance (X : ι → d → 𝕜) : Matrix d d 𝕜 :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ k, vecMulVec (X k) (star (X k))

omit [DecidableEq d] in
/-- Every finite empirical covariance matrix is positive semidefinite.
@isnad1 id=possemid.0h4v.s5.225684dfeb28 from=translated src=- shape=cd3a6db7 vocab=0f52d72b
-/
theorem posSemidef_sampleCovariance (X : ι → d → 𝕜) :
    (sampleCovariance X).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (by positivity)
  exact Matrix.posSemidef_sum _ (fun k _ => posSemidef_vecMulVec_self_star (X k))

omit [DecidableEq d] in
/-- Applying a linear map to every sample transforms the empirical
covariance by the same congruence.
@isnad1 id=eq.0h6v.s7.507ee9f226a2 from=translated src=- shape=0f5b4799 vocab=d2714595
-/
theorem sampleCovariance_mulVec {m : Type*} [Fintype m] [DecidableEq m]
    (S : Matrix m d 𝕜) (X : ι → d → 𝕜) :
    sampleCovariance (fun k => S *ᵥ X k) = S * sampleCovariance X * Sᴴ := by
  simp only [sampleCovariance, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul, vecMulVec_mulVec_star_mulVec]

/-- An invertible whitening map identifies the lower relative covariance
bound with its isotropic version.
@isnad1 id=iff.2h7v.s9.9c7036d079ca from=translated src=- shape=8a4a63c7 vocab=bab01d16
-/
theorem smul_le_sampleCovariance_iff_whitened
    {K S : Matrix d d 𝕜} (hS : IsUnit S) (hwhite : S * K * Sᴴ = 1)
    (X : ι → d → 𝕜) (a : ℝ) :
    a • K ≤ sampleCovariance X ↔
      a • (1 : Matrix d d 𝕜) ≤ sampleCovariance (fun k => S *ᵥ X k) := by
  rw [sampleCovariance_mulVec, Matrix.le_iff, Matrix.le_iff]
  have heq : S * (sampleCovariance X - a • K) * Sᴴ =
      S * sampleCovariance X * Sᴴ - a • (1 : Matrix d d 𝕜) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hwhite]
  rw [← heq]
  exact hS.posSemidef_star_right_conjugate_iff.symm

end NLAlib
