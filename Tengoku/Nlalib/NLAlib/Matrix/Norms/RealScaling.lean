import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Named spectral norms under real dilation -/

namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Real scaling multiplies the native spectral norm by its absolute value.
@isnad1 id=eq.0h5v.s6.8f6e717586f0 from=translated src=- shape=6e643242 vocab=055eab7e
-/
theorem specNorm_real_smul (c : ℝ) (A : Matrix m n 𝕜) :
    specNorm (c•A)=|c| * specNorm A := by
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), specNorm_eq_norm,
    norm_smul, RCLike.norm_ofReal]

/-- A positive supplied norm bound normalizes a rectangular matrix to a contraction.
@isnad1 id=le.2h5v.s7.8e1824bfae9b from=translated src=- shape=5f571fba vocab=8ad04786
-/
theorem specNorm_inv_smul_le_one {A : Matrix m n 𝕜} {S : ℝ}
    (hS : 0 < S) (hbound : specNorm A ≤ S) : specNorm (S⁻¹•A) ≤ 1 := by
  rw [specNorm_real_smul, abs_of_nonneg (inv_nonneg.mpr hS.le)]
  calc
    _ ≤ S⁻¹*S := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hS.le)
    _ = 1 := inv_mul_cancel₀ hS.ne'

end NLAlib
