import Tengoku.Nlalib.NLAlib.Matrix.Spectral.Core
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SingularValueSpectrum
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Reindex
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extreme singular values and the spectral norm

The extreme singular values on arbitrary finite index types: `singularValues_zero_eq_specNorm`
(`σ₀ = ‖A‖₂`), `singularValues_le_specNorm`, `specNorm_sq_eq_specNorm_conjTranspose_mul_self`
(`‖A‖₂² = ‖AᴴA‖₂`), the Gram-error identity `specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one`
and `singularValues_last_pos_iff_rank_eq_card` (the last singular value is positive exactly at
full column rank). Source: Horn–Johnson 2013, §2.6 and §5.6. Atlas: `svd`, `norms-frob-spec`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The spectral norm squared is the norm of the Gram matrix `AᴴA`, over `ℝ` or `ℂ`, including
empty dimensions. Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec-/
theorem specNorm_sq_eq_specNorm_conjTranspose_mul_self {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix m n 𝕜) : specNorm A ^ 2 = specNorm (Aᴴ * A) := by
  open scoped Matrix.Norms.L2Operator in unfold specNorm
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self]

/-- `‖A‖₂² = ‖AᵀA‖₂` for a real matrix (`specNorm_sq_eq_specNorm_conjTranspose_mul_self` at `ℝ`).
Kept for the real consumers of the transpose spelling.-/
theorem specNorm_sq_eq_specNorm_transpose_mul_self (A : Matrix m n ℝ) :
    specNorm A ^ 2 = specNorm (Aᵀ * A) := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact specNorm_sq_eq_specNorm_conjTranspose_mul_self A

end NLAlib

namespace NLAlib

end NLAlib

namespace NLAlib

end NLAlib
