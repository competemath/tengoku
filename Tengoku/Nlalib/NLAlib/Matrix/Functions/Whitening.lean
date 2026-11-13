import Tengoku.Nlalib.NLAlib.Matrix.Functions.GeometricMean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An actual positive-definite whitening map

The inverse square root constructs an invertible congruence carrying a
positive-definite matrix to the identity, over real or complex scalars.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix.PosDef

/-- The inverse square root provides an actual invertible whitening map
for every positive-definite real or complex matrix.
@isnad1 id=ex.1h3v.s8.fec41a726af6 from=translated src=- shape=849de9d0 vocab=295e4c3b
-/
theorem exists_isUnit_whitening
    {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] [DecidableEq d]
    {K : Matrix d d 𝕜} (hK : K.PosDef) :
    ∃ S : Matrix d d 𝕜, IsUnit S ∧ S * K * Sᴴ = 1 := by
  let S := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) K
  let T := cfc Real.sqrt K
  have hST : S * T = 1 := NLAlib.cfc_inv_sqrt_mul_sqrt hK
  have hTS : T * S = 1 := NLAlib.cfc_sqrt_mul_inv_sqrt hK
  have hS : IsUnit S := ⟨⟨S, T, hST, hTS⟩, rfl⟩
  have hSherm : S.IsHermitian := cfc_predicate _ _
  exact ⟨S, hS, by rw [hSherm.eq]; exact NLAlib.cfc_inv_sqrt_mul_self_mul_inv_sqrt hK⟩

end Matrix.PosDef
