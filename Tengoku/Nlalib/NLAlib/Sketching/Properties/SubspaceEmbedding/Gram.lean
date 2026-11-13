import Tengoku.Nlalib.NLAlib.Sketching.Properties.SubspaceEmbedding.SubspaceEmbedding
import Tengoku.Nlalib.NLAlib.Matrix.Norms.RayleighNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# The complete Gram form of a subspace embedding

Atlas: `ose-def`. Completes the converse of NLAlib's Gram-form sufficient
condition using the symmetric quadratic-form result in `Matrix.Gram`.
The latter adapts the MIT-licensed Rayleigh proof of Diar Heidary,
Nelson-Nguyen-conjecture-upper-bound-palomar commit
`3fdbf2cbb26c10c18bc799fa63fbd3a768f6f0e2`.
All finite index types, including empty types, are covered.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {k m d : Type*} [Fintype k] [Fintype m] [Fintype d] [DecidableEq d]

/-- An embedding on an orthonormal frame controls its Gram error in spectral
norm. Atlas: `ose-def` (the previously missing converse). The distortion is
explicitly nonnegative, including for an empty frame.
atlas: ose-def
@isnad1 id=le.3h6v.s7.02860cde7a33 from=translated src=- shape=b6e22941 vocab=a6bd9457
-/
theorem specNorm_transpose_mul_self_sub_one_le_of_isSubspaceEmbedding
    {S : Matrix k m ℝ} {U : Matrix m d ℝ} (hU : HasOrthonormalCols U)
    {ε : ℝ} (hε : 0 ≤ ε) (h : IsSubspaceEmbedding S U ε) :
    specNorm ((S * U)ᵀ * (S * U) - 1) ≤ ε := by
  have hGram : (((S * U)ᵀ * (S * U) - 1) : Matrix d d ℝ).IsHermitian := by
    have hG := Matrix.isHermitian_conjTranspose_mul_self (S * U)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hG
    exact hG.sub Matrix.isHermitian_one
  apply (specNorm_le_iff_abs_dotProduct_mulVec_le _ hGram ε hε).2
  intro x
  obtain ⟨hlo, hup⟩ := (isSubspaceEmbedding_iff_of_hasOrthonormalCols hU).1 h x
  have hq : x ⬝ᵥ ((((S * U)ᵀ * (S * U) - 1) : Matrix d d ℝ) *ᵥ x) =
      ((S * U) *ᵥ x) ⬝ᵥ ((S * U) *ᵥ x) - x ⬝ᵥ x := by
    have hM := star_mulVec_dotProduct_mulVec_self (S * U) x
    simp only [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial] at hM
    rw [Matrix.sub_mulVec, dotProduct_sub, ← hM, Matrix.one_mulVec]
  rw [hq, abs_le]
  constructor <;> nlinarith

/-- Complete Gram-form equivalence for an orthonormal frame, valid also in
empty dimensions. Atlas: `ose-def`.
atlas: ose-def
@isnad1 id=iff.2h6v.s7.fba29da12bac from=translated src=- shape=bf61b05d vocab=a6bd9457
-/
theorem isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le
    {S : Matrix k m ℝ} {U : Matrix m d ℝ} (hU : HasOrthonormalCols U)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsSubspaceEmbedding S U ε ↔ specNorm ((S * U)ᵀ * (S * U) - 1) ≤ ε :=
  ⟨specNorm_transpose_mul_self_sub_one_le_of_isSubspaceEmbedding hU hε,
    isSubspaceEmbedding_of_specNorm_transpose_mul_self_sub_one_le hU⟩

end NLAlib
