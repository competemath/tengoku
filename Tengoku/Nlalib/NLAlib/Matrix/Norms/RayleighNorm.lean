/- Copyright (c) 2026 Diar Heidary. Adapted under the MIT license. -/
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core
import Tengoku.Seed.Analysis.Matrix.Spectrum
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spectral norm and symmetric quadratic forms

Atlas: `ose-def`, `norms-frob-spec`.MatrixTail.Only Mathlib and NLAlib are imported; the donor probability development is
not needed. All finite index types, including empty types, are covered.
-/

noncomputable section
open scoped Matrix InnerProductSpace

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A real symmetric matrix has spectral norm at most a nonnegative `ε`
exactly when its quadratic form is bounded by `ε ‖x‖²` for every vector.
Atlas: `ose-def`, `norms-frob-spec`.MatrixTail.
@isnad1 id=iff.2h3v.s6.30fed35dce4d from=translated src=- shape=f90ebc76 vocab=4ed579da
-/
theorem specNorm_le_iff_abs_dotProduct_mulVec_le (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) :
    specNorm A ≤ ε ↔ ∀ x : n → ℝ, |x ⬝ᵥ (A *ᵥ x)| ≤ ε * (x ⬝ᵥ x) := by
  constructor
  · intro h x
    exact (abs_dotProduct_mulVec_le_specNorm A x).trans
      (mul_le_mul_of_nonneg_right h (dotProduct_self_nonneg x))
  · intro hquad
    let T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) A
    have hT : (T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).IsSymmetric := by
      change (Matrix.toEuclideanLin A).IsSymmetric
      exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    change ‖T‖ ≤ ε
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hε
    · have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      rw [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
        abs_of_nonneg hxpos.le]
      apply (div_le_iff₀ hxpos).2
      have hnorm : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [dotProduct, sq]
      simpa [T, real_inner_comm, Matrix.inner_toEuclideanCLM,
        hnorm] using hquad x.ofLp

end NLAlib
