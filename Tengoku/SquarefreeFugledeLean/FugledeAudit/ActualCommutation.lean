import Tengoku.SquarefreeFugledeLean.FugledeAudit.ActualIntegralGram

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FugledeAudit

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem local_eigen_space_eq_level_of_residual_eq_bot
    (T : End ℂ E) (L : Submodule ℂ E) (ω : ℂ) (q : ℕ)
    (h : localResidual T L ω q = ⊥) : localEigenSpace T L ω q = L := by
  apply le_antisymm (local_eigen_space_le_level T L ω q)
  intro v hv
  let W := localEigenSpace T L ω q
  have hp : W.starProjection v ∈ L :=
    local_eigen_space_le_level T L ω q (W.starProjection_apply_mem v)
  have hr : v - W.starProjection v ∈ localResidual T L ω q := by
    refine ⟨L.sub_mem hv hp, ?_⟩
    exact W.sub_starProjection_mem_orthogonal v
  rw [h] at hr
  have he : v = W.starProjection v := sub_eq_zero.mp hr
  rw [he]
  exact W.starProjection_apply_mem v

theorem reducing_map_commutes_projection
    (T : End ℂ E) (L : Submodule ℂ E)
    (hL : ∀ x, x ∈ L → T x ∈ L)
    (hO : ∀ x, x ∈ Lᗮ → T x ∈ Lᗮ) :
    L.starProjection.toLinearMap * T = T * L.starProjection.toLinearMap := by
  apply LinearMap.ext
  intro v
  change L.starProjection (T v) = T (L.starProjection v)
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (hL _ (L.starProjection_apply_mem v))
  rw [← map_sub]
  exact hO _ (L.sub_starProjection_mem_orthogonal v)

omit [FiniteDimensional ℂ E] in
theorem commuting_map_commutes_average
    (Q T : End ℂ E) (h : Q * T = T * Q) (q : ℕ) (c : Fin q → ℂ) :
    Q * averagedPowers T q c = averagedPowers T q c * Q := by
  have hp (n : ℕ) : Q * T ^ n = T ^ n * Q := (Commute.pow_right h n).eq
  simp only [averagedPowers, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, hp]

end FugledeAudit
