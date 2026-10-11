import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.Regular
import Tengoku

namespace OAI

/-! Finite-average identities for contracting averages in Hilbert spaces. -/
noncomputable section
namespace Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite Hilbert-space variance identity, without normalization. -/
theorem sum_pairwise_sq (S : Finset I) (v : I → H) :
    ∑ i ∈ S, ∑ j ∈ S, ‖v i - v j‖ ^ 2 =
      2 * (S.card : ℝ) * (∑ i ∈ S, ‖v i‖ ^ 2) - 2 * ‖∑ i ∈ S, v i‖ ^ 2 := by
  have hs : (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) =
      ‖∑ i ∈ S, v i‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ]
    simp only [sum_inner, inner_sum, map_sum]
    exact Finset.sum_comm
  simp_rw [@norm_sub_sq ℂ H]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [← Finset.mul_sum]
  change _ - 2 * (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) + _ = _
  rw [hs]
  ring

omit [InnerProductSpace ℂ H] in
/-- A chosen pair contributes at most the total squared defect. -/
theorem pairwise_sq_le_sum (S : Finset I) (v : I → H) {i j : I}
    (hi : i ∈ S) (hj : j ∈ S) :
    ‖v i - v j‖ ^ 2 ≤ ∑ a ∈ S, ∑ b ∈ S, ‖v a - v b‖ ^ 2 := by
  exact (Finset.single_le_sum (fun b _ => sq_nonneg ‖v i - v b‖) hj).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (s := S) (fun b _ => sq_nonneg ‖v a - v b‖)) hi)

variable {G : Type*} [Group G]

/-- A norm-one vector witnessing any strict lower bound for an operator norm. -/
theorem exists_unit_near_opNorm (A : H →L[ℂ] H) {c : ℝ}
    (hc : 0 ≤ c) (hA : c < ‖A‖) : ∃ ξ : H, ‖ξ‖ = 1 ∧ c < ‖A ξ‖ := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hA) (ContinuousLinearMap.opNorm_le_of_unit_norm hc h)

end Dixmier

end

end OAI
