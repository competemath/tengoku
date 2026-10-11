import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.ClosedUnion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uX

namespace ExactModuli

lemma unit_in_nonempty_slice {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
    (ell : X →L[ℝ] ℝ) (α : ℝ) (hs : ∃ x : X, ‖x‖ ≤ 1 ∧ α < ell x) :
    ∃ u : X, ‖u‖ = 1 ∧ α < ell u := by
  obtain ⟨x,hxn,hα⟩ := hs
  by_cases hxpos : 0 < ell x
  · have hx0 : x ≠ 0 := by intro hx; simp [hx] at hxpos
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    refine ⟨‖x‖⁻¹ • x,norm_smul_inv_norm hx0,?_⟩
    rw [map_smul, smul_eq_mul]
    exact hα.trans_le (le_mul_of_one_le_left hxpos.le ((one_le_inv₀ hnx).mpr hxn))
  · have hα0 : α < 0 := hα.trans_le (le_of_not_gt hxpos)
    obtain ⟨u,hu⟩ := exists_norm_eq X (by norm_num : (0:ℝ)≤1)
    by_cases hu0 : 0 ≤ ell u
    · exact ⟨u,hu,hα0.trans_le hu0⟩
    · exact ⟨-u,by simpa using hu,by simpa using hα0.trans (neg_pos.mpr (lt_of_not_ge hu0))⟩

end ExactModuli

namespace ExactModuli.KW

end ExactModuli.KW

end

end OAI
