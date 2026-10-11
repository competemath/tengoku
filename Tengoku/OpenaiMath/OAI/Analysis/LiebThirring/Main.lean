import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.ExtremizerMass

namespace OAI

noncomputable section
namespace SharpLiebThirring
open MeasureTheory Set ExtremizerProof

lemma sharp_times_extremizer_mass {γ : ℝ} (hγ : 1/2 < γ) :
    ENNReal.ofReal (sharpConstant γ)*potentialMass γ (equalityPotential γ) = 1 := by
  rw [(equalityPotential_admissible hγ).mass_eq_ofReal hγ,
    ← ENNReal.ofReal_mul (sharpConstant_pos hγ).le,
    sharp_times_extremizer_integral hγ,ENNReal.ofReal_one]

lemma sharp_le_oneStateConstant {γ : ℝ} (hγ : 1/2 < γ) :
    ENNReal.ofReal (sharpConstant γ) ≤ oneStateConstant γ := by
  have hr : 0 < (γ-1/2)⁻¹ := inv_pos.mpr (by linarith)
  have hW := equalityPotential_admissible hγ
  have hpos : 0 < potentialMass γ (equalityPotential γ) := potential_mass_pos hr
  have hle : ENNReal.ofReal (sharpConstant γ) ≤
      oneStateMoment γ (equalityPotential γ) / potentialMass γ (equalityPotential γ) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl (hW.mass_ne_top hγ))).mpr
    rw [sharp_times_extremizer_mass hγ]
    exact one_le_oneStateMoment hr γ
  unfold oneStateConstant
  exact hle.trans (le_iSup_of_le (equalityPotential γ)
    (le_iSup_of_le hW (le_iSup_of_le hpos le_rfl)))

end SharpLiebThirring

end

end OAI
