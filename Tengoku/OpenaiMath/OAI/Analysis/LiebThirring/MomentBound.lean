import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.ComplexFamilies

namespace OAI

noncomputable section
namespace SharpLiebThirring
open MeasureTheory Set
open SobolevProof SobolevProof.C1L2 SpectralProof ConstantProof

lemma Admissible.locallyIntegrable {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) : LocallyIntegrable W volume := by
  apply hW.2.locallyIntegrable
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

lemma Admissible.integrable_rpow {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) :
    Integrable (fun x ↦ W x^(γ+1/2)) := by
  have hp : 0 < γ+1/2 := by linarith
  have hh := hW.2.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at hh
  apply hh.congr
  filter_upwards [hW.1] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg hx]

lemma Admissible.mass_eq_ofReal {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) :
    potentialMass γ W = ENNReal.ofReal (∫ x, W x^(γ+1/2)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hW.integrable_rpow hγ)]
  · apply lintegral_congr_ae
    filter_upwards [hW.1] with x hx
    exact ENNReal.ofReal_rpow_of_nonneg hx (by linarith)
  · filter_upwards [hW.1] with x hx
    exact Real.rpow_nonneg hx _

lemma Admissible.mass_ne_top {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) : potentialMass γ W ≠ ⊤ := by
  rw [hW.mass_eq_ofReal hγ]
  exact ENNReal.ofReal_ne_top

lemma sharpConstant_pos {γ : ℝ} (hγ : 1/2 < γ) : 0 < sharpConstant γ := by
  have hσ : 0 < γ-1/2 := by linarith
  have he := action_constant_eq_sharp hσ
  rw [sub_add_cancel] at he
  rw [← he]
  apply div_pos _ (betaAction_pos hσ)
  unfold actionYoungConstant
  positivity

end SharpLiebThirring

end

end OAI
