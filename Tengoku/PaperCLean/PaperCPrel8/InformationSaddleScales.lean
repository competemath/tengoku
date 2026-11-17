import Tengoku.PaperCLean.PaperCPrel8.InformationSaddleBudget
import Tengoku.PaperCLean.PaperCV282.SaddleScales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Uniform analytic scales of the information-adapted crossing -/
namespace PaperC.Prel8.InformationSaddleScales
open Set Filter Topology
open PaperC.V282.SaddleParameters PaperC.V282.SaddleBranch
open PaperC.V282.SaddleAsymptotics PaperC.V282.SaddleExpansion PaperC.V282.SaddleScales
open PaperC.Prel8.InformationSaddleBudget
noncomputable section

def informationParameter (H I : ℝ) : ℝ := upperSaddleBranch (H/informationCutoff H I)

/-- The actual intermediate parameter lies between the two existing saddle parameters.
@isnad1 id=and.3h2v.s6.0043c50cf340 from=translated src=- shape=c6be6103 vocab=27d69245
-/
theorem parameter_bounds {H I : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H) :
    saddleParameter 2 H ≤ informationParameter H I ∧ informationParameter H I ≤ saddleParameter 1 H := by
  have hs := cutoff_spec hH hI hIV
  have hp := cutoff_pos hH hI hIV
  have hH1 := (le_max_left _ _).trans hH
  have hH2 := (le_max_right _ _).trans hH
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH1
  have hd := saddleCutoff_domain (by norm_num : (0:ℝ)<2) hH2
  have hl := div_le_div_of_nonneg_left hHp.le hp hs.1.2
  have hu := div_le_div_of_nonneg_left hHp.le (saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH1) hs.1.1
  have hleft := strictMonoOn_upperSaddleBranch.monotoneOn hd (hd.trans hl) hl
  have hright := strictMonoOn_upperSaddleBranch.monotoneOn (hd.trans hl) (hd.trans (hl.trans hu)) hu
  rw [upperSaddleBranch_div_saddleCutoff (by norm_num : (0:ℝ)<2) hH2] at hleft
  rw [upperSaddleBranch_div_saddleCutoff (by norm_num : (0:ℝ)<1) hH1] at hright
  exact ⟨hleft,hright⟩

/-- Along any admissible information profile, the parameter escapes to infinity.
@isnad1 id=tendsto.1h1v.s5.c629845c45f0 from=translated src=- shape=cbb0bd6a vocab=696cea29
-/
theorem parameter_tendsto_atTop (I : ℝ → ℝ)
    (hI : ∀ᶠ H in atTop, 0 ≤ I H ∧ I H ≤ saddleCutoff 1 H) :
    Tendsto (fun H => informationParameter H (I H)) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (tendsto_saddleParameter_atTop (by norm_num : (0:ℝ)<2))
  filter_upwards [eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)),hI] with H hH hi
  exact (parameter_bounds hH hi.1 hi.2).1

/-- No limit assumption on I/V is needed for the leading saddle parameter.
@isnad1 id=tendsto.1h1v.s6.e1b90104f412 from=translated src=- shape=1c7ca9f4 vocab=b340b599
-/
theorem parameter_div_log_tendsto (I : ℝ → ℝ)
    (hI : ∀ᶠ H in atTop, 0 ≤ I H ∧ I H ≤ saddleCutoff 1 H) :
    Tendsto (fun H => informationParameter H (I H)/Real.log H) atTop (𝓝 (1/2)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_saddleParameter_div_log (by norm_num : (0:ℝ)<2))
    (tendsto_saddleParameter_div_log (by norm_num : (0:ℝ)<1))
  · filter_upwards [eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)),eventually_gt_atTop (1:ℝ),hI] with H hH hp hi
    exact div_le_div_of_nonneg_right (parameter_bounds hH hi.1 hi.2).1 (Real.log_pos hp).le
  · filter_upwards [eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)),eventually_gt_atTop (1:ℝ),hI] with H hH hp hi
    exact div_le_div_of_nonneg_right (parameter_bounds hH hi.1 hi.2).2 (Real.log_pos hp).le

/-- The exact information saddle satisfies a quadratic identity before taking limits.
@isnad1 id=eq.3h2v.s7.fab57d6a5797 from=translated src=- shape=bfea7631 vocab=e0bb91f3
-/
theorem quadratic_identity {H I : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H) :
    (informationCutoff H I)^2+I*informationCutoff H I =
      2*H*(informationParameter H I-normalizedExponentialIntegral (informationParameter H I)) := by
  have hs := cutoff_spec hH hI hIV
  have hp := cutoff_pos hH hI hIV
  have hH1 := (le_max_left _ _).trans hH
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH1
  have hd := (saddleCutoff_domain (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)).trans
    (div_le_div_of_nonneg_left hHp.le hp hs.1.2)
  have hu : 0 < informationParameter H I := upperSaddleBranch_pos hd
  have he : Real.exp (informationParameter H I)=(H/informationCutoff H I)*informationParameter H I := exp_upperSaddleBranch hd
  have hc : saddleCost (H/informationCutoff H I)=
      (H/informationCutoff H I)*(informationParameter H I-normalizedExponentialIntegral (informationParameter H I)) := by
    unfold saddleCost normalizedExponentialIntegral
    change (H/informationCutoff H I)*informationParameter H I-
      PaperC.V282.ExponentialIntegral.exponentialIntegral (informationParameter H I) = _
    rw [he]
    field_simp
  rw [hc] at hs
  have hh := congrArg (fun z : ℝ => z*informationCutoff H I) hs.2
  field_simp at hh
  nlinarith

/-- The normalized quadratic has a limit uniform over all admissible information profiles.
@isnad1 id=tendsto.1h1v.s6.2db9f65315b1 from=translated src=- shape=094bbb24 vocab=afc9577e
-/
theorem quadratic_normalized_tendsto (I : ℝ → ℝ)
    (hI : ∀ᶠ H in atTop, 0 ≤ I H ∧ I H ≤ saddleCutoff 1 H) :
    Tendsto (fun H => ((informationCutoff H (I H))^2+I H*informationCutoff H (I H))/(H*Real.log H))
      atTop (𝓝 1) := by
  have he := (tendsto_normalizedExponentialIntegral.comp (parameter_tendsto_atTop I hI)).div_atTop Real.tendsto_log_atTop
  have h := ((parameter_div_log_tendsto I hI).sub he).const_mul 2
  have ht : Tendsto (fun H => 2*(informationParameter H (I H)/Real.log H-
      normalizedExponentialIntegral (informationParameter H (I H))/Real.log H)) atTop (𝓝 1) := by
    convert h using 1 <;> norm_num
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)),eventually_gt_atTop (1:ℝ),hI] with H hH hp hi
  rw [quadratic_identity hH hi.1 hi.2]
  field_simp

end
end PaperC.Prel8.InformationSaddleScales
