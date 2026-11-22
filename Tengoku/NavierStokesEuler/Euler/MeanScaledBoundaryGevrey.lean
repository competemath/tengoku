import Tengoku.NavierStokesEuler.Euler.MeanBoundaryGevrey
import Tengoku.NavierStokesEuler.Euler.MeanScaledCutoff
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The source boundary operator has uniform Gevrey bounds under physical cutoff rescaling. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  EulerMeanCutoffCurl EulerGevrey
open scoped ContDiff

def cutoffUnitBallFactor : ℝ := (Real.pi * 4 / 3) ^ (1/3 : ℝ)

/--
@isnad1 id=le.0h0v.s3.49192e7d929c from=translated src=- shape=ff3a10fc vocab=612445eb
-/
theorem cutoffUnitBallFactor_nonneg : 0 ≤ cutoffUnitBallFactor := by
  unfold cutoffUnitBallFactor
  positivity

/--
@isnad1 id=eq.1h1v.s9.f0d1413191d9 from=translated src=- shape=774d908a vocab=466bd273
-/
theorem closedBall_volume_oneThird (R : ℝ) (hR : 0 ≤ R) :
    (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ) = R * cutoffUnitBallFactor := by
  rw [EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal (by positivity),
    Real.mul_rpow (pow_nonneg hR 3) (by positivity), ← Real.rpow_natCast_mul hR]
  norm_num [cutoffUnitBallFactor]

def scaledCutoffGevreySize : ℝ := (9 * (1 + 3 / EulerGevreyCutoff.bumpMass)^2)^3

/--
@isnad1 id=le.0h0v.s3.20cad789d102 from=translated src=- shape=ff3a10fc vocab=4123c26e
-/
theorem scaledCutoffGevreySize_nonneg : 0 ≤ scaledCutoffGevreySize := by
  unfold scaledCutoffGevreySize
  positivity

/-- The exact scaling factor is retained, so the L³ derivative term will cancel the support radius.
@isnad1 id=le.1h3v.s9.2630328c43f2 from=translated src=- shape=f925cf19 vocab=54e74ccd
-/
theorem scaledCutoff_scaledRadiusGevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (scaledCutoff ℓ hℓ).field x‖ ≤
      scaledCutoffGevreySize * majorant (256*ℓ) 0 n := by
  change ‖iteratedFDeriv ℝ n (fun y => EulerSpatialCutoffs.outerCutoff (ℓ • y)) x‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul ℓ
    (EulerSpatialCutoffs.outerCutoff_contDiff.of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hℓ.le n)]
  have H := mul_le_mul_of_nonneg_left (EulerSpatialCutoffs.outerCutoff_gevrey n (ℓ • x))
    (pow_nonneg hℓ.le n)
  apply H.trans_eq
  unfold scaledCutoffGevreySize majorant
  simp only [Nat.add_zero, mul_pow]
  ring

/--
@isnad1 id=le.1h1v.s7.e1a13adf40a9 from=translated src=- shape=32e0f1d2 vocab=7ad6fb05
-/
theorem scaledCutoff_support_ball (ℓ : ℝ) (hℓ : 0 < ℓ) :
    tsupport (scaledCutoff ℓ hℓ).field ⊆ Metric.closedBall (0 : Space) (2*ℓ⁻¹) := by
  intro x hx
  have H := scaledCutoff_support ℓ hℓ hx
  change ‖ℓ • x‖ ≤ 2 at H
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at H
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hℓ.le)
  simp only [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul] at H'
  simpa only [Metric.mem_closedBall, dist_zero_right, mul_comm] using H'

/-- This is one fixed dimensional constant, independent of the physical scale. -/
def scaledCutoffOperatorAmplitude : ℝ :=
  3 * cutoffCurlConstant * scaledCutoffGevreySize * (1 + 512 * cutoffUnitBallFactor)

/--
@isnad1 id=le.0h0v.s3.1e09b85ac780 from=translated src=- shape=ff3a10fc vocab=06eb8c1f
-/
theorem scaledCutoffOperatorAmplitude_nonneg : 0 ≤ scaledCutoffOperatorAmplitude := by
  unfold scaledCutoffOperatorAmplitude
  have h₁ := cutoffCurlConstant_pos.le
  have h₂ := scaledCutoffGevreySize_nonneg
  have h₃ := cutoffUnitBallFactor_nonneg
  positivity

/--
@isnad1 id=eq.1h1v.s5.3bb3c13474a2 from=translated src=- shape=2a14ebed vocab=e338a866
-/
theorem scaledCutoff_amplitude (ℓ : ℝ) (hℓ : 0 < ℓ) :
    cutoffGevreyAmplitude (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize =
      scaledCutoffOperatorAmplitude := by
  unfold cutoffGevreyAmplitude scaledCutoffOperatorAmplitude
  rw [closedBall_volume_oneThird (2*ℓ⁻¹) (by positivity)]
  rw [show (256*ℓ) * (2*ℓ⁻¹ * cutoffUnitBallFactor) =
    512 * (ℓ*ℓ⁻¹) * cutoffUnitBallFactor by ring, mul_inv_cancel₀ hℓ.ne', mul_one]

/--
@isnad1 id=le.2h2v.s6.91f9dfe5e987 from=translated src=- shape=aa4afd34 vocab=0a37d379
-/
theorem scaled_majorant_le (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) :
    majorant (4*(256*ℓ)) 0 n ≤ majorant 1024 0 n := by
  unfold majorant
  simp only [Nat.add_zero]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (by positivity) (by linarith) n

/--
@isnad1 id=le.2h3v.s21.c32081119792 from=translated src=- shape=aef21607 vocab=52c8e30f
-/
theorem scaledCutoffCurl_gevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => cutoffCurl ((scaledCutoff ℓ hℓ).translate b)) a‖ ≤
      scaledCutoffOperatorAmplitude * majorant 1024 0 n := by
  have H := cutoffCurl_gevrey (scaledCutoff ℓ hℓ) (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize
    (by positivity) scaledCutoffGevreySize_nonneg (scaledCutoff_support_ball ℓ hℓ)
    (scaledCutoff_scaledRadiusGevrey ℓ hℓ) n a
  rw [scaledCutoff_amplitude ℓ hℓ] at H
  exact H.trans (mul_le_mul_of_nonneg_left (scaled_majorant_le ℓ hℓ.le hℓ1 n)
    scaledCutoffOperatorAmplitude_nonneg)

/--
@isnad1 id=le.2h3v.s21.9296b5cc858b from=translated src=- shape=1bef94e4 vocab=b6b9dd49
-/
theorem scaledWeakPotential_gevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => weakPotential ((scaledCutoff ℓ hℓ).translate b)) a‖ ≤
      scaledCutoffOperatorAmplitude * majorant 1024 0 n := by
  have H := weakPotential_gevrey (scaledCutoff ℓ hℓ) (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize
    (by positivity) scaledCutoffGevreySize_nonneg (scaledCutoff_support_ball ℓ hℓ)
    (scaledCutoff_scaledRadiusGevrey ℓ hℓ) n a
  rw [scaledCutoff_amplitude ℓ hℓ] at H
  exact H.trans (mul_le_mul_of_nonneg_left (scaled_majorant_le ℓ hℓ.le hℓ1 n)
    scaledCutoffOperatorAmplitude_nonneg)

def scaledBoundaryOperatorAmplitude : ℝ := 3 * scaledCutoffOperatorAmplitude^2

/--
@isnad1 id=le.0h0v.s3.738839d7e623 from=translated src=- shape=ff3a10fc vocab=c3664c6f
-/
theorem scaledBoundaryOperatorAmplitude_nonneg : 0 ≤ scaledBoundaryOperatorAmplitude := by
  unfold scaledBoundaryOperatorAmplitude
  positivity

/-- The source operator is genuinely smooth in the entire spatial translation parameter.
@isnad1 id=contdiff.1h1v.s16.661b17fcb910 from=translated src=- shape=182be4b6 vocab=f98dfd19
-/
theorem scaledBoundaryOperator_contDiff (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ContDiff ℝ ∞ (fun a : Space => boundaryOperator ((scaledCutoff ℓ hℓ).translate a)) :=
  mixedBoundaryOperator_contDiff (scaledCutoff ℓ hℓ) (scaledCutoff ℓ hℓ)

/-- All actual operator derivatives have an unshifted Gevrey-two bound, uniformly for 0 < ℓ ≤ 1.
@isnad1 id=le.2h3v.s19.a11001927f02 from=translated src=- shape=08c5a312 vocab=5786c9e2
-/
theorem scaledBoundaryOperator_gevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => boundaryOperator ((scaledCutoff ℓ hℓ).translate b)) a‖ ≤
      scaledBoundaryOperatorAmplitude * majorant 1024 0 n := by
  have H := mixedBoundaryOperator_gevrey (scaledCutoff ℓ hℓ) (scaledCutoff ℓ hℓ)
    (2*ℓ⁻¹) (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize scaledCutoffGevreySize
    (by positivity) scaledCutoffGevreySize_nonneg scaledCutoffGevreySize_nonneg
    (scaledCutoff_support_ball ℓ hℓ) (scaledCutoff_support_ball ℓ hℓ)
    (scaledCutoff_scaledRadiusGevrey ℓ hℓ) (scaledCutoff_scaledRadiusGevrey ℓ hℓ) n a
  rw [scaledCutoff_amplitude ℓ hℓ] at H
  have Hb := H.trans (mul_le_mul_of_nonneg_left (scaled_majorant_le ℓ hℓ.le hℓ1 n)
    (mul_nonneg (mul_nonneg (by norm_num) scaledCutoffOperatorAmplitude_nonneg)
      scaledCutoffOperatorAmplitude_nonneg))
  simpa only [mixedBoundaryOperator_diagonal, scaledBoundaryOperatorAmplitude, pow_two, mul_assoc] using Hb

end EulerMeanBoundary
