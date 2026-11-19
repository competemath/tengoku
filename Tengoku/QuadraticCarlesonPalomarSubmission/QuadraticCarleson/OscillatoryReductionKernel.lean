/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.DyadicKernelInfinite
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.FiniteModulationKernelComparison
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.HarmonicPhaseSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact scalar kernels for the oscillatory reduction

The inner radius is dictated by the selected scale, not chosen independently.
The high-pass kernel is exactly the sum of all nonnegative oscillatory heights.
Subtracting two ordinary Hilbert truncations leaves a boundary annulus and a
small-phase error supported in the inner interval.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace OscillatoryReduction

noncomputable def innerRadius (lam : ℝ) (hlam : lam ≠ 0) : ℝ :=
  (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 3)

/--
@isnad1 id=lt.1h1v.s4.4e06c43154d4 from=translated src=- shape=60baa177 vocab=6e6d4fb3
-/
theorem innerRadius_pos (lam : ℝ) (hlam : lam ≠ 0) : 0 < innerRadius lam hlam := by
  unfold innerRadius
  positivity

/--
@isnad1 id=le.1h1v.s5.a8713926c81d from=translated src=- shape=c7bcfeed vocab=465f9469
-/
theorem innerRadius_phase_bound (lam : ℝ) (hlam : lam ≠ 0) :
    |lam| * innerRadius lam hlam ^ 2 ≤ 1 := by
  have hs := (oscillatoryScaleIndex_spec lam 0 hlam).2
  have hr := innerRadius_pos lam hlam
  have hsqrt := Real.sqrt_nonneg |lam|
  have heq : (2 : ℝ) ^ oscillatoryScaleIndex lam 0 hlam = 8 * innerRadius lam hlam := by
    unfold innerRadius
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  rw [heq] at hs
  norm_num at hs
  have hsqr := Real.sq_sqrt (abs_nonneg lam)
  have hsmall : innerRadius lam hlam * Real.sqrt |lam| < 1 := by nlinarith
  have hprod : 0 ≤ innerRadius lam hlam * Real.sqrt |lam| := mul_nonneg hr.le hsqrt
  nlinarith [sq_nonneg (innerRadius lam hlam * Real.sqrt |lam| - 1)]

noncomputable def highPassKernel (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) : ℂ :=
  sharpQuadraticTailKernel lam (innerRadius lam hlam) t -
    cutoffBoundaryKernel lam (innerRadius lam hlam) t

/--
@isnad1 id=eq.2h2v.s7.ae4944d5b64f from=translated src=- shape=a2682490 vocab=22bcf6a0
-/
theorem highPassKernel_eq_cutoff (lam : ℝ) (hlam : lam ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    highPassKernel lam hlam t =
      (((1 - dyadicCutoff ((2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t)) /
        t : ℝ) : ℂ) * phase (lam * t ^ 2) := by
  have hscale : (2⁻¹ : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam - 1) * t =
      t / (4 * innerRadius lam hlam) := by
    unfold innerRadius
    rw [show oscillatoryScaleIndex lam 0 hlam - 3 =
      (oscillatoryScaleIndex lam 0 hlam - 1) - 2 by ring,
      zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_zpow]
    field_simp [zpow_ne_zero]
  rw [hscale]
  unfold highPassKernel sharpQuadraticTailKernel cutoffBoundaryKernel
  rw [ite_eq_right ht]
  by_cases h : innerRadius lam hlam < |t|
  · rw [ite_eq_left h, ite_eq_right (not_le.mpr h)]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_left (le_of_not_gt h)]
    push_cast
    ring

/--
@isnad1 id=eq.1h1v.s4.db783c579a5c from=translated src=- shape=08f44604 vocab=0b50541c
-/
theorem highPassKernel_zero (lam : ℝ) (hlam : lam ≠ 0) : highPassKernel lam hlam 0 = 0 := by
  simp [highPassKernel, sharpQuadraticTailKernel, cutoffBoundaryKernel,
    not_lt_of_ge (innerRadius_pos lam hlam).le]

/--
@isnad1 id=hassum.1h2v.s6.5a6891033cf9 from=translated src=- shape=441fc4db vocab=62e350aa
-/
theorem hasSum_oscillatoryKernels (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    HasSum (fun r : ℕ ↦ (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) *
      phase (lam * t ^ 2)) (highPassKernel lam hlam t) := by
  by_cases ht : t = 0
  · subst t
    simpa only [dyadicPsi_zero, Complex.ofReal_zero, zero_mul, highPassKernel_zero] using
      (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℂ)) 0)
  · rw [highPassKernel_eq_cutoff lam hlam ht]
    exact (Complex.hasSum_ofReal.mpr
      (hasSum_dyadicPsi_oscillatoryScaleIndex lam hlam ht)).mul_right _

/--
@isnad1 id=measurab.1h1v.s4.184e6f31eb12 from=translated src=- shape=a5372030 vocab=daabe84d
-/
theorem measurable_highPassKernel (lam : ℝ) (hlam : lam ≠ 0) :
    Measurable (highPassKernel lam hlam) :=
  (measurable_sharpQuadraticTailKernel lam _).sub (measurable_cutoffBoundaryKernel lam _)

/--
@isnad1 id=le.1h2v.s5.1f654b59896d from=translated src=- shape=faf43e1a vocab=05145550
-/
theorem highPassKernel_norm_le (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    ‖highPassKernel lam hlam t‖ ≤ 2 / innerRadius lam hlam := by
  apply (norm_sub_le _ _).trans
  have hs := sharpQuadraticTailKernel_norm_le (t := t) lam (innerRadius_pos lam hlam)
  have hb := cutoffBoundaryKernel_norm_le (t := t) lam (innerRadius_pos lam hlam)
  apply (add_le_add hs hb).trans_eq
  ring

noncomputable def smallPhaseKernel (lam ε ρ t : ℝ) : ℂ :=
  if ε < |t| ∧ |t| ≤ ρ then (phase (lam * t ^ 2) - 1) / (t : ℂ) else 0

/--
@isnad1 id=measurab.0h3v.s3.01e2a37f5069 from=translated src=- shape=229f8ef9 vocab=a432bba4
-/
theorem measurable_smallPhaseKernel (lam ε ρ : ℝ) : Measurable (smallPhaseKernel lam ε ρ) := by
  unfold smallPhaseKernel
  apply Measurable.ite
    ((measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_le measurable_id.abs measurable_const))
  · unfold phase
    fun_prop
  · exact measurable_const

/--
@isnad1 id=le.0h3v.s4.bda3e556640b from=translated src=- shape=72b965cb vocab=66734477
-/
theorem smallPhaseKernel_support_subset (lam ε ρ : ℝ) :
    support (smallPhaseKernel lam ε ρ) ⊆ Metric.closedBall 0 ρ := by
  intro t ht
  have h : ε < |t| ∧ |t| ≤ ρ := by
    by_contra hn
    exact ht (by simp [smallPhaseKernel, hn])
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using h.2

/--
@isnad1 id=le.1h3v.s5.f003a99a649b from=translated src=- shape=77c73a0f vocab=f14dda6b
-/
theorem smallPhaseKernel_norm_le (lam ε : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    ‖smallPhaseKernel lam ε (innerRadius lam hlam) t‖ ≤
      (2 * Real.pi) / innerRadius lam hlam := by
  have hr := innerRadius_pos lam hlam
  by_cases ht : ε < |t| ∧ |t| ≤ innerRadius lam hlam
  · rw [smallPhaseKernel, ite_eq_left ht, norm_div, Complex.norm_real, Real.norm_eq_abs]
    by_cases ht0 : t = 0
    · simp only [ht0, abs_zero, div_zero]
      positivity
    · have htp := abs_pos.mpr ht0
      have hp := norm_phase_sub_one_le (lam * t ^ 2)
      rw [abs_mul, abs_pow] at hp
      have hprod : |lam| * |t| * innerRadius lam hlam ≤ 1 := by
        have hm := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg lam)
        have hm2 := mul_le_mul_of_nonneg_right hm hr.le
        nlinarith [innerRadius_phase_bound lam hlam]
      apply (div_le_iff₀ htp).mpr
      apply le_trans hp
      rw [show (2 * Real.pi / innerRadius lam hlam) * |t| =
        (2 * Real.pi * |t|) / innerRadius lam hlam by ring]
      apply (le_div_iff₀ hr).mpr
      convert mul_le_mul_of_nonneg_left hprod
        (by positivity : 0 ≤ 2 * Real.pi * |t|) using 1 <;> ring
  · rw [smallPhaseKernel, ite_eq_right ht, norm_zero]
    positivity

/--
@isnad1 id=eq.3h3v.s6.b4885817caf4 from=translated src=- shape=765b383e vocab=ac9e1257
-/
theorem sharpQuadraticTailKernel_eq_oscillatory_reduction
    (lam ε : ℝ) (hlam : lam ≠ 0) (_hε : 0 < ε)
    (hερ : ε ≤ innerRadius lam hlam) (t : ℝ) :
    sharpQuadraticTailKernel lam ε t =
      highPassKernel lam hlam t + cutoffBoundaryKernel lam (innerRadius lam hlam) t +
      sharpQuadraticTailKernel 0 ε t - sharpQuadraticTailKernel 0 (innerRadius lam hlam) t +
      smallPhaseKernel lam ε (innerRadius lam hlam) t := by
  unfold highPassKernel sharpQuadraticTailKernel smallPhaseKernel
  simp only [sub_add_cancel, zero_mul, phase_zero]
  by_cases hεt : ε < |t|
  · by_cases hρt : innerRadius lam hlam < |t|
    · simp [hεt, hρt, not_le.mpr hρt]
    · simp [hεt, hρt, le_of_not_gt hρt]
      ring
  · have hρt : ¬ innerRadius lam hlam < |t| := fun h ↦ hεt (hερ.trans_lt h)
    simp [hεt, hρt]

end OscillatoryReduction
end QuadraticCarleson
