/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveDyadicKernel
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.QuadraticFixedHeightAveragingCorrelation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete one-sided dyadic amplitudes for fixed-height quadratic decay

The positive half of the paper's annular dyadic kernel is a dilation of one
fixed smooth compactly supported function. Uniform amplitude and derivative
constants are derived from that fixed function, not supplied as assumptions.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace QuadraticCarleson

/-- Exact dilation law for the dyadic difference quotient in the paper.
@isnad1 id=eq.0h2v.s6.b3edcaf92ab5 from=translated src=- shape=23feabf1 vocab=5d5e6dec
-/
theorem dyadicPsi_dilation (j : ℤ) (t : ℝ) :
    dyadicPsi j t = (2⁻¹ : ℝ) ^ j * dyadicPsi 0 ((2⁻¹ : ℝ) ^ j * t) := by
  have hc : (2⁻¹ : ℝ) ^ j ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hs : (2⁻¹ : ℝ) ^ (j - 1) = 2 * (2⁻¹ : ℝ) ^ j := by
    rw [zpow_sub₀ (by norm_num : (2⁻¹ : ℝ) ≠ 0)]
    norm_num
    ring
  by_cases ht : t = 0
  · simp [ht, dyadicPsi_zero]
  · rw [dyadicPsi_eq_quotient ht, dyadicPsi_eq_quotient (mul_ne_zero hc ht)]
    simp only [zpow_zero, one_mul, zero_sub, zpow_neg, zpow_one]
    simp only [inv_inv]
    rw [hs]
    field_simp

/-- The fixed positive half of the scale-zero dyadic amplitude.-/
noncomputable def positiveDyadicBase (t : ℝ) : ℂ :=
  if 0 < t then (dyadicPsi 0 t : ℂ) else 0

/--
@isnad1 id=contdiff.0h0v.s5.e7aebd5fab4e from=translated src=- shape=352d7a74 vocab=bd20942e
-/
theorem positiveDyadicBase_smooth : ContDiff ℝ ∞ positiveDyadicBase := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : 0 < t
  · apply (Complex.ofRealCLM.contDiff.comp (dyadicPsi_smooth 0)).contDiffAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    have hup : 0 < u := hu
    simp [positiveDyadicBase, hup]
  by_cases ht' : t < 0
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht'] with u hu
    have hun : u < 0 := hu
    simp [positiveDyadicBase, not_lt.mpr hun.le]
  have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) (le_of_not_gt ht')
  subst t
  apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 8)] with u hu
  have habs : |u| ≤ (2 : ℝ) ^ ((0 : ℤ) - 3) := by
    have hh : |u| < 1 / 8 := by simpa [Metric.mem_ball, Real.dist_eq] using hu
    norm_num
    exact hh.le
  have hz := dyadicPsi_eq_zero_of_abs_le habs
  simp [positiveDyadicBase, hz]

/--
@isnad1 id=le.0h0v.s5.6e02dcd8492d from=translated src=- shape=6758b511 vocab=9a086d10
-/
theorem positiveDyadicBase_support_subset :
    Function.support positiveDyadicBase ⊆ Icc (1 / 8 : ℝ) (1 / 2) := by
  intro t ht
  have hpos : 0 < t := by
    by_contra h
    exact ht (by simp [positiveDyadicBase, h])
  have hpsi : dyadicPsi 0 t ≠ 0 := by
    intro hz
    exact ht (by simp [positiveDyadicBase, hz])
  have h := dyadicPsi_support_subset 0 hpsi
  norm_num [abs_of_pos hpos] at h
  exact ⟨h.1.le, h.2.le⟩

/--
@isnad1 id=hascompa.0h0v.s3.6a238ef527a9 from=translated src=- shape=54c8eceb vocab=05c7576b
-/
theorem positiveDyadicBase_hasCompactSupport : HasCompactSupport positiveDyadicBase :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc positiveDyadicBase_support_subset

/--
@isnad1 id=continuo.0h0v.s6.a11caa57b1a0 from=translated src=- shape=9a8f392b vocab=92b18847
-/
theorem continuous_deriv_positiveDyadicBase : Continuous (deriv positiveDyadicBase) := by
  have h2 : ContDiff ℝ 2 positiveDyadicBase := positiveDyadicBase_smooth.of_le (by norm_num)
  exact h2.differentiable_deriv_two.continuous

/-- A single finite constant bounds the fixed amplitude and its derivative.
@isnad1 id=ex.0h0v.s6.1f1c0c8f0219 from=translated src=- shape=f09236c9 vocab=baaf6961
-/
theorem exists_positiveDyadicBase_bound : ∃ D : ℝ, 0 ≤ D ∧
    (∀ t, ‖positiveDyadicBase t‖ ≤ D) ∧ (∀ t, ‖deriv positiveDyadicBase t‖ ≤ D) := by
  have hc : Continuous positiveDyadicBase := positiveDyadicBase_smooth.continuous
  have hdc : Continuous (deriv positiveDyadicBase) := continuous_deriv_positiveDyadicBase
  obtain ⟨C, hC⟩ := hc.norm.bddAbove_range_of_hasCompactSupport positiveDyadicBase_hasCompactSupport.norm
  obtain ⟨C', hC'⟩ := hdc.norm.bddAbove_range_of_hasCompactSupport
    positiveDyadicBase_hasCompactSupport.deriv.norm
  refine ⟨max (max C C') 0, le_max_right _ _, ?_, ?_⟩
  · intro t
    exact (hC (mem_range_self t)).trans ((le_max_left C C').trans (le_max_left _ _))
  · intro t
    exact (hC' (mem_range_self t)).trans ((le_max_right C C').trans (le_max_left _ _))

noncomputable def positiveDyadicAmplitudeBound : ℝ := Classical.choose exists_positiveDyadicBase_bound

/--
@isnad1 id=le.0h0v.s3.fa5324d120ab from=translated src=- shape=ff3a10fc vocab=351fb529
-/
theorem positiveDyadicAmplitudeBound_nonneg : 0 ≤ positiveDyadicAmplitudeBound :=
  (Classical.choose_spec exists_positiveDyadicBase_bound).1

/--
@isnad1 id=le.0h1v.s3.2e8eea759a12 from=translated src=- shape=1036feda vocab=6182952d
-/
theorem norm_positiveDyadicBase_le (t : ℝ) : ‖positiveDyadicBase t‖ ≤ positiveDyadicAmplitudeBound :=
  (Classical.choose_spec exists_positiveDyadicBase_bound).2.1 t

/--
@isnad1 id=le.0h1v.s5.cda38c4b3dd0 from=translated src=- shape=68ae7430 vocab=df455809
-/
theorem norm_deriv_positiveDyadicBase_le (t : ℝ) :
    ‖deriv positiveDyadicBase t‖ ≤ positiveDyadicAmplitudeBound :=
  (Classical.choose_spec exists_positiveDyadicBase_bound).2.2 t

/-- The one-sided dyadic amplitude, expressed by its exact dilation.-/
noncomputable def positiveDyadicAmplitude (j : ℤ) (t : ℝ) : ℂ :=
  (((2⁻¹ : ℝ) ^ j : ℝ) : ℂ) * positiveDyadicBase ((2⁻¹ : ℝ) ^ j * t)

noncomputable def positiveDyadicAmplitudeDerivative (j : ℤ) (t : ℝ) : ℂ :=
  (((2⁻¹ : ℝ) ^ j : ℝ) : ℂ) ^ 2 * deriv positiveDyadicBase ((2⁻¹ : ℝ) ^ j * t)

/--
@isnad1 id=eq.0h2v.s5.0dd273a44e4a from=translated src=- shape=5df72834 vocab=6c101e74
-/
theorem positiveDyadicAmplitude_eq (j : ℤ) (t : ℝ) :
    positiveDyadicAmplitude j t = if 0 < t then (dyadicPsi j t : ℂ) else 0 := by
  have hc : 0 < (2⁻¹ : ℝ) ^ j := zpow_pos (by norm_num) j
  unfold positiveDyadicAmplitude positiveDyadicBase
  simp only [mul_pos_iff_of_pos_left hc]
  split_ifs with ht
  · rw [dyadicPsi_dilation j t]
    push_cast
    rfl
  · simp

/--
@isnad1 id=hasderiv.0h2v.s5.02f538c4588b from=translated src=- shape=d0f726c2 vocab=00417fef
-/
theorem hasDerivAt_positiveDyadicAmplitude (j : ℤ) (t : ℝ) :
    HasDerivAt (positiveDyadicAmplitude j) (positiveDyadicAmplitudeDerivative j t) t := by
  have h : HasDerivAt positiveDyadicBase (deriv positiveDyadicBase ((2⁻¹ : ℝ) ^ j * t))
      ((2⁻¹ : ℝ) ^ j * t) :=
    (positiveDyadicBase_smooth.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hc := h.scomp t ((hasDerivAt_id t).const_mul ((2⁻¹ : ℝ) ^ j))
  apply (hc.const_mul ((((2⁻¹ : ℝ) ^ j : ℝ) : ℂ))).congr_deriv
  simp only [positiveDyadicAmplitudeDerivative, id_eq, mul_one, Complex.real_smul]
  ring

/--
@isnad1 id=continuo.0h1v.s4.5d3f746fc2ff from=translated src=- shape=7000f90d vocab=84a7de6f
-/
theorem continuous_positiveDyadicAmplitudeDerivative (j : ℤ) :
    Continuous (positiveDyadicAmplitudeDerivative j) := by
  exact continuous_const.mul
    (continuous_deriv_positiveDyadicBase.comp (continuous_const.mul continuous_id))

/-- The normalization relating the dilation and the outer annular radius.
@isnad1 id=eq.0h1v.s6.8951524cc8b0 from=translated src=- shape=3a861f51 vocab=5efd2295
-/
theorem dyadicDilation_mul_radius (j : ℤ) :
    (2⁻¹ : ℝ) ^ j * (2 : ℝ) ^ (j - 1) = 1 / 2 := by
  rw [inv_zpow, ← zpow_neg, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring_nf
  norm_num

/-- Exact positive-annular support at outer radius `2^(j-1)`.
@isnad1 id=le.0h1v.s6.4f0a38ae6030 from=translated src=- shape=2f12834b vocab=43ffc81c
-/
theorem positiveDyadicAmplitude_support_subset (j : ℤ) :
    Function.support (positiveDyadicAmplitude j) ⊆
      Icc ((2 : ℝ) ^ (j - 1) / 4) ((2 : ℝ) ^ (j - 1)) := by
  intro t ht
  have hpos : 0 < t := by
    by_contra h
    exact ht (by simp [positiveDyadicAmplitude_eq, h])
  have hpsi : dyadicPsi j t ≠ 0 := by
    intro hz
    exact ht (by simp [positiveDyadicAmplitude_eq, hz])
  have h := dyadicPsi_support_subset j hpsi
  change (2 : ℝ) ^ (j - 3) < |t| ∧ |t| < (2 : ℝ) ^ (j - 1) at h
  rw [abs_of_pos hpos] at h
  have hid : (2 : ℝ) ^ (j - 1) / 4 = (2 : ℝ) ^ (j - 3) := by
    rw [show j - 3 = (j - 1) - 2 by ring,
      zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0) (j - 1) 2]
    norm_num
  exact ⟨by rw [hid]; exact h.1.le, h.2.le⟩

/-- The concrete uniform amplitude bound required by the annular theorem.
@isnad1 id=le.0h2v.s5.c877d5e7e0f2 from=translated src=- shape=062b8009 vocab=3ec79add
-/
theorem norm_positiveDyadicAmplitude_le (j : ℤ) (t : ℝ) :
    ‖positiveDyadicAmplitude j t‖ ≤ positiveDyadicAmplitudeBound / (2 : ℝ) ^ (j - 1) := by
  have hc : 0 < (2⁻¹ : ℝ) ^ j := zpow_pos (by norm_num) j
  have hR : 0 < (2 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
  have hD := positiveDyadicAmplitudeBound_nonneg
  have hcle : (2⁻¹ : ℝ) ^ j ≤ 1 / (2 : ℝ) ^ (j - 1) := by
    apply (le_div_iff₀ hR).mpr
    rw [dyadicDilation_mul_radius]
    norm_num
  calc
    _ = (2⁻¹ : ℝ) ^ j * ‖positiveDyadicBase ((2⁻¹ : ℝ) ^ j * t)‖ := by
      simp only [positiveDyadicAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    _ ≤ (2⁻¹ : ℝ) ^ j * positiveDyadicAmplitudeBound :=
      mul_le_mul_of_nonneg_left (norm_positiveDyadicBase_le _) hc.le
    _ ≤ (1 / (2 : ℝ) ^ (j - 1)) * positiveDyadicAmplitudeBound :=
      mul_le_mul_of_nonneg_right hcle hD
    _ = _ := by ring

/-- The concrete uniform derivative bound required by the annular theorem.
@isnad1 id=le.0h2v.s6.e45a9c35c280 from=translated src=- shape=3742abb0 vocab=c1b00509
-/
theorem norm_positiveDyadicAmplitudeDerivative_le (j : ℤ) (t : ℝ) :
    ‖positiveDyadicAmplitudeDerivative j t‖ ≤
      positiveDyadicAmplitudeBound / ((2 : ℝ) ^ (j - 1)) ^ 2 := by
  have hc : 0 < (2⁻¹ : ℝ) ^ j := zpow_pos (by norm_num) j
  have hR : 0 < (2 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
  have hD := positiveDyadicAmplitudeBound_nonneg
  have hcle : (2⁻¹ : ℝ) ^ j ≤ 1 / (2 : ℝ) ^ (j - 1) := by
    apply (le_div_iff₀ hR).mpr
    rw [dyadicDilation_mul_radius]
    norm_num
  calc
    _ = ((2⁻¹ : ℝ) ^ j) ^ 2 * ‖deriv positiveDyadicBase ((2⁻¹ : ℝ) ^ j * t)‖ := by
      simp only [positiveDyadicAmplitudeDerivative, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    _ ≤ ((2⁻¹ : ℝ) ^ j) ^ 2 * positiveDyadicAmplitudeBound :=
      mul_le_mul_of_nonneg_left (norm_deriv_positiveDyadicBase_le _) (sq_nonneg _)
    _ ≤ (1 / (2 : ℝ) ^ (j - 1)) ^ 2 * positiveDyadicAmplitudeBound :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le hcle 2) hD
    _ = _ := by ring

end QuadraticCarleson
