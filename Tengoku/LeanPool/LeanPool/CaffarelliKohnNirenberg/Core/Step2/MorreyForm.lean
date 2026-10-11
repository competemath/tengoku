/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyBalls

/-!
# Morrey Form

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Parabolic.Integration
noncomputable section
namespace CKN
/-- Pressure coefficient controlling the small-scale Morrey integral bounds. -/
def pressureSmallConstant (M : ℝ) : ℝ≥0∞ := ENNReal.ofReal (M ^ (3 / 2 : ℝ) * (8 : ℝ) ^ (13 / 5 :
  ℝ))
/-- Gradient coefficient controlling the small-scale Morrey integral bounds. -/
def gradientSmallConstant (M : ℝ) : ℝ≥0∞ := ENNReal.ofReal (M ^ 2 * (8 : ℝ) ^ (9 / 5 : ℝ))
/-- Velocity coefficient obtained from Sobolev interpolation in the small-scale Morrey estimate.
-/
def velocitySmallConstant (M : ℝ) : ℝ≥0∞ := ((ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2 - 1)) * 3) *
    localSobolevConstant ^ (3 / 2 : ℝ)) * ENNReal.ofReal (M ^ 3 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      ((2 : ℝ) ^ (27 / 10 : ℝ) + (32 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (27 / 10 : ℝ)) * (4 : ℝ) ^ (16
        / 5 : ℝ))
private theorem ballPowerIntegral_zero {p : ℝ} {Q : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hp : 0 < p) (hdis : Metric.ball z r ∩ Q = ∅) : ballPowerIntegral
      p (Q.indicator g) z r = 0 := by
  unfold ballPowerIntegral
  apply le_antisymm
  · have heq : (∫⁻ y in Metric.ball z r,
        ENNReal.ofReal |Q.indicator g y| ^ p) =
        ∫⁻ y in Metric.ball z r, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_ball)] with y hy
      have hyQ : y ∉ Q := by
        intro hyQ
        have : y ∈ (∅ : Set ParabolicPoint) := hdis ▸ Set.mem_inter hy hyQ
        exact this
      simp [Set.indicator_of_notMem hyQ, ENNReal.zero_rpow_of_pos hp]
    exact heq.le.trans_eq (by simp)
  · exact bot_le
private theorem abar_real {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    ((2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) = M * (2 * R) ^ (9 / 10 : ℝ) := by
  have hX : 0 ≤ 2 * R := by positivity
  have hXpos : 0 < 2 * R := by positivity
  have hA : 0 ≤ M * (2 * R) ^ (2 / 5 : ℝ) :=
    mul_nonneg hM (Real.rpow_nonneg hX _)
  have hAsqrt : ((M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) ^
      (1 / 2 : ℝ) = M * (2 * R) ^ (2 / 5 : ℝ) := by
    calc
      _ = ((M * (2 * R) ^ (2 / 5 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = (M * (2 * R) ^ (2 / 5 : ℝ)) ^ ((2 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hA 2 (1 / 2)).symm
      _ = _ := by norm_num
  rw [Real.mul_rpow hX (sq_nonneg (M * (2 * R) ^ (2 / 5 : ℝ))), hAsqrt]
  calc
    (2 * R) ^ (1 / 2 : ℝ) * (M * (2 * R) ^ (2 / 5 : ℝ)) =
        M * ((2 * R) ^ (1 / 2 : ℝ) * (2 * R) ^ (2 / 5 : ℝ)) := by ring_nf
    _ = _ := by rw [← Real.rpow_add hXpos]; norm_num
private theorem gbar_real {M R : ℝ} (_ : 0 ≤ M) (hR : 0 < R) :
    (2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2 = M ^ 2 * (2 * R) ^ (9 / 5 : ℝ) := by
  have hX : 0 ≤ 2 * R := by positivity
  have hXpos : 0 < 2 * R := by positivity
  have hpow : ((2 * R) ^ (2 / 5 : ℝ)) ^ 2 =
      (2 * R) ^ (4 / 5 : ℝ) := by
    calc
      _ = ((2 * R) ^ (2 / 5 : ℝ)) ^ (2 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = _ := by rw [← Real.rpow_mul hX]; norm_num
  rw [mul_pow, hpow]
  calc
    2 * R * (M ^ 2 * (2 * R) ^ (4 / 5 : ℝ)) =
        M ^ 2 * ((2 * R) * (2 * R) ^ (4 / 5 : ℝ)) := by ring_nf
    _ = M ^ 2 * ((2 * R) ^ (1 : ℝ) * (2 * R) ^ (4 / 5 : ℝ)) := by
      rw [Real.rpow_one]
    _ = M ^ 2 * (2 * R) ^ (9 / 5 : ℝ) := by
      rw [← Real.rpow_add hXpos]
      norm_num
private theorem decay_bounds {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * R)) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z (2 * R)) (beta u Du z (2 * R)))
      (delta p z (2 * R) ^ 2) ≤ M * (2 * R) ^ (2 / 5 : ℝ)) :
    (essSup (fun s => ∫⁻ y in vec3Ball z.1 (2 * R), ENNReal.ofReal
      (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Set.Ioc (z.2 - R ^ 2) z.2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (M * (2 * R) ^ (9 / 10 : ℝ)) ∧
      (∫⁻ w in parabolicCylinder z.1 z.2 (2 * R), ENNReal.ofReal
        (spatialGradientSq u Du w)) ≤ ENNReal.ofReal (M ^ 2 * (2 * R) ^ (9 / 5 : ℝ)) := by
  have hR2 : 0 < 2 * R := by positivity
  have hD : 0 ≤ M * (2 * R) ^ (2 / 5 : ℝ) := by positivity
  have hα : alpha u z (2 * R) ≤ M * (2 * R) ^ (2 / 5 : ℝ) :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hdec)
  have hβ : beta u Du z (2 * R) ≤ M * (2 * R) ^ (2 / 5 : ℝ) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hdec)
  have hα0 : 0 ≤ alpha u z (2 * R) := by unfold alpha; positivity
  have hβ0 : 0 ≤ beta u Du z (2 * R) := by unfold beta; positivity
  have hαsq : (2 * R) * alpha u z (2 * R) ^ 2 ≤
      (2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hα0 hD).2 hα) hR2.le
  have hβsq : (2 * R) * beta u Du z (2 * R) ^ 2 ≤
      (2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hβ0 hD).2 hβ) hR2.le
  have hEss := sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol z hR2 hsub
  have hGrad := sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
    hsol z hR2 hsub
  have hTsub : Set.Ioc (z.2 - R ^ 2) z.2 ⊆
      Set.Ioc (z.2 - (2 * R) ^ 2) z.2 := by
    intro s hs
    exact ⟨by nlinarith only [hs.1, hR], hs.2⟩
  have hpoint : ∀ s, (∫⁻ y in vec3Ball z.1 (2 * R),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      timeSliceBallEnergy z.1 (2 * R) s
        (fun w => vec3EuclideanNorm (u w)) := by
    intro s
    change (∫⁻ y in vec3Ball z.1 (2 * R),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      ∫⁻ y in vec3Ball z.1 (2 * R),
        ‖vec3EuclideanNorm (u (y, s))‖ₑ ^ (2 : ℝ)
    apply le_of_eq
    apply lintegral_congr
    intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg (u (y, s)))]
  have hmono := essSup_mono_measure_and_ae
    (μ := volume.restrict (Set.Ioc (z.2 - R ^ 2) z.2))
    (ν := volume.restrict (Set.Ioc (z.2 - (2 * R) ^ 2) z.2))
    (Measure.restrict_mono_set volume hTsub) (Filter.Eventually.of_forall hpoint)
  have hess := hmono.trans_eq hEss
  have hA : (essSup (fun s => ∫⁻ y in vec3Ball z.1 (2 * R),
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Set.Ioc (z.2 - R ^ 2) z.2))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (M * (2 * R) ^ (9 / 10 : ℝ)) := by
    have hroot := ENNReal.rpow_le_rpow hess (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      _ ≤ (ENNReal.ofReal ((2 * R) * alpha u z (2 * R) ^ 2)) ^
          (1 / 2 : ℝ) := hroot
      _ = ENNReal.ofReal (((2 * R) * alpha u z (2 * R) ^ 2) ^
          (1 / 2 : ℝ)) := ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
      _ ≤ ENNReal.ofReal (((2 * R) *
          (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)) := by
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
          (by positivity) hαsq (by norm_num))
      _ = _ := by rw [abar_real (by linarith only [hM]) hR]
  refine ⟨hA, ?_⟩
  calc
    _ = ENNReal.ofReal ((2 * R) * beta u Du z (2 * R) ^ 2) := hGrad
    _ ≤ ENNReal.ofReal ((2 * R) * (M * (2 * R) ^ (2 / 5 : ℝ)) ^ 2) :=
      ENNReal.ofReal_le_ofReal hβsq
    _ = _ := by rw [gbar_real (by linarith only [hM]) hR]
/-! The Step 2 decay certificate is converted into the three Morrey bounds. -/
end CKN
