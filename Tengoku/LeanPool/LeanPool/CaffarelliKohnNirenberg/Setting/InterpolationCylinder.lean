/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationBall
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.VectorNormAggregation
public import Tengoku

/-!
# Interpolation Cylinder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! The spatial estimate is stated with the component `L²` masses.  This is
the form in which the finite-dimensional aggregation is cheapest to reuse in
the time integration below. -/

/-! The next bridge is independent of the origin of the slice functions.  It
packages the time Hölder step, so a consumer only has to provide the spatial
interpolation estimate and the two energy bounds. -/

/-- Time integration of a same-ball cubic interpolation estimate. -/
theorem time_interpolation_ball_l3
    {T : Set ℝ} {A G : ℝ → ℝ≥0∞}
    {K R A₀ G₂ V : ℝ≥0∞}
    (hA : AEMeasurable A (volume.restrict T))
    (hG : AEMeasurable G (volume.restrict T))
    (hKtop : K ≠ ∞)
    (hA₀top : A₀ ≠ ∞)
    (hA₀ : ∀ᵐ s ∂volume.restrict T, A s ≤ A₀)
    (hG₂ : (∫⁻ s in T, G s ^ (2 : ℝ)) ≤ G₂)
    (hV : volume T ≤ V) :
    (∫⁻ s in T,
        K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) +
          K * R * A s ^ (3 : ℝ)) ≤
      K * A₀ ^ (3 / 2 : ℝ) * G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) +
        K * R * V * A₀ ^ (3 : ℝ) := by
  have hGmeas : AEMeasurable (fun s => G s ^ (3 / 2 : ℝ))
      (volume.restrict T) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hG
  have hone : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞))
      (volume.restrict T) := aemeasurable_const
  have hpq : (4 / 3 : ℝ).HolderConjugate (4 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict T) hpq hGmeas hone
  have hGpow : (∫⁻ s in T, G s ^ (3 / 2 : ℝ)) ≤
      G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
    calc
      _ = ∫⁻ s in T, (G s ^ (3 / 2 : ℝ)) * 1 := by
        apply lintegral_congr
        intro s
        rw [mul_one]
      _ ≤ (∫⁻ s in T, (G s ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ)) ^
            (1 / (4 / 3 : ℝ)) *
          (∫⁻ s in T, (1 : ℝ≥0∞) ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) := by
        simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, one_mul,
          lintegral_const] using hholder
      _ = (∫⁻ s in T, G s ^ (2 : ℝ)) ^ (3 / 4 : ℝ) *
          (volume T) ^ (1 / 4 : ℝ) := by
        rw [show 1 / (4 / 3 : ℝ) = (3 / 4 : ℝ) by norm_num]
        congr 1
        · apply congrArg (fun z : ℝ≥0∞ => z ^ (3 / 4 : ℝ))
          apply lintegral_congr
          intro s
          rw [← ENNReal.rpow_mul]
          norm_num
        · simp
      _ ≤ _ := by gcongr
  have hfirst : (∫⁻ s in T,
      K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ)) ≤
      K * A₀ ^ (3 / 2 : ℝ) * G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
    have hpoint : ∀ᵐ s ∂volume.restrict T,
        K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) ≤
          K * A₀ ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) := by
      filter_upwards [hA₀] with s hs
      gcongr
    calc
      _ ≤ ∫⁻ s in T, K * A₀ ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) :=
        lintegral_mono_ae hpoint
      _ = K * A₀ ^ (3 / 2 : ℝ) *
          (∫⁻ s in T, G s ^ (3 / 2 : ℝ)) := by
        have hconst := lintegral_const_mul'
          (μ := volume.restrict T) (K * A₀ ^ (3 / 2 : ℝ))
          (fun s : ℝ => G s ^ (3 / 2 : ℝ))
          (ENNReal.mul_ne_top hKtop
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA₀top))
        simpa only [mul_assoc] using hconst
      _ ≤ _ := by
        calc
          _ ≤ K * A₀ ^ (3 / 2 : ℝ) *
              (G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hGpow (by positivity)
          _ = K * A₀ ^ (3 / 2 : ℝ) * G₂ ^ (3 / 4 : ℝ) *
              V ^ (1 / 4 : ℝ) := by ring
  have hsecond : (∫⁻ s in T, K * R * A s ^ (3 : ℝ)) ≤
      K * R * V * A₀ ^ (3 : ℝ) := by
    have hpoint : ∀ᵐ s ∂volume.restrict T,
        K * R * A s ^ (3 : ℝ) ≤ K * R * A₀ ^ (3 : ℝ) := by
      filter_upwards [hA₀] with s hs
      gcongr
    calc
      _ ≤ ∫⁻ s in T, K * R * A₀ ^ (3 : ℝ) := lintegral_mono_ae hpoint
      _ = K * R * (volume T) * A₀ ^ (3 : ℝ) := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        ring
      _ ≤ _ := by gcongr
  have hfirstmeas : AEMeasurable
      (fun s => K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ))
      (volume.restrict T) :=
    (aemeasurable_const.mul (hA.pow_const (3 / 2 : ℝ))).mul hGmeas
  calc
    _ = (∫⁻ s in T, K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ)) +
        (∫⁻ s in T, K * R * A s ^ (3 : ℝ)) :=
      lintegral_add_left' hfirstmeas _
    _ ≤ _ := add_le_add hfirst hsecond

end CKN
