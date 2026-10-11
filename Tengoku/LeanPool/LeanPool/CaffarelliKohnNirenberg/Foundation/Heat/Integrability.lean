/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Bounds
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.TestFunction
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.PolyExpBounds
public import Tengoku

/-!
# Integrability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- Wider Gaussian majorant for the spatial heat-kernel gradient. -/
def heatKernelGradientMajorant (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    (Real.sqrt t)⁻¹ * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(∑ i, x i ^ 2) / (8 * t))
  else 0

lemma heatKernelGradientMajorant_nonneg (x : Vec3) (t : ℝ) :
    0 ≤ heatKernelGradientMajorant x t := by
  unfold heatKernelGradientMajorant
  by_cases ht : 0 < t
  · simp only [ite_eq_left ht]
    positivity
  · simp only [ite_eq_right ht]
    norm_num

private lemma gaussian_eight_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (8 * t))) volume := by
  have hG := heatKernel_integrable (show 0 < 2 * t by positivity)
  have hc : 0 < (8 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by positivity
  have heq : (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (8 * t))) =
      (fun x : Vec3 => ((8 * Real.pi * t) ^ (-(3 : ℝ) / 2))⁻¹ *
        heatKernel x (2 * t)) := by
    funext x
    rw [heatKernel_eq_formula_sum (show 0 < 2 * t by positivity)]
    field_simp
    ring_nf
  rw [heq]
  exact hG.const_mul _

private lemma heat_prefactor_double_le {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) ≤ 4 := by
  have hbase : 0 < 4 * Real.pi * t := by positivity
  have hbase8 : 0 < 8 * Real.pi * t := by positivity
  have hsqrt : (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) =
      (8 * Real.pi * t) ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hbase8.le]
    norm_num
  rw [hsqrt]
  have hinv : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) =
      ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring_nf, Real.rpow_neg hbase.le]
  rw [hinv]
  have hsplit : (8 * Real.pi * t) = 2 * (4 * Real.pi * t) := by ring_nf
  have htwo : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 := by
    have htwo' : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
        (y := (3 : ℝ) / 2) (z := 2) (by norm_num) (by norm_num)
    convert htwo' using 1
    norm_num
  have hratio : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        (8 * Real.pi * t) ^ ((3 : ℝ) / 2) =
      (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    have hp : (4 * Real.pi * t) ^ ((3 : ℝ) / 2) ≠ 0 :=
      (Real.rpow_pos_of_pos hbase _).ne'
    calc
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          (8 * Real.pi * t) ^ ((3 : ℝ) / 2) =
          ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ *
            (2 * (4 * Real.pi * t)) ^ ((3 : ℝ) / 2) := by rw [hinv, hsplit]
      _ = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ *
            ((2 : ℝ) ^ ((3 : ℝ) / 2) *
              (4 * Real.pi * t) ^ ((3 : ℝ) / 2)) := by
        rw [Real.mul_rpow (by norm_num) hbase.le]
      _ = (2 : ℝ) ^ ((3 : ℝ) / 2) := by field_simp [hp]
  have hratio_inv : ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ *
        (8 * Real.pi * t) ^ ((3 : ℝ) / 2) =
      (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← hinv]
    exact hratio
  rw [hratio_inv]
  exact htwo

lemma heatKernelGradientMajorant_slice_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => heatKernelGradientMajorant x t) volume := by
  rw [show (fun x : Vec3 => heatKernelGradientMajorant x t) =
      (fun x : Vec3 => (Real.sqrt t)⁻¹ *
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, x i ^ 2) / (8 * t))) by
    funext x
    simp [heatKernelGradientMajorant, ht]]
  exact (gaussian_eight_integrable ht).const_mul _

lemma heatKernelGradientMajorant_slice_le {t : ℝ} (ht : 0 < t) :
    ∫ x : Vec3, ‖heatKernelGradientMajorant x t‖ ≤
      4 * (Real.sqrt t)⁻¹ := by
  have hnonneg : ∀ x : Vec3, 0 ≤ heatKernelGradientMajorant x t :=
    fun x => heatKernelGradientMajorant_nonneg x t
  have hform : (fun x : Vec3 => heatKernelGradientMajorant x t) =
      (fun x : Vec3 => (Real.sqrt t)⁻¹ *
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, x i ^ 2) / (8 * t))) := by
    funext x
    simp [heatKernelGradientMajorant, ht]
  rw [show (fun x : Vec3 => ‖heatKernelGradientMajorant x t‖) =
      (fun x : Vec3 => heatKernelGradientMajorant x t) by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]]
  rw [hform, integral_const_mul]
  have hg := gaussian_integral (2 * t) (by positivity)
  have heq : (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (8 * t))) =
      (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (4 * (2 * t)))) := by
    funext x
    congr 1
    ring_nf
  rw [heq, hg]
  have hsqrt2 : Real.sqrt (4 * Real.pi * (2 * t)) =
      Real.sqrt (8 * Real.pi * t) := by
    congr 1
    ring_nf
  rw [hsqrt2]
  have hpref := heat_prefactor_double_le ht
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  calc
    (Real.sqrt t)⁻¹ * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) ≤
        (Real.sqrt t)⁻¹ * 4 := by
      calc
        (Real.sqrt t)⁻¹ * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ) =
            (Real.sqrt t)⁻¹ *
              ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
                (Real.sqrt (8 * Real.pi * t)) ^ (3 : ℕ)) := by ring_nf
        _ ≤ (Real.sqrt t)⁻¹ * 4 :=
          mul_le_mul_of_nonneg_left hpref (by positivity)
    _ = 4 * (Real.sqrt t)⁻¹ := by ring_nf

private lemma heatKernelPlus_measurable :
    Measurable (fun p : ParabolicPoint => heatKernelPlus p) := by
  unfold heatKernelPlus
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · exact (by
      unfold heatKernel
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
      · fun_prop
      · exact measurable_const)
  · exact measurable_const

private lemma heatKernel_measurable :
    Measurable (fun p : ParabolicPoint => heatKernel p.1 p.2) := by
  unfold heatKernel
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · fun_prop
  · exact measurable_const

lemma heatKernelGradientNorm_measurable :
    Measurable (fun p : ParabolicPoint => heatKernelGradientNorm p.1 p.2) := by
  unfold heatKernelGradientNorm
  apply Finset.measurable_sum Finset.univ
  intro i hi
  have hderiv : Measurable
      (fun p : ParabolicPoint => heatKernelSpaceDerivative p.1 p.2 i) := by
    unfold heatKernelSpaceDerivative
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · have hcoord : Measurable (fun p : ParabolicPoint => p.1 i) :=
        measurable_pi_apply i |>.comp measurable_fst
      have htime : Measurable (fun p : ParabolicPoint => p.2) := measurable_snd
      exact (hcoord.neg.div (measurable_const.mul htime)).mul heatKernel_measurable
    · exact measurable_const
  exact (continuous_abs.measurable.comp hderiv)

lemma heatKernelPlus_integrable_prod {T : ℝ} :
    Integrable (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p))
      ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 T))) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 T)
  change Integrable (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p))
      ((volume : Measure Vec3).prod ν)
  have hmeas₀ := heatKernelPlus_measurable
  change Measurable (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p)) at hmeas₀
  have hmeas : AEStronglyMeasurable
      (fun p : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from p)) (volume.prod ν) :=
    hmeas₀.aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have heq : (fun x : Vec3 => heatKernelPlus (show ParabolicPoint from (x, t))) =
        (fun x : Vec3 => heatKernel x t) := by
      funext x
      exact heatKernelPlus_eq_heatKernel (show ParabolicPoint from (x, t))
    rw [heq]
    exact heatKernel_integrable ht.1
  · have houter : (fun t : ℝ => ∫ x : Vec3, ‖heatKernelPlus (x, t)‖) =ᵐ[ν]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hnorm : (fun x : Vec3 =>
          ‖heatKernelPlus (show ParabolicPoint from (x, t))‖) =
          (fun x : Vec3 => heatKernel x t) := by
        funext x
        rw [heatKernelPlus_eq_heatKernel, Real.norm_eq_abs,
          abs_of_nonneg (heatKernel_nonneg _ _)]
      rw [hnorm, heatKernel_integral t ht.1]
    have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ν :=
      integrableOn_const (s := Ioc 0 T) (μ := volume)
        (measure_Ioc_lt_top (μ := volume)).ne
    exact hone.congr houter.symm

lemma heatKernelPlus_integrableOn_time {T : ℝ} :
    IntegrableOn (fun p : ParabolicPoint => heatKernelPlus p)
      (Set.univ ×ˢ Ioc 0 T) volume := by
  change Integrable (fun p : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from p))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioc 0 T))
  rw [← Measure.prod_restrict]
  simpa only [Measure.restrict_univ] using heatKernelPlus_integrable_prod

lemma time_sqrt_inv_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => 4 * (Real.sqrt t)⁻¹)
      (volume.restrict (Ioc 0 T)) := by
  have hpowIoo : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioo 0 T) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 (by norm_num)
  have hpowIoc : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioc 0 T) volume := by
    apply hpowIoo.congr_set_ae
    exact (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := T)).symm
  have hpow : Integrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2))
      (volume.restrict (Ioc 0 T)) := hpowIoc
  have hmul := hpow.const_mul (4 : ℝ)
  apply hmul.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring_nf,
    Real.rpow_neg ht0.le]

lemma heatKernelGradientNorm_eq_zero_of_nonpos {x : Vec3} {t : ℝ}
    (ht : t ≤ 0) : heatKernelGradientNorm x t = 0 := by
  unfold heatKernelGradientNorm heatKernelSpaceDerivative
  simp [not_lt.mpr ht]

end CKN.Foundation.Heat
