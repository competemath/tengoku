/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Near
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Morrey Sources

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/- The first-index Morrey norm gives the absolute source mass on every shell. -/

theorem integrableOn_abs_of_lintegral_lt_top
    {F : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    (hF : AEMeasurable F volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞) :
    IntegrableOn (fun w => |F w|) S volume := by
  have hmeas : AEStronglyMeasurable (fun w => |F w|)
      (volume.restrict S) := hF.norm.aestronglyMeasurable.restrict
  have hnonneg : 0 ≤ᵐ[(volume.restrict S)] (fun w => |F w|) :=
    Filter.Eventually.of_forall (fun w => abs_nonneg (F w))
  have hiff := lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg
  exact hiff.mp (ne_of_lt hfinite)

theorem integrableOn_of_abs_integrable
    {F : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    (hF : AEMeasurable F volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞) :
    IntegrableOn F S volume := by
  have habs := integrableOn_abs_of_lintegral_lt_top hF hfinite
  apply habs.mono'
  · exact hF.aestronglyMeasurable.restrict
  · filter_upwards [] with w
    simp only [Real.norm_eq_abs]
    exact le_rfl

theorem integrableOn_mul_of_abs_integrable_of_bound
    {F K : ParabolicPoint → ℝ} {S : Set ParabolicPoint} {C : ℝ}
    (hS : MeasurableSet S) (hF : AEMeasurable F volume)
    (hK : AEMeasurable K volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞)
    (_ : 0 ≤ C)
    (hbound : ∀ w ∈ S, |K w| ≤ C) :
    IntegrableOn (fun w => K w * F w) S volume := by
  have hsource := integrableOn_abs_of_lintegral_lt_top hF hfinite
  have hmajor : IntegrableOn (fun w => C * |F w|) S volume :=
    hsource.const_mul C
  apply hmajor.mono'
  · exact (hK.mul hF).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem hS] with w hw
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound w hw) (abs_nonneg _)

theorem real_integral_abs_le_of_lintegral_le
    {F : ParabolicPoint → ℝ} {S : Set ParabolicPoint} {M : ℝ≥0∞}
    (hF : AEMeasurable F volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞)
    (hMtop : M ≠ ∞)
    (hM : (∫⁻ w in S, ENNReal.ofReal |F w|) ≤ M) :
    ∫ w in S, |F w| ≤ M.toReal := by
  have hsource := integrableOn_abs_of_lintegral_lt_top hF hfinite
  have hEq : ENNReal.ofReal (∫ w in S, |F w|) =
      ∫⁻ w in S, ENNReal.ofReal |F w| := by
    exact ofReal_integral_eq_lintegral_ofReal hsource
      (Filter.Eventually.of_forall fun w => abs_nonneg (F w))
  have hI : 0 ≤ ∫ w in S, |F w| :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun w => abs_nonneg (F w))
  have hle : (ENNReal.ofReal (∫ w in S, |F w|)).toReal ≤ M.toReal := by
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hMtop).mpr
    rw [hEq]
    exact hM
  simpa only [ENNReal.toReal_ofReal hI] using hle

theorem heatPotential_near_shell_geometric_sum
    {A : ℕ → ℝ≥0∞} {C q : ℝ≥0∞}
    (_ : q < 1) (hA : ∀ n : ℕ, A n ≤ C * q ^ n) :
    ∑' n : ℕ, A n ≤ C * (1 - q)⁻¹ := by
  calc
    ∑' n : ℕ, A n ≤ ∑' n : ℕ, C * q ^ n :=
      ENNReal.tsum_le_tsum hA
    _ = C * ∑' n : ℕ, q ^ n := ENNReal.tsum_mul_left
    _ = C * (1 - q)⁻¹ := by rw [ENNReal.tsum_geometric q]

end CKN.Core.HeatPotential
