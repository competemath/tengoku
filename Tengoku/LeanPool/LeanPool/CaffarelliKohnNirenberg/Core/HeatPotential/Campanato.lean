/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Exponents
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Kernel
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.CampanatoHolderCorollaries
public import Tengoku

/-!
# Campanato

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic

/-- Contribution of scalar and divergence sources restricted to one integration shell. -/
def heatPotentialShellValue (F : ParabolicPoint → ℝ)
    (G : Fin 3 → ParabolicPoint → ℝ) (S : Set ParabolicPoint)
    (w : ParabolicPoint) : ℝ :=
  (∫ v in S, heatPotentialKernel w v * F v) +
    ∑ i, ∫ v in S, heatPotentialSpatialKernel i w v * G i v

/--
@isnad1 id=le.6h6v.s8.753c872fc1ac from=translated src=- shape=fc20d9a1 vocab=d8a21482
-/
lemma heatPotential_single_kernel_shell_bound {K : ParabolicPoint → ParabolicPoint → ℝ}
    {f : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    {p p' : ParabolicPoint} {C : ℝ}
    (_ : 0 ≤ C)
    (hS : MeasurableSet S)
    (hwi : IntegrableOn (fun v => K p v * f v) S volume)
    (hwi' : IntegrableOn (fun v => K p' v * f v) S volume)
    (hmajor : IntegrableOn (fun v => C * |f v|) S volume)
    (hpoint : ∀ v ∈ S, |K p v - K p' v| ≤ C) :
    |(∫ v in S, K p v * f v) - ∫ v in S, K p' v * f v| ≤
      C * ∫ v in S, |f v| := by
  have hdiff : IntegrableOn
      (fun v => K p v * f v - K p' v * f v) S volume := hwi.sub hwi'
  have hbound : ∀ᵐ v ∂(volume.restrict S),
      |K p v * f v - K p' v * f v| ≤ C * |f v| := by
    filter_upwards [MeasureTheory.ae_restrict_mem hS] with v hv
    rw [show K p v * f v - K p' v * f v = (K p v - K p' v) * f v by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_right (hpoint v hv) (abs_nonneg _)
  calc
    |(∫ v in S, K p v * f v) - ∫ v in S, K p' v * f v| =
        |∫ v in S, (K p v * f v - K p' v * f v)| := by
      rw [integral_sub hwi hwi']
    _ ≤ ∫ v in S, |K p v * f v - K p' v * f v| :=
      by simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict S)
          (fun v => K p v * f v - K p' v * f v)).trans_eq rfl
    _ ≤ ∫ v in S, C * |f v| :=
      MeasureTheory.integral_mono_ae hdiff.norm hmajor hbound
    _ = C * ∫ v in S, |f v| := by rw [integral_const_mul]

/--
@isnad1 id=le.5h4v.s7.b90e3fd3dca6 from=translated src=- shape=7eb9cb4e vocab=6481c5be
-/
lemma heatPotential_far_shell_bound {γ : ℝ} (hγ : γ < 1) {A : ℕ → ℝ}
    {C r : ℝ} (_ : 0 ≤ C) (_ : 0 ≤ r)
    (hA : ∀ j : ℕ, 0 ≤ A j)
    (hAj : ∀ j : ℕ, A j ≤ C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) :
    ∑' j : ℕ, A j ≤
      C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ := by
  have hq0 : 0 ≤ (2 : ℝ) ^ (γ - 1) := heat_morrey_geometric_ratio_nonneg
  have hq1 : (2 : ℝ) ^ (γ - 1) < 1 :=
    heat_morrey_geometric_ratio_lt_one hγ
  let g : ℕ → ℝ := fun j => C * r ^ γ *
    (2 : ℝ) ^ ((j : ℝ) * (γ - 1))
  have hg : Summable g := by
    let hgeo : Summable (fun j : ℕ =>
        (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) := by
      rw [show (fun j : ℕ => (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) =
          (fun j : ℕ => ((2 : ℝ) ^ (γ - 1)) ^ j) by
            funext j
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring]
      exact summable_geometric_of_lt_one hq0 hq1
    simpa only [g] using hgeo.mul_left (C * r ^ γ)
  have hterm : ∀ j : ℕ,
      A j ≤ (C * r ^ γ) * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
    intro j
    convert hAj j using 1
    ring
  have hsum : Summable A := by
    apply Summable.of_norm_bounded hg
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hA j)]
    exact hterm j
  have hsum_le : ∑' j : ℕ, A j ≤ ∑' j : ℕ, g j := by
    exact (le_abs_self _).trans
      (hsum.hasSum.norm_le_of_bounded hg.hasSum (fun j => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA j)]
        exact hterm j))
  calc
    ∑' j : ℕ, A j ≤ ∑' j : ℕ, g j := hsum_le
    _ = (C * r ^ γ) *
          (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
      rw [show (fun j : ℕ => g j) =
          (fun j : ℕ => (C * r ^ γ) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) by
            funext j
            rfl]
      rw [tsum_mul_left]
      rw [heat_morrey_geometric_series hγ]
    _ = C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ := by ring

/--
@isnad1 id=le.6h6v.s8.ae0e3cb5cf4b from=translated src=- shape=32d6ad2c vocab=3c2f95c9
-/
lemma heatPotential_near_far_sum_bound {γ : ℝ} (hγ : γ < 1)
    {Anear : ℝ} {A : ℕ → ℝ} {Cnear Cfar r : ℝ}
    (hnear : Anear ≤ Cnear * r ^ γ)
    (hA : ∀ j : ℕ, 0 ≤ A j)
    (hfar : ∀ j : ℕ,
      A j ≤ Cfar * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ)
    (hCfar : 0 ≤ Cfar) (hr : 0 ≤ r) :
    Anear + ∑' j : ℕ, A j ≤
      (Cnear + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) * r ^ γ := by
  have hfar' := heatPotential_far_shell_bound hγ hCfar hr hA hfar
  calc
    Anear + ∑' j : ℕ, A j ≤
        Cnear * r ^ γ + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ :=
      add_le_add hnear hfar'
    _ = (Cnear + Cfar * (1 - (2 : ℝ) ^ (γ - 1))⁻¹) * r ^ γ := by ring

/--
@isnad1 id=le.5h4v.s8.59ceb29eca5c from=translated src=- shape=74051eba vocab=3c2f95c9
-/
lemma heatPotential_far_shell_sum_from_six {γ : ℝ} (hγ : γ < 1)
    {A : ℕ → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hA : ∀ j : ℕ, 0 ≤ A j)
    (hAj : ∀ j : ℕ,
      A (j + 6) ≤ C * (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) * r ^ γ) :
    ∑' j : ℕ, A (j + 6) ≤
      C * (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) *
        (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ := by
  let C₆ : ℝ := C * (2 : ℝ) ^ ((6 : ℝ) * (γ - 1))
  have hC₆ : 0 ≤ C₆ := by
    dsimp [C₆]
    exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hAj' : ∀ j : ℕ,
      A (j + 6) ≤ C₆ * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    intro j
    have hsplit :
        (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) =
          (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
      rw [Nat.cast_add, add_mul, Real.rpow_add (by norm_num)]
      ring_nf
    calc
      A (j + 6) ≤ C * (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) * r ^ γ := hAj j
      _ = C₆ * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
        rw [hsplit]
        dsimp [C₆]
        ring
  have hsum := heatPotential_far_shell_bound hγ hC₆ hr
    (fun j => hA (j + 6)) hAj'
  simpa [C₆, mul_assoc, mul_left_comm, mul_comm] using hsum

end CKN.Core.HeatPotential
