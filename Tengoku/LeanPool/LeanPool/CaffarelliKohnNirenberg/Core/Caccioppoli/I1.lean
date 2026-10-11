/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Terms
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I1ProductRules

/-!
# I1

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat

noncomputable section

namespace CKN

theorem caccioppoli_I1_lintegral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U H : α → ℝ≥0∞} {C E : ℝ≥0∞}
    (hC : C ≠ ∞) (hHC : H ≤ᵐ[μ] fun _ => C)
    (hE : (∫⁻ x, U x ∂μ) ≤ E) :
    (∫⁻ x, U x * H x ∂μ) ≤ C * E := by
  calc
    (∫⁻ x, U x * H x ∂μ) ≤ ∫⁻ x, U x * C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hHC] with x hx
      simpa only [mul_comm (U x)] using mul_le_mul_left hx (U x)
    _ = C * ∫⁻ x, U x ∂μ := by
      calc
        (∫⁻ x, U x * C ∂μ) = ∫⁻ x, C * U x ∂μ := by
          apply lintegral_congr
          intro x
          rw [mul_comm]
        _ = C * ∫⁻ x, U x ∂μ :=
          lintegral_const_mul' C U hC
    _ ≤ C * E := by
      simpa only [mul_comm C] using mul_le_mul_left hE C

theorem caccioppoli_I1_toReal_lintegral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U H : α → ℝ≥0∞} {C E : ℝ≥0∞}
    (_ : AEMeasurable U μ) (_ : AEMeasurable H μ)
    (hC : C ≠ ∞) (hHC : H ≤ᵐ[μ] fun _ => C)
    (hE : (∫⁻ x, U x ∂μ) ≤ E)
    (hCE : C * E ≠ ∞) :
    (∫⁻ x, U x * H x ∂μ).toReal ≤ (C * E).toReal := by
  exact ENNReal.toReal_mono hCE
    (caccioppoli_I1_lintegral_bound hC hHC hE)

private theorem caccioppoli_energy_lintegral_bound
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ A : ℝ}
    (_ : 0 < ρ)
    (hU : AEMeasurable (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)))
    (hess : essSup (fun s =>
      ∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) = ENNReal.ofReal A) :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal A := by
  have hpow : AEMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    hU.pow_const (2 : ℝ)
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)),
      (∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
        ENNReal.ofReal A := by
    rw [← hess]
    exact ENNReal.ae_le_essSup (fun s =>
      ∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
  calc
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) =
        ∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ∫⁻ y in vec3Ball z.1 ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) :=
      lintegral_parabolicCylinder hpow
    _ ≤ ∫⁻ _s in Ioc (z.2 - ρ ^ 2) z.2, ENNReal.ofReal A := by
      apply lintegral_mono_ae
      exact hinner
    _ = ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal A := by
      have hμ :
          (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) Set.univ =
            ENNReal.ofReal (ρ ^ 2) := by
        simp [Real.volume_Ioc]
      rw [lintegral_const, hμ]
      ring

theorem caccioppoli_I1_normalization
    {ρ r α K C₂₅ I₁ : ℝ} (hρ : 0 < ρ) (_ : 0 < r)
    (hKbound : K ≤ C₂₅ ^ 2)
    (hraw : I₁ ≤ K * (r ^ 2 / ρ ^ 5) * (ρ ^ 3 * α ^ 2)) :
    I₁ ≤ (C₂₅ * (r / ρ) * α) ^ 2 := by
  have hscale : r ^ 2 / ρ ^ 5 * (ρ ^ 3 * α ^ 2) =
      (r / ρ) ^ 2 * α ^ 2 := by
    field_simp [hρ.ne']
  calc
    I₁ ≤ K * (r ^ 2 / ρ ^ 5) * (ρ ^ 3 * α ^ 2) := hraw
    _ = K * (r ^ 2 / ρ ^ 5 * (ρ ^ 3 * α ^ 2)) := by ring
    _ = K * ((r / ρ) ^ 2 * α ^ 2) := by rw [hscale]
    _ ≤ C₂₅ ^ 2 * ((r / ρ) ^ 2 * α ^ 2) := by
      gcongr
    _ = (C₂₅ * (r / ρ) * α) ^ 2 := by ring

theorem caccioppoli_I1_velocity_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (ρ ^ 3 * alpha u z ρ ^ 2) := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hnorm : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hu
  have hnorm' : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    hnorm.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hess : essSup (fun s =>
      ∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
      ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
    simpa only [timeSliceEnergyEssSup, timeSliceBallEnergy,
      Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)] using
      sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol z hρ hsub
  have henergy := caccioppoli_energy_lintegral_bound hρ hnorm'.aemeasurable hess
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ 2)] at henergy
  convert henergy using 1
  congr 1
  ring

end CKN
