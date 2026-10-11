/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.ParamExtension
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.Slices

/-!
# I2

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

theorem caccioppoli_I2_slice_divfree_countable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {C : Set (Vec3 → ℝ)} (hC : C.Countable)
    (hCtest : ∀ ψ ∈ C, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I, ∀ ψ ∈ C,
      ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
  exact divfree_slice_weak_countable hsol.2.2.2.2.2.2.1 hsol.2.1 hC hCtest

theorem caccioppoli_I2_velocity_integral_identity
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
      ENNReal.ofReal (ρ ^ 2 * gamma u z ρ ^ 3) := by
  have hcube := gamma_cube_eq u z ρ hρ
  have hmul : ρ ^ 2 * gamma u z ρ ^ 3 =
      (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
    rw [hcube]
    rw [← mul_assoc]
    have hpow : ρ ^ 2 * ρ ^ (-2 : ℝ) = (1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hρ]
      norm_num
    rw [hpow, one_mul]
  rw [← ENNReal.ofReal_toReal hfin, hmul]

theorem caccioppoli_I2_holder
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : α → ℝ≥0∞} {C : ℝ≥0∞}
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hC : C ≠ ∞) :
    (∫⁻ x, C * A x * B x ∂μ) ≤
      C * (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (∫⁻ x, B x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) := by
  have hconj : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    hA hB
  calc
    (∫⁻ x, C * A x * B x ∂μ) = ∫⁻ x, C * (A x * B x) ∂μ := by
      apply lintegral_congr
      intro x
      ring
    _ = C * ∫⁻ x, A x * B x ∂μ := by
      rw [lintegral_const_mul' C (fun x => A x * B x) hC]
    _ ≤ C * ((∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (∫⁻ x, B x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ)) := by
      gcongr
      simpa only [Pi.mul_apply,
        show (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) by norm_num,
        show (1 / (3 : ℝ)) = (1 / 3 : ℝ) by norm_num] using hholder
    _ = C * (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (∫⁻ x, B x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) := by ring

theorem caccioppoli_I2_normalization
    {κ α β γ K C₂₅ I₂ : ℝ} (hκ : 0 < κ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hKbound : K ≤ C₂₅ ^ 2)
    (hraw : I₂ ≤ K * κ⁻¹ ^ 2 * α * β * γ) :
    I₂ ≤ (C₂₅ * κ⁻¹ * α ^ (1 / 2 : ℝ) * β ^ (1 / 2 : ℝ) *
      γ ^ (1 / 2 : ℝ)) ^ 2 := by
  have hsqrt (x : ℝ) (hx : 0 ≤ x) :
      (x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hscale :
      (κ⁻¹ * α ^ (1 / 2 : ℝ) * β ^ (1 / 2 : ℝ) *
        γ ^ (1 / 2 : ℝ)) ^ 2 = κ⁻¹ ^ 2 * α * β * γ := by
    rw [mul_pow, mul_pow, mul_pow, hsqrt α hα, hsqrt β hβ, hsqrt γ hγ]
  calc
    I₂ ≤ K * (κ⁻¹ ^ 2 * α * β * γ) := by simpa [mul_assoc] using hraw
    _ ≤ C₂₅ ^ 2 * (κ⁻¹ ^ 2 * α * β * γ) := by
      gcongr
    _ = (C₂₅ * κ⁻¹ * α ^ (1 / 2 : ℝ) * β ^ (1 / 2 : ℝ) *
        γ ^ (1 / 2 : ℝ)) ^ 2 := by rw [← hscale]; ring

end CKN
