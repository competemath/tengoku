/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Util.Concentration
public import Tengoku
/-!
# Exponential concentration of the tensor-product RY quantum kernel

The global-measurement example of Thanasilp et al. (2022): the fidelity kernel of the
embedding `U(x) = ⊗ₖ R_Y(xₖ)` is `κ(x,x') = ∏ₖ cos²((xₖ-x'ₖ)/2)`. By translation
invariance each coordinate reduces to a uniform variable on `[-π,π]`, so we study
`ryKernel n θ = ∏ₖ cos²(θₖ)`. Its moments are elementary (`𝔼[κ]=(1/2)ⁿ`,
`Var[κ]=(3/8)ⁿ-(1/4)ⁿ`), giving genuine exponential concentration with NO Haar assumption.
-/

@[expose] public section

namespace QuantumAlg

open MeasureTheory ProbabilityTheory Real intervalIntegral

/-- Uniform probability measure on `[-π, π]`. -/
noncomputable def unifAngle : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Icc (-Real.pi) Real.pi)

/-- The reduced tensor-product RY fidelity kernel `∏ₖ cos²(θₖ)`. -/
noncomputable def ryKernel (n : ℕ) (θ : Fin n → ℝ) : ℝ := ∏ k, Real.cos (θ k) ^ 2

/-- The data distribution: `n` independent uniform angles. -/
noncomputable def ryMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => unifAngle)

instance : IsProbabilityMeasure unifAngle := by
  refine ⟨?_⟩
  rw [unifAngle, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, Real.volume_Icc,
    show Real.pi - -Real.pi = 2 * Real.pi from by ring,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top]

theorem ryKernel_nonneg (n : ℕ) (θ : Fin n → ℝ) : 0 ≤ ryKernel n θ :=
  Finset.prod_nonneg (fun _ _ => sq_nonneg _)

theorem continuous_ryKernel (n : ℕ) : Continuous (ryKernel n) := by
  unfold ryKernel
  exact continuous_finsetProd _
    (fun k _ => (Real.continuous_cos.comp (continuous_apply k)).pow 2)

/-- `∫ cos²θ` over the uniform measure on `[-π,π]` equals `1/2`. -/
theorem integral_cos_sq_unifAngle : ∫ x, Real.cos x ^ 2 ∂unifAngle = 1 / 2 := by
  have hpi : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [unifAngle, MeasureTheory.integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpi, integral_cos_sq,
    Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  field_simp
  ring

/-- `∫ cos⁴θ` over the uniform measure on `[-π,π]` equals `3/8`. -/
theorem integral_cos_pow4_unifAngle : ∫ x, Real.cos x ^ 4 ∂unifAngle = 3 / 8 := by
  have hpi : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hI : ∫ x in (-Real.pi)..Real.pi, Real.cos x ^ 4 = 3 * Real.pi / 4 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, integral_cos_pow, integral_cos_sq,
      Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
    push_cast
    ring
  rw [unifAngle, MeasureTheory.integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpi, hI,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  field_simp
  ring

/-- First moment: `𝔼[κ_n] = (1/2)ⁿ`. -/
theorem mean_ryKernel (n : ℕ) : ∫ θ, ryKernel n θ ∂(ryMeasure n) = (1 / 2) ^ n := by
  unfold ryKernel ryMeasure
  rw [integral_fintype_prod_eq_pow (fun t => Real.cos t ^ 2), integral_cos_sq_unifAngle,
    Fintype.card_fin]

/-- Second moment: `𝔼[κ_n²] = (3/8)ⁿ`. -/
theorem mean_ryKernel_sq (n : ℕ) :
    ∫ θ, (ryKernel n θ) ^ 2 ∂(ryMeasure n) = (3 / 8) ^ n := by
  have hrw : (fun θ : Fin n → ℝ => (ryKernel n θ) ^ 2)
      = (fun θ => ∏ k, Real.cos (θ k) ^ 4) := by
    funext θ
    simp only [ryKernel, ← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun k _ => by ring)
  calc ∫ θ, (ryKernel n θ) ^ 2 ∂(ryMeasure n)
      = ∫ θ, ∏ k, Real.cos (θ k) ^ 4 ∂(ryMeasure n) := by rw [hrw]
    _ = (∫ x, Real.cos x ^ 4 ∂unifAngle) ^ (Fintype.card (Fin n)) := by
        unfold ryMeasure; rw [integral_fintype_prod_eq_pow (fun t => Real.cos t ^ 4)]
    _ = (3 / 8) ^ n := by rw [integral_cos_pow4_unifAngle, Fintype.card_fin]

end QuantumAlg
