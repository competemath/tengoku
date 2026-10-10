import Tengoku.Degiorgi.DeGiorgi.Common
import Tengoku.Degiorgi.DeGiorgi.WholeSpaceSobolev

noncomputable section

open MeasureTheory Metric Filter Set Function
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def C_poinc_val (d : ℕ) : ℝ :=
  2 ^ (d + 1) * d

/-- Pointwise Euclidean norm of the classical gradient of a smooth scalar
function, written in coordinates. This matches the weak-gradient norm used in
the Sobolev witness layer for smooth functions. -/
noncomputable def smoothGradNorm (u : E → ℝ) : E → ℝ :=
  fun x => ‖WithLp.toLp 2 (fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1))‖

theorem weighted_power_mean_setIntegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s)
    {p : ℝ} (hp : 1 < p)
    {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hw : ∀ x, 0 ≤ w x)
    (hf_meas : AEMeasurable f (μ.restrict s))
    (hwi : IntegrableOn w s μ)
    (hfpwi : IntegrableOn (fun x => (f x) ^ p * w x) s μ) :
    (∫ x in s, f x * w x ∂μ) ^ p ≤
      (∫ x in s, w x ∂μ) ^ (p - 1) * ∫ x in s, (f x) ^ p * w x ∂μ := by
  set μs : Measure α := μ.restrict s
  set ρ : α → ℝ≥0∞ := fun x => ENNReal.ofReal (w x)
  set ν : Measure α := μs.withDensity ρ
  let q : ℝ := p / (p - 1)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpq : p.HolderConjugate q := by
    dsimp [q]
    exact Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < q := hpq.symm.pos
  have hρ_aemeas : AEMeasurable ρ μs := by
    simpa [ρ, μs] using hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hρ_lt_top : ∀ᵐ x ∂μs, ρ x < ∞ := by
    filter_upwards with x
    simp [ρ]
  have hρ_lint_ne_top : ∫⁻ x, ρ x ∂μs ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ fun x => hw x)]
    simp
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hρ_lint_ne_top
  have hf_meas_ν : AEMeasurable f ν := by
    exact hf_meas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpow_int_base : Integrable (fun x => (ρ x).toReal • (‖f x‖ ^ p)) μs := by
    refine hfpwi.congr ?_
    filter_upwards with x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hw x), Real.norm_of_nonneg (hf x)]
    ring
  have hpow_int : Integrable (fun x => ‖f x‖ ^ p) ν := by
    rw [show ν = μs.withDensity ρ by rfl]
    exact
      (MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
        (μ := μs) hρ_aemeas hρ_lt_top).2 hpow_int_base
  have hf_mem : MemLp f (ENNReal.ofReal p) ν := by
    exact
      (MeasureTheory.integrable_norm_rpow_iff
        (μ := ν) hf_meas_ν.aestronglyMeasurable
        (by simp [hp_pos]) ENNReal.ofReal_ne_top).1 <| by
          simpa [ENNReal.toReal_ofReal hp_nonneg] using hpow_int
  have h_one_mem : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal q) ν := by
    simpa [q] using (MeasureTheory.memLp_const (μ := ν) (p := ENNReal.ofReal q) (1 : ℝ))
  have hHolder :
      ∫ x, f x * (1 : ℝ) ∂ν ≤
        (∫ x, (f x) ^ p ∂ν) ^ (1 / p : ℝ) *
          (∫ x, (1 : ℝ) ^ q ∂ν) ^ (1 / q : ℝ) := by
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := ν) hpq
      (ae_of_all _ fun x => hf x)
      (ae_of_all _ fun _ => by positivity)
      hf_mem h_one_mem
  have hleft_eq : ∫ x, f x ∂ν = ∫ x in s, f x * w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hpow_eq : ∫ x, (f x) ^ p ∂ν = ∫ x in s, (f x) ^ p * w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hone_eq : ∫ x, (1 : ℝ) ^ q ∂ν = ∫ x in s, w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, q, smul_eq_mul, ENNReal.toReal_ofReal, hw]
  set A := ∫ x in s, f x * w x ∂μ
  set I := ∫ x in s, (f x) ^ p * w x ∂μ
  set W := ∫ x in s, w x ∂μ
  have hA_nonneg : 0 ≤ A := by
    exact setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
  have hI_nonneg : 0 ≤ I := by
    exact setIntegral_nonneg hs (fun x _ =>
      mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))
  have hW_nonneg : 0 ≤ W := by
    exact setIntegral_nonneg hs (fun x _ => hw x)
  -- If ∫ w = 0, both sides are 0
  by_cases hW_zero : ∫ x in s, w x ∂μ = 0
  · -- Here `w = 0` a.e., so the weighted integral also vanishes.
    have hfw_nonneg : 0 ≤ ∫ x in s, f x * w x ∂μ :=
      setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
    have hfw_zero : ∫ x in s, f x * w x ∂μ ≤ 0 := by
      by_cases hfwi : IntegrableOn (fun x => f x * w x) s μ
      · -- w ≥ 0 and ∫ w = 0 → w =ᵃᵉ 0 → f·w =ᵃᵉ 0 → ∫ f·w = 0
        have hwi := hwi
        have hw_ae : w =ᵐ[μ.restrict s] 0 := by
          rwa [setIntegral_eq_zero_iff_of_nonneg_ae
            (ae_restrict_of_ae (ae_of_all _ (fun x => hw x))) hwi] at hW_zero
        have : (fun x => f x * w x) =ᵐ[μ.restrict s] 0 :=
          hw_ae.mono (fun x hx => by simp [hx])
        rw [integral_congr_ae this]; simp
      · simp [integral_undef hfwi]
    have h0 := le_antisymm hfw_zero hfw_nonneg
    -- h0 : ∫ f·w = 0, hW_zero : ∫ w = 0. Goal: 0^p ≤ 0^{p-1} * ∫ f^p·w
    simpa [A, I, W, h0, hW_zero] using
      (show A ^ p ≤ W ^ (p - 1) * I by
        simp [A, I, W, h0, hW_zero,
          mul_nonneg (Real.rpow_nonneg (le_refl _) _)
            (setIntegral_nonneg hs (fun x _ => mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))),
          Real.zero_rpow (by linarith : p ≠ 0)])
  · -- ∫ w > 0
    have hW_pos : 0 < ∫ x in s, w x ∂μ :=
      lt_of_le_of_ne (setIntegral_nonneg hs (fun x _ => hw x)) (Ne.symm hW_zero)
    have hνreal_eq : ν.real Set.univ = W := by
      calc
        ν.real Set.univ = ∫ x, (1 : ℝ) ∂ν := by
          rw [integral_const]
          simp [Measure.real]
        _ = ∫ x, (1 : ℝ) ^ q ∂ν := by simp [q]
        _ = W := hone_eq
    have hHolder' : A ≤ W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ) := by
      simpa [A, I, W, hleft_eq, hpow_eq, hνreal_eq, one_div, mul_comm, mul_left_comm, mul_assoc]
        using hHolder
    have hpow :=
      Real.rpow_le_rpow hA_nonneg hHolder' (le_of_lt hp_pos)
    have hWroot_nonneg : 0 ≤ W ^ (1 / q : ℝ) := Real.rpow_nonneg hW_nonneg _
    have hIroot_nonneg : 0 ≤ I ^ (1 / p : ℝ) := Real.rpow_nonneg hI_nonneg _
    have hq_ne_zero : q ≠ 0 := by linarith
    have hp_ne_zero : p ≠ 0 := by linarith
    have hrhs :
        (W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ)) ^ p = W ^ (p - 1) * I := by
      rw [Real.mul_rpow hWroot_nonneg hIroot_nonneg]
      rw [← Real.rpow_mul hW_nonneg, ← Real.rpow_mul hI_nonneg]
      have hWq : (1 / q : ℝ) * p = p - 1 := by
        dsimp [q]
        field_simp [hp_ne_zero, show p - 1 ≠ 0 by linarith]
      have hIp : (1 / p : ℝ) * p = 1 := by
        field_simp [hp_ne_zero]
      rw [hWq, hIp, Real.rpow_one]
    simpa [A, I, W] using hpow.trans_eq hrhs

end DeGiorgi
