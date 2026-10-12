/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
module

public import Tengoku

/-!
# Derivatives of Moment and Cumulant Generating Functions

Auxiliary results for differentiating exponential moments, tilted expectations, and cumulant
generating functions.

## Main definitions

This module extends Mathlib's existing moment-generating and tilted-measure definitions.

## Main results

* `ProbabilityTheory.tilt_first_deriv`: first derivative of an exponential moment.
* `ProbabilityTheory.tilt_second_deriv`: second derivative of an exponential moment.
* `ProbabilityTheory.cgf_deriv_one`: first derivative of the cumulant generating function.
* `ProbabilityTheory.cgf_deriv_two`: second derivative of the cumulant generating function.
-/

@[expose] public section

namespace LeanPool

open MeasureTheory Filter Finset Real
open _root_.ProbabilityTheory

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω}

section GeneratingFunctionDerivatives

lemma aemeasurable_expt {X : Ω → ℝ} (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω ↦ rexp (t * (X ω))) μ :=
  aestronglyMeasurable_iff_aemeasurable.mpr <| measurable_exp.comp_aemeasurable' (hX.const_mul t)

lemma integrable_expt [IsFiniteMeasure μ] {X : Ω → ℝ} (t b : ℝ) (ht : t > 0)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  have hm1 : HasFiniteIntegral (fun ω ↦ rexp (t * X ω)) μ := by
    have b' : ∀ᵐ ω ∂μ, rexp (t * X ω) ≤ rexp (t * b) := by
      filter_upwards [hb] with ω hb
      using exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb (le_of_lt ht))
    have p : ∀ᵐ ω ∂μ, ‖rexp (t * X ω)‖₊ ≤ rexp (t * b) := by
      filter_upwards [b'] with ω b'
      rw [(by simp : ‖rexp (t * X ω)‖₊ = rexp (t * X ω))]
      exact b'
    have p'' : ∫⁻ ω, ‖rexp (t * X ω)‖₊ ∂μ ≤ ∫⁻ _, ‖rexp (t * b)‖₊ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [p] with ω p
      simp only [ENNReal.coe_le_coe]
      rw [← (by simp : ‖rexp (t * b)‖₊ = rexp (t * b))] at p
      exact p
    suffices ∫⁻ _, ↑‖rexp (t * b)‖₊ ∂μ < ⊤ from lt_of_le_of_lt p'' this
    simp only [lintegral_const]
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top (IsFiniteMeasure.measure_univ_lt_top)
  exact ⟨aestronglyMeasurable_iff_aemeasurable.mpr <|
    measurable_exp.comp_aemeasurable' (hX.const_mul t), hm1⟩

lemma integrable_expt_bound [IsFiniteMeasure μ] {X : Ω → ℝ} {t a b : ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  cases lt_trichotomy t 0 with
  | inr ht => cases ht with
    | inr ht => exact integrable_expt t b ht hX (h.mono fun ω h ↦ h.2)
    | inl ht => rw [ht]; simp only [zero_mul, exp_zero, integrable_const]
  | inl ht =>
    rw [(by ext ω; rw [(by ring : - t * (- X ω) = t * X ω)] :
      (fun ω ↦ rexp (t * X ω)) = (fun ω ↦ rexp (- t * (- X ω))))]
    apply integrable_expt (-t) _ _ hX.neg
    · filter_upwards [h] with ω h
      apply neg_le_neg h.1
    · exact Left.neg_pos_iff.mpr ht

lemma tilt_var_bound [IsProbabilityMeasure μ] (a b t : ℝ) {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hX : AEMeasurable X μ) :
    variance X (μ.tilted (fun ω ↦ t * X ω)) ≤ ((b - a) / 2) ^ 2 := by
  have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
    isProbabilityMeasure_tilted (integrable_expt_bound hX h)
  exact variance_le_sq_of_bounded
      ((tilted_absolutelyContinuous μ fun ω ↦ t * X ω) h)
      (hX.mono_ac (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))

theorem integrable_bounded [IsFiniteMeasure μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ := by
  have m1 : HasFiniteIntegral X μ := by
     apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
     filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω using abs_le_max_abs_abs
  exact ⟨aestronglyMeasurable_iff_aemeasurable.mpr hX, m1⟩

theorem integrable_deriv_expt [IsFiniteMeasure μ] (t a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ rexp (t * X ω) * X ω) μ := by
  apply MeasureTheory.Integrable.bdd_mul
    (integrable_bounded a b hX h) (aemeasurable_expt _ hX)
  · set c := max ‖a‖ ‖b‖
    filter_upwards [h] with ω h
    change ‖rexp (t * X ω)‖ ≤ ‖rexp (|t| * c)‖
    simp only [norm_eq_abs, abs_exp, exp_le_exp]
    rw [← (abs_eq_self.mpr (le_trans' (le_max_left |a| ‖b‖) (abs_nonneg a)) : |c| = c)]
    calc
    _ ≤ |t * X ω| := le_abs_self (t * X ω)
    _ = |t| * |X ω| := abs_mul t (X ω)
    _ ≤ |t| * |c| :=
      mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
        (abs_le_max_abs_abs h.1 h.2) : |X ω| ≤ |c|) (abs_nonneg t)

theorem integral_tilted [IsFiniteMeasure μ]
    (t : ℝ) (f : ℝ → ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ f (X ω)] =
    (μ[fun ω ↦ rexp (t * X ω) * f (X ω)]) / mgf X μ t := by
  calc
  _ = (∫ ω, ((∂Measure.tilted μ fun ω ↦ t * X ω/∂μ) ω).toReal • f (X ω) ∂μ) :=
    Eq.symm (MeasureTheory.integral_rnDeriv_smul (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))
  _ = ∫ ω, (rexp (t * X ω) / μ[fun ω ↦ rexp (t * X ω)]) * f (X ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [rnDeriv_tilted_left_self (hX.const_mul t)] with ω w
    rw [w]
    simp only [smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
    left
    have q2 : 0 ≤ μ[fun ω ↦ rexp (t * X ω)] := by
      apply integral_nonneg
      apply Pi.le_def.mpr _
      intro i
      simp only [Pi.zero_apply]
      exact exp_nonneg (t * X i)
    exact div_nonneg (exp_nonneg (t * X ω)) q2
  _ = (∫ ω, (rexp (t * X ω) * f (X ω)) / (μ[fun ω ↦ rexp (t * X ω)]) ∂μ) := by
    refine integral_congr_ae (ae_of_all μ fun a ↦ ?_)
    simp only
    ring
  _ = (∫ ω, rexp (t * X ω) * f (X ω) ∂μ) / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_div (μ[fun ω ↦ rexp (t * X ω)]) fun a ↦ rexp (t * X a) * f (X a)

/-! ### Derivatives of cumulant-/

end GeneratingFunctionDerivatives

end ProbabilityTheory

end

end LeanPool
