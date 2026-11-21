/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentMGF
import Tengoku.Seed.Probability.Kernel.Condexp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional one-sided strong-moment MGF estimates

This file lifts the one-measure estimate from `StrongMomentMGF` to
conditional expectation.  The lift is performed on the probability fibres
of `condExpKernel`.  Deterministic bounds on the conditional second and
positive moments then replace the fibre moments by monotonicity of
`strongMomentTaylorExponent`.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

/-! ## Deterministic monotonicity -/

/-- The strong-moment Taylor exponent is monotone in every moment parameter
which it uses.-/
theorem strongMomentTaylorExponent_mono
    (q : ℕ) (hq : 3 ≤ q) {t y second second' : ℝ}
    (ht : 0 ≤ t) (hsecond : second ≤ second')
    {moment moment' : ℕ → ℝ}
    (hmoment : ∀ k ∈ Finset.Icc 2 q, moment k ≤ moment' k) :
    strongMomentTaylorExponent q t y second moment ≤
      strongMomentTaylorExponent q t y second' moment' := by
  unfold strongMomentTaylorExponent
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left hsecond (by positivity)
    · apply Finset.sum_le_sum
      intro k hk
      have hkBounds := Finset.mem_Ico.mp hk
      apply mul_le_mul_of_nonneg_left
        (hmoment k (Finset.mem_Icc.mpr
          ⟨(by omega : 2 ≤ k), hkBounds.2.le⟩))
      positivity
  · apply mul_le_mul_of_nonneg_left
      (hmoment q (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
    positivity

/-! ## Conditional-kernel lift -/

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

/-- **Conditional strong-moment MGF estimate.**

For `t ≥ 0`, an almost-sure upper bound and deterministic bounds on the
conditional second and positive moments give the same Taylor exponent as in
the unconditional theorem.  The conditional mean need only be nonpositive,
which is the form naturally satisfied by one-sided upper truncations of
martingale differences.-/
theorem condExp_exp_mul_le_exp_strongMomentTaylorExponent
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (X : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y second : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega ↦ X omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega ↦ (max (X omega) 0) ^ k) mu)
    (hupper : ∀ᵐ omega ∂mu, X omega ≤ y)
    (hcenter : mu[X | m] ≤ᵐ[mu] 0)
    (hsecond : mu[fun omega ↦ X omega ^ 2 | m] ≤ᵐ[mu]
      fun _ ↦ second)
    (moment : ℕ → ℝ)
    (hmoment : ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega ↦ (max (X omega) 0) ^ k | m] ≤ᵐ[mu]
        fun _ ↦ moment k) :
    ∀ᵐ omega ∂mu,
      mu[fun z ↦ Real.exp (t * X z) | m] omega ≤
        Real.exp (strongMomentTaylorExponent q t y second moment) := by
  have hExp : Integrable (fun omega ↦ Real.exp (t * X omega)) mu := by
    apply Integrable.of_bound
      ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (Real.exp (t * y))
    filter_upwards [hupper] with omega homega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_monotone (mul_le_mul_of_nonneg_left homega ht)
  have hXKernel : ∀ᵐ omega ∂mu.trim hm,
      Integrable X (condExpKernel mu m omega) := by
    apply Measure.ae_integrable_of_integrable_comp
    rw [condExpKernel_comp_trim hm]
    exact hX
  have hXsqKernel : ∀ᵐ omega ∂mu.trim hm,
      Integrable (fun z ↦ X z ^ 2) (condExpKernel mu m omega) := by
    apply Measure.ae_integrable_of_integrable_comp
    rw [condExpKernel_comp_trim hm]
    exact hXsq
  have hpowKernel : ∀ᵐ omega ∂mu.trim hm,
      ∀ k ∈ Finset.Icc 2 q,
        Integrable (fun z ↦ (max (X z) 0) ^ k)
          (condExpKernel mu m omega) := by
    rw [(Finset.Icc 2 q).eventually_all]
    intro k hk
    apply Measure.ae_integrable_of_integrable_comp
    rw [condExpKernel_comp_trim hm]
    exact hpow k hk
  have hupperKernel : ∀ᵐ omega ∂mu.trim hm,
      ∀ᵐ z ∂condExpKernel mu m omega, X z ≤ y := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim hm]
    exact hupper
  have hmeanKernel : mu[X | m] =ᵐ[mu.trim hm]
      fun omega ↦ ∫ z, X z ∂condExpKernel mu m omega :=
    condExp_ae_eq_trim_integral_condExpKernel hm hX
  have hsecondKernel : mu[fun z ↦ X z ^ 2 | m] =ᵐ[mu.trim hm]
      fun omega ↦ ∫ z, X z ^ 2 ∂condExpKernel mu m omega :=
    condExp_ae_eq_trim_integral_condExpKernel hm hXsq
  have hmomentKernel : ∀ᵐ omega ∂mu.trim hm,
      ∀ k ∈ Finset.Icc 2 q,
        mu[fun z ↦ (max (X z) 0) ^ k | m] omega =
          ∫ z, (max (X z) 0) ^ k ∂condExpKernel mu m omega := by
    rw [(Finset.Icc 2 q).eventually_all]
    intro k hk
    exact condExp_ae_eq_trim_integral_condExpKernel hm (hpow k hk)
  have hcenterTrim : mu[X | m] ≤ᵐ[mu.trim hm] 0 :=
    StronglyMeasurable.ae_le_trim_of_stronglyMeasurable
      hm stronglyMeasurable_condExp stronglyMeasurable_zero hcenter
  have hsecondTrim :
      mu[fun z ↦ X z ^ 2 | m] ≤ᵐ[mu.trim hm] fun _ ↦ second :=
    StronglyMeasurable.ae_le_trim_of_stronglyMeasurable
      hm stronglyMeasurable_condExp stronglyMeasurable_const hsecond
  have hmomentTrim : ∀ᵐ omega ∂mu.trim hm,
      ∀ k ∈ Finset.Icc 2 q,
        mu[fun z ↦ (max (X z) 0) ^ k | m] omega ≤ moment k := by
    rw [(Finset.Icc 2 q).eventually_all]
    intro k hk
    exact StronglyMeasurable.ae_le_trim_of_stronglyMeasurable
      hm stronglyMeasurable_condExp stronglyMeasurable_const (hmoment k hk)
  have hExpKernel : mu[fun z ↦ Real.exp (t * X z) | m] =ᵐ[mu.trim hm]
      fun omega ↦ ∫ z, Real.exp (t * X z) ∂condExpKernel mu m omega :=
    condExp_ae_eq_trim_integral_condExpKernel hm hExp
  apply ae_of_ae_trim hm
  filter_upwards [hXKernel, hXsqKernel, hpowKernel,
      hupperKernel, hmeanKernel, hsecondKernel, hmomentKernel,
      hcenterTrim, hsecondTrim, hmomentTrim, hExpKernel]
    with omega hXOmega hXsqOmega hpowOmega hupperOmega
      hmeanOmega hsecondOmega hmomentOmega hcenterOmega
      hsecondBoundOmega hmomentBoundOmega hExpOmega
  have hcenterFiber : (∫ z, X z ∂condExpKernel mu m omega) ≤ 0 := by
    rw [← hmeanOmega]
    exact hcenterOmega
  have hsecondFiber : (∫ z, X z ^ 2 ∂condExpKernel mu m omega) ≤
      second := by
    rw [← hsecondOmega]
    exact hsecondBoundOmega
  let fiberMoment : ℕ → ℝ := fun k ↦
    ∫ z, (max (X z) 0) ^ k ∂condExpKernel mu m omega
  have hmomentFiber : ∀ k ∈ Finset.Icc 2 q,
      fiberMoment k ≤ moment k := by
    intro k hk
    unfold fiberMoment
    rw [← hmomentOmega k hk]
    exact hmomentBoundOmega k hk
  have hbase := integral_exp_mul_le_exp_strongMomentTaylorExponent
    (mu := condExpKernel mu m omega) X q hq ht hy hXOmega hXsqOmega
      hpowOmega hupperOmega hcenterFiber
  have hexponent :
      strongMomentTaylorExponent q t y
          (∫ z, X z ^ 2 ∂condExpKernel mu m omega) fiberMoment ≤
        strongMomentTaylorExponent q t y second moment :=
    strongMomentTaylorExponent_mono q hq (y := y) ht
      hsecondFiber hmomentFiber
  rw [hExpOmega]
  exact hbase.trans (Real.exp_monotone hexponent)

end ProbabilityTheory
