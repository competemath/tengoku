/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentSeriesMGF
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentMartingale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact-series strong-moment martingale bounds

This file transports the exact exponential-series remainder from
`StrongMomentSeriesMGF` to conditional expectations, upper-truncated
martingale differences, finite adapted sums, and finally CVaR.  The last
result is parameterized by the Laplace parameter and the truncation height;
optimization is deliberately left to the analytic Rio--Marchina layer.

Unlike the Lagrange-remainder version, the exponential part retains
`expSeriesTail q (t * y) / y ^ q`.  Restoring the discarded upper tails uses
the sharp Bernoulli residual factor `1 / q` already established in
`StrongMomentMartingale`.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

/-! ## Deterministic monotonicity -/

/-- The exact-series exponent is monotone in all of its deterministic
moment proxies.
@isnad1 id=le.5h7v.s6.e839d225a658 from=translated src=- shape=51a7ddfc vocab=95f32f73
-/
theorem strongMomentSeriesExponent_mono
    (q : ℕ) (hq : 3 ≤ q) {t y second second' : ℝ}
    (ht : 0 ≤ t) (hy : 0 < y) (hsecond : second ≤ second')
    {moment moment' : ℕ → ℝ}
    (hmoment : ∀ k ∈ Finset.Icc 2 q, moment k ≤ moment' k) :
    strongMomentSeriesExponent q t y second moment ≤
      strongMomentSeriesExponent q t y second' moment' := by
  unfold strongMomentSeriesExponent
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
    exact div_nonneg
      (expSeriesTail_nonneg (mul_nonneg ht hy.le) q)
      (pow_nonneg hy.le q)

/-! ## Conditional exact-series estimate -/

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

/-- Conditional-kernel lift of
`integral_exp_mul_le_exp_strongMomentSeriesExponent`, with deterministic
upper bounds on all conditional moment proxies.
@isnad1 id=eventual.11h10v.s8.b3eba039c5af from=translated src=- shape=45e4210c vocab=511865ab
-/
theorem condExp_exp_mul_le_exp_strongMomentSeriesExponent
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (X : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y second : ℝ} (ht : 0 ≤ t) (hy : 0 < y)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega => X omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (X omega) 0) ^ k) mu)
    (hupper : ∀ᵐ omega ∂mu, X omega ≤ y)
    (hcenter : mu[X | m] ≤ᵐ[mu] 0)
    (hsecond : mu[fun omega => X omega ^ 2 | m] ≤ᵐ[mu]
      fun _ => second)
    (moment : ℕ → ℝ)
    (hmoment : ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega => (max (X omega) 0) ^ k | m] ≤ᵐ[mu]
        fun _ => moment k) :
    ∀ᵐ omega ∂mu,
      mu[fun z => Real.exp (t * X z) | m] omega ≤
        Real.exp (strongMomentSeriesExponent q t y second moment) := by
  have hExp : Integrable (fun omega => Real.exp (t * X omega)) mu := by
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
      Integrable (fun z => X z ^ 2) (condExpKernel mu m omega) := by
    apply Measure.ae_integrable_of_integrable_comp
    rw [condExpKernel_comp_trim hm]
    exact hXsq
  have hpowKernel : ∀ᵐ omega ∂mu.trim hm,
      ∀ k ∈ Finset.Icc 2 q,
        Integrable (fun z => (max (X z) 0) ^ k)
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
      fun omega => ∫ z, X z ∂condExpKernel mu m omega :=
    condExp_ae_eq_trim_integral_condExpKernel hm hX
  have hsecondKernel : mu[fun z => X z ^ 2 | m] =ᵐ[mu.trim hm]
      fun omega => ∫ z, X z ^ 2 ∂condExpKernel mu m omega :=
    condExp_ae_eq_trim_integral_condExpKernel hm hXsq
  have hmomentKernel : ∀ᵐ omega ∂mu.trim hm,
      ∀ k ∈ Finset.Icc 2 q,
        mu[fun z => (max (X z) 0) ^ k | m] omega =
          ∫ z, (max (X z) 0) ^ k ∂condExpKernel mu m omega := by
    rw [(Finset.Icc 2 q).eventually_all]
    intro k hk
    exact condExp_ae_eq_trim_integral_condExpKernel hm (hpow k hk)
  have hcenterTrim : mu[X | m] ≤ᵐ[mu.trim hm] 0 :=
    StronglyMeasurable.ae_le_trim_of_stronglyMeasurable
      hm stronglyMeasurable_condExp stronglyMeasurable_zero hcenter
  have hsecondTrim :
      mu[fun z => X z ^ 2 | m] ≤ᵐ[mu.trim hm] fun _ => second :=
    StronglyMeasurable.ae_le_trim_of_stronglyMeasurable
      hm stronglyMeasurable_condExp stronglyMeasurable_const hsecond
  have hmomentTrim : ∀ᵐ omega ∂mu.trim hm,
      ∀ k ∈ Finset.Icc 2 q,
        mu[fun z => (max (X z) 0) ^ k | m] omega ≤ moment k := by
    rw [(Finset.Icc 2 q).eventually_all]
    intro k hk
    exact StronglyMeasurable.ae_le_trim_of_stronglyMeasurable
      hm stronglyMeasurable_condExp stronglyMeasurable_const (hmoment k hk)
  have hExpKernel : mu[fun z => Real.exp (t * X z) | m] =ᵐ[mu.trim hm]
      fun omega => ∫ z, Real.exp (t * X z) ∂condExpKernel mu m omega :=
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
  let fiberMoment : ℕ → ℝ := fun k =>
    ∫ z, (max (X z) 0) ^ k ∂condExpKernel mu m omega
  have hmomentFiber : ∀ k ∈ Finset.Icc 2 q,
      fiberMoment k ≤ moment k := by
    intro k hk
    unfold fiberMoment
    rw [← hmomentOmega k hk]
    exact hmomentBoundOmega k hk
  have hbase := integral_exp_mul_le_exp_strongMomentSeriesExponent
    (mu := condExpKernel mu m omega) X q hq ht hy hXOmega hXsqOmega
      hpowOmega hupperOmega hcenterFiber
  have hexponent :
      strongMomentSeriesExponent q t y
          (∫ z, X z ^ 2 ∂condExpKernel mu m omega) fiberMoment ≤
        strongMomentSeriesExponent q t y second moment :=
    strongMomentSeriesExponent_mono q hq ht hy
      hsecondFiber hmomentFiber
  rw [hExpOmega]
  exact hbase.trans (Real.exp_monotone hexponent)

/-! ## Upper truncation -/

/-- The unconditional exact-series estimate for an upper-truncated centred
variable.  Moment hypotheses refer to the original variable.
@isnad1 id=le.9h9v.s8.65555bea8e3a from=translated src=- shape=2dc95ca6 vocab=b07f2264
-/
theorem integral_exp_mul_upperTruncation_le_exp_strongMomentSeriesExponent
    [IsProbabilityMeasure mu]
    (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y second : ℝ} (ht : 0 ≤ t) (hy : 0 < y)
    (hD : Integrable D mu)
    (hDsq : Integrable (fun omega => D omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (D omega) 0) ^ k) mu)
    (hcenter : ∫ omega, D omega ∂mu = 0)
    (hsecond : (∫ omega, D omega ^ 2 ∂mu) ≤ second)
    (moment : ℕ → ℝ)
    (hmoment : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (D omega) 0) ^ k ∂mu) ≤ moment k) :
    (∫ omega, Real.exp (t * upperTruncation D y omega) ∂mu) ≤
      Real.exp (strongMomentSeriesExponent q t y second moment) := by
  let U : Omega → ℝ := upperTruncation D y
  have hU : Integrable U mu := integrable_upperTruncation hD y
  have hUsq : Integrable (fun omega => U omega ^ 2) mu :=
    integrable_sq_upperTruncation hD.aemeasurable hDsq hy.le
  have hUpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (U omega) 0) ^ k) mu := by
    intro k hk
    exact integrable_pow_max_upperTruncation_zero
      hD.aemeasurable y k (hpow k hk)
  have hmeanU : (∫ omega, U omega ∂mu) ≤ 0 := by
    calc
      (∫ omega, U omega ∂mu) ≤ ∫ omega, D omega ∂mu :=
        integral_mono hU hD
          (fun omega => upperTruncation_le_self D y omega)
      _ = 0 := hcenter
  have hsecondU : (∫ omega, U omega ^ 2 ∂mu) ≤ second := by
    calc
      (∫ omega, U omega ^ 2 ∂mu) ≤
          ∫ omega, D omega ^ 2 ∂mu :=
        integral_mono hUsq hDsq
          (fun omega => sq_upperTruncation_le_sq_self D hy.le omega)
      _ ≤ second := hsecond
  let UMoment : ℕ → ℝ := fun k =>
    ∫ omega, (max (U omega) 0) ^ k ∂mu
  have hmomentU : ∀ k ∈ Finset.Icc 2 q, UMoment k ≤ moment k := by
    intro k hk
    unfold UMoment
    calc
      (∫ omega, (max (U omega) 0) ^ k ∂mu) ≤
          ∫ omega, (max (D omega) 0) ^ k ∂mu :=
        integral_mono (hUpow k hk) (hpow k hk)
          (fun omega =>
            pow_max_upperTruncation_zero_le_pow_max_self D y k omega)
      _ ≤ moment k := hmoment k hk
  have hbase := integral_exp_mul_le_exp_strongMomentSeriesExponent
    U q hq ht hy hU hUsq hUpow
      (ae_of_all mu fun omega => upperTruncation_le D y omega) hmeanU
  exact hbase.trans (Real.exp_monotone
    (strongMomentSeriesExponent_mono q hq ht hy hsecondU hmomentU))

/-- Conditional exact-series estimate for an upper-truncated martingale
difference.
@isnad1 id=eventual.10h10v.s8.197f7f2e01c6 from=translated src=- shape=55768d0e vocab=6dc0eed4
-/
theorem condExp_exp_mul_upperTruncation_le_exp_strongMomentSeriesExponent
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y second : ℝ} (ht : 0 ≤ t) (hy : 0 < y)
    (hD : Integrable D mu)
    (hDsq : Integrable (fun omega => D omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (D omega) 0) ^ k) mu)
    (hcenter : mu[D | m] =ᵐ[mu] 0)
    (hsecond : mu[fun omega => D omega ^ 2 | m] ≤ᵐ[mu]
      fun _ => second)
    (moment : ℕ → ℝ)
    (hmoment : ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega => (max (D omega) 0) ^ k | m] ≤ᵐ[mu]
        fun _ => moment k) :
    ∀ᵐ omega ∂mu,
      mu[fun z => Real.exp (t * upperTruncation D y z) | m] omega ≤
        Real.exp (strongMomentSeriesExponent q t y second moment) := by
  let U : Omega → ℝ := upperTruncation D y
  have hU : Integrable U mu := integrable_upperTruncation hD y
  have hUsq : Integrable (fun omega => U omega ^ 2) mu :=
    integrable_sq_upperTruncation hD.aemeasurable hDsq hy.le
  have hUpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (U omega) 0) ^ k) mu := by
    intro k hk
    exact integrable_pow_max_upperTruncation_zero
      hD.aemeasurable y k (hpow k hk)
  have hcenterU : mu[U | m] ≤ᵐ[mu] 0 := by
    have hmono := condExp_mono (m := m) hU hD
      (ae_of_all mu fun omega => upperTruncation_le_self D y omega)
    filter_upwards [hmono, hcenter] with omega hle heq
    simpa only [heq] using hle
  have hsecondU : mu[fun omega => U omega ^ 2 | m] ≤ᵐ[mu]
      fun _ => second := by
    have hmono := condExp_mono (m := m) hUsq hDsq
      (ae_of_all mu fun omega =>
        sq_upperTruncation_le_sq_self D hy.le omega)
    exact hmono.trans hsecond
  have hmomentU : ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega => (max (U omega) 0) ^ k | m] ≤ᵐ[mu]
        fun _ => moment k := by
    intro k hk
    have hmono := condExp_mono (m := m) (hUpow k hk) (hpow k hk)
      (ae_of_all mu fun omega =>
        pow_max_upperTruncation_zero_le_pow_max_self D y k omega)
    exact hmono.trans (hmoment k hk)
  exact condExp_exp_mul_le_exp_strongMomentSeriesExponent
    hm U q hq ht hy hU hUsq hUpow
      (ae_of_all mu fun omega => upperTruncation_le D y omega)
      hcenterU hsecondU moment hmomentU

/-! ## One-sided MGF certificates -/

/-- Ordinary exact-series MGF certificate for an upper truncation.
@isnad1 id=hasonesi.8h8v.s8.f3c89c397e3e from=translated src=- shape=29aca9c2 vocab=31d2eb4d
-/
theorem hasOneSidedMGF_upperTruncation_of_strongMomentSeries
    [IsProbabilityMeasure mu]
    (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {y second : ℝ} (hy : 0 < y)
    (hD : Integrable D mu)
    (hDsq : Integrable (fun omega => D omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (D omega) 0) ^ k) mu)
    (hcenter : ∫ omega, D omega ∂mu = 0)
    (hsecond : (∫ omega, D omega ^ 2 ∂mu) ≤ second)
    (moment : ℕ → ℝ)
    (hmoment : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (D omega) 0) ^ k ∂mu) ≤ moment k) :
    HasOneSidedMGF (upperTruncation D y)
      (fun t => strongMomentSeriesExponent q t y second moment) mu := by
  have hU : Integrable (upperTruncation D y) mu :=
    integrable_upperTruncation hD y
  refine
    { aemeasurable := hU.aemeasurable
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t ht
    apply Integrable.of_bound
      ((hU.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (Real.exp (t * y))
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_monotone
      (mul_le_mul_of_nonneg_left (upperTruncation_le D y omega) ht)
  · intro t ht
    exact
      integral_exp_mul_upperTruncation_le_exp_strongMomentSeriesExponent
        D q hq ht hy hD hDsq hpow hcenter hsecond moment hmoment

/-- Conditional exact-series MGF certificate for an upper truncation.
@isnad1 id=hascondo.9h9v.s8.96f725e85792 from=translated src=- shape=d33d4ee0 vocab=664d1c68
-/
theorem hasCondOneSidedMGF_upperTruncation_of_strongMomentSeries
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {y second : ℝ} (hy : 0 < y)
    (hD : Integrable D mu)
    (hDsq : Integrable (fun omega => D omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (D omega) 0) ^ k) mu)
    (hcenter : mu[D | m] =ᵐ[mu] 0)
    (hsecond : mu[fun omega => D omega ^ 2 | m] ≤ᵐ[mu]
      fun _ => second)
    (moment : ℕ → ℝ)
    (hmoment : ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega => (max (D omega) 0) ^ k | m] ≤ᵐ[mu]
        fun _ => moment k) :
    HasCondOneSidedMGF m hm (upperTruncation D y)
      (fun t => strongMomentSeriesExponent q t y second moment) mu := by
  have hU : Integrable (upperTruncation D y) mu :=
    integrable_upperTruncation hD y
  refine
    { aemeasurable := hU.aemeasurable
      integrable_exp_mul := ?_
      cond_mgf_le := ?_ }
  · intro t ht
    apply Integrable.of_bound
      ((hU.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (Real.exp (t * y))
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_monotone
      (mul_le_mul_of_nonneg_left (upperTruncation_le D y omega) ht)
  · intro t ht
    exact
      condExp_exp_mul_upperTruncation_le_exp_strongMomentSeriesExponent
        hm D q hq ht hy hD hDsq hpow hcenter hsecond moment hmoment

/-! ## Composition along a filtration -/

variable (filtration : Filtration ℕ mOmega)

/-- A finite adapted family of upper-truncated martingale differences has
the exact-series exponent obtained by adding its deterministic conditional
moment proxies.
@isnad1 id=hasonesi.13h10v.s9.da9320b0c35c from=translated src=- shape=9fac85ac vocab=d04e3c71
-/
theorem hasOneSidedMGF_sum_upperTruncation_of_strongMomentSeries
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hAdapted : StronglyAdapted filtration D)
    (second : ℕ → ℝ) (moment : ℕ → ℕ → ℝ)
    (n q : ℕ) (hn : 0 < n) (hq : 3 ≤ q)
    {y : ℝ} (hy : 0 < y)
    (hD : ∀ i < n, Integrable (D i) mu)
    (hDsq : ∀ i < n, Integrable (fun omega => D i omega ^ 2) mu)
    (hpow : ∀ i < n, ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (D i omega) 0) ^ k) mu)
    (hcenter0 : ∫ omega, D 0 omega ∂mu = 0)
    (hcenterSucc : ∀ i < n - 1,
      mu[D (i + 1) | filtration i] =ᵐ[mu] 0)
    (hsecond0 : (∫ omega, D 0 omega ^ 2 ∂mu) ≤ second 0)
    (hsecondSucc : ∀ i < n - 1,
      mu[fun omega => D (i + 1) omega ^ 2 | filtration i] ≤ᵐ[mu]
        fun _ => second (i + 1))
    (hmoment0 : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (D 0 omega) 0) ^ k ∂mu) ≤ moment 0 k)
    (hmomentSucc : ∀ i < n - 1, ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega => (max (D (i + 1) omega) 0) ^ k | filtration i]
        ≤ᵐ[mu] fun _ => moment (i + 1) k) :
    HasOneSidedMGF
      (fun omega => ∑ i ∈ Finset.range n, upperTruncation (D i) y omega)
      (fun t => strongMomentSeriesExponent q t y
        (∑ i ∈ Finset.range n, second i)
        (fun k => ∑ i ∈ Finset.range n, moment i k)) mu := by
  let U : ℕ → Omega → ℝ := fun i => upperTruncation (D i) y
  let psi : ℕ → ℝ → ℝ := fun i t =>
    strongMomentSeriesExponent q t y (second i) (moment i)
  let B : ℕ → ℝ := fun _ => y
  have hUAdapted : StronglyAdapted filtration U := by
    intro i
    change StronglyMeasurable[filtration i]
      (fun omega => min (D i omega) y)
    exact ((hAdapted i).measurable.min measurable_const).stronglyMeasurable
  have hzero : HasOneSidedMGF (U 0) (psi 0) mu := by
    dsimp only [U, psi]
    exact hasOneSidedMGF_upperTruncation_of_strongMomentSeries
      (D 0) q hq hy (hD 0 hn) (hDsq 0 hn) (hpow 0 hn)
        hcenter0 hsecond0 (moment 0) hmoment0
  have hcond : ∀ i < n - 1,
      HasCondOneSidedMGF (filtration i) (filtration.le i)
        (U (i + 1)) (psi (i + 1)) mu := by
    intro i hi
    dsimp only [U, psi]
    exact hasCondOneSidedMGF_upperTruncation_of_strongMomentSeries
      (filtration.le i) (D (i + 1)) q hq hy
        (hD (i + 1) (by omega)) (hDsq (i + 1) (by omega))
        (hpow (i + 1) (by omega)) (hcenterSucc i hi)
        (hsecondSucc i hi) (moment (i + 1)) (hmomentSucc i hi)
  have hbound : ∀ i < n, ∀ᵐ omega ∂mu, U i omega ≤ B i := by
    intro i hi
    exact ae_of_all mu fun omega => upperTruncation_le (D i) y omega
  have hsum := HasOneSidedMGF.sum_of_hasCondOneSidedMGF
    filtration hUAdapted hzero n hbound hcond
  convert hsum using 1
  funext t
  dsimp only [psi]
  exact (sum_strongMomentSeriesExponent
    (Finset.range n) q t y second moment).symm

/-! ## CVaR endpoint -/

/-- Complete parameterized exact-series strong-moment martingale CVaR
bound.  The first term controls the upper-truncated martingale sum and the
second restores the residuals with the sharp factor `1 / q`.

No choice of `t` or `y` is made here.
@isnad1 id=le.16h12v.s9.12b08986da3a from=translated src=- shape=a98fd2e6 vocab=c443bdbf
-/
theorem conditionalValueAtRisk_sum_le_strongMomentSeriesExponent_add_residual
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hAdapted : StronglyAdapted filtration D)
    (second : ℕ → ℝ) (moment : ℕ → ℕ → ℝ)
    (n q : ℕ) (hn : 0 < n) (hq : 3 ≤ q)
    {y alpha t : ℝ} (hy : 0 < y)
    (hD : ∀ i < n, Integrable (D i) mu)
    (hDsq : ∀ i < n, Integrable (fun omega => D i omega ^ 2) mu)
    (hpow : ∀ i < n, ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (D i omega) 0) ^ k) mu)
    (hcenter0 : ∫ omega, D 0 omega ∂mu = 0)
    (hcenterSucc : ∀ i < n - 1,
      mu[D (i + 1) | filtration i] =ᵐ[mu] 0)
    (hsecond0 : (∫ omega, D 0 omega ^ 2 ∂mu) ≤ second 0)
    (hsecondSucc : ∀ i < n - 1,
      mu[fun omega => D (i + 1) omega ^ 2 | filtration i] ≤ᵐ[mu]
        fun _ => second (i + 1))
    (hmoment0 : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (D 0 omega) 0) ^ k ∂mu) ≤ moment 0 k)
    (hmomentSucc : ∀ i < n - 1, ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega => (max (D (i + 1) omega) 0) ^ k | filtration i]
        ≤ᵐ[mu] fun _ => moment (i + 1) k)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) (ht : 0 < t) :
    conditionalValueAtRisk alpha
        (fun omega => ∑ i ∈ Finset.range n, D i omega) mu ≤
      (strongMomentSeriesExponent q t y
          (∑ i ∈ Finset.range n, second i)
          (fun k => ∑ i ∈ Finset.range n, moment i k) -
        Real.log alpha) / t +
      alpha⁻¹ *
        ((∑ i ∈ Finset.range n, moment i q) /
          ((q : ℝ) * y ^ (q - 1))) := by
  have hqOne : 1 ≤ q := by omega
  have hqIcc : q ∈ Finset.Icc 2 q :=
    Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hpowq : ∀ i < n,
      Integrable (fun omega => (max (D i omega) 0) ^ q) mu := by
    intro i hi
    exact hpow i hi q hqIcc
  have hmgf :=
    hasOneSidedMGF_sum_upperTruncation_of_strongMomentSeries
      filtration D hAdapted second moment n q hn hq hy hD hDsq hpow
        hcenter0 hcenterSucc hsecond0 hsecondSucc hmoment0 hmomentSucc
  have hraw := conditionalValueAtRisk_sum_le_of_upperTruncation_mgf
      D n q hqOne hD hpowq
        (fun t => strongMomentSeriesExponent q t y
          (∑ i ∈ Finset.range n, second i)
          (fun k => ∑ i ∈ Finset.range n, moment i k))
        hy halpha0 halpha1 ht hmgf
  have hmomentQ : ∀ i < n,
      (∫ omega, (max (D i omega) 0) ^ q ∂mu) ≤ moment i q := by
    intro i hi
    cases i with
    | zero => exact hmoment0 q hqIcc
    | succ i =>
        have hiPred : i < n - 1 := by omega
        have hcond := hmomentSucc i hiPred q hqIcc
        have hint :
            (∫ omega,
                mu[fun z => (max (D (i + 1) z) 0) ^ q |
                  filtration i] omega ∂mu) ≤
              ∫ _ : Omega, moment (i + 1) q ∂mu :=
          integral_mono_ae integrable_condExp (integrable_const _) hcond
        rw [integral_condExp (filtration.le i), integral_const] at hint
        simpa only [probReal_univ, smul_eq_mul, one_mul] using hint
  have hsumMoment :
      (∑ i ∈ Finset.range n,
        ∫ omega, (max (D i omega) 0) ^ q ∂mu) ≤
        ∑ i ∈ Finset.range n, moment i q := by
    exact Finset.sum_le_sum fun i hi =>
      hmomentQ i (Finset.mem_range.mp hi)
  have hden : 0 < (q : ℝ) * y ^ (q - 1) := by positivity
  have hresidual :
      alpha⁻¹ *
          ((∑ i ∈ Finset.range n,
            ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
              ((q : ℝ) * y ^ (q - 1))) ≤
        alpha⁻¹ *
          ((∑ i ∈ Finset.range n, moment i q) /
            ((q : ℝ) * y ^ (q - 1))) := by
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hsumMoment hden.le)
      (inv_nonneg.mpr halpha0.le)
  exact hraw.trans (add_le_add le_rfl hresidual)

end ProbabilityTheory
