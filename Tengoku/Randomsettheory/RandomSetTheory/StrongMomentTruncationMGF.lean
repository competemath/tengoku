/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentConditionalMGF

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One-sided strong-moment MGF bounds after upper truncation

Rio's Fuk--Nagaev argument applies the one-sided exponential estimate to
`min D y`, where `D` is a martingale difference.  This file records the
transport from moment bounds on `D` to its upper truncation.  No recentering
is needed: `min D y ≤ D`, so its ordinary or conditional mean is
nonpositive whenever the mean of `D` is zero.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

/-- Ordinary strong-moment MGF estimate for an upper-truncated centred
variable.-/
theorem integral_exp_mul_upperTruncation_le_exp_strongMomentTaylorExponent
    [IsProbabilityMeasure mu]
    (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y second : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y)
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
      Real.exp (strongMomentTaylorExponent q t y second moment) := by
  let U : Omega → ℝ := upperTruncation D y
  have hU : Integrable U mu := integrable_upperTruncation hD y
  have hUsq : Integrable (fun omega => U omega ^ 2) mu := by
    exact integrable_sq_upperTruncation hD.aemeasurable hDsq hy
  have hUpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (U omega) 0) ^ k) mu := by
    intro k hk
    exact integrable_pow_max_upperTruncation_zero hD.aemeasurable y k (hpow k hk)
  have hmeanU : (∫ omega, U omega ∂mu) ≤ 0 := by
    calc
      (∫ omega, U omega ∂mu) ≤ ∫ omega, D omega ∂mu :=
        integral_mono hU hD (fun omega => upperTruncation_le_self D y omega)
      _ = 0 := hcenter
  have hsecondU : (∫ omega, U omega ^ 2 ∂mu) ≤ second := by
    calc
      (∫ omega, U omega ^ 2 ∂mu) ≤ ∫ omega, D omega ^ 2 ∂mu :=
        integral_mono hUsq hDsq
          (fun omega => sq_upperTruncation_le_sq_self D hy omega)
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
  have hbase := integral_exp_mul_le_exp_strongMomentTaylorExponent
    U q hq ht hy hU hUsq hUpow
      (ae_of_all mu fun omega => upperTruncation_le D y omega) hmeanU
  exact hbase.trans (Real.exp_monotone
    (strongMomentTaylorExponent_mono q hq (y := y) ht hsecondU hmomentU))

/-- Conditional strong-moment MGF estimate for an upper-truncated martingale
difference.  All deterministic moment bounds are assumed for the original
difference and inherited monotonically by the truncation.-/
theorem condExp_exp_mul_upperTruncation_le_exp_strongMomentTaylorExponent
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y second : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y)
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
        Real.exp (strongMomentTaylorExponent q t y second moment) := by
  let U : Omega → ℝ := upperTruncation D y
  have hU : Integrable U mu := integrable_upperTruncation hD y
  have hUsq : Integrable (fun omega => U omega ^ 2) mu := by
    exact integrable_sq_upperTruncation hD.aemeasurable hDsq hy
  have hUpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (U omega) 0) ^ k) mu := by
    intro k hk
    exact integrable_pow_max_upperTruncation_zero hD.aemeasurable y k (hpow k hk)
  have hcenterU : mu[U | m] ≤ᵐ[mu] 0 := by
    have hmono := condExp_mono (m := m) hU hD
      (ae_of_all mu fun omega => upperTruncation_le_self D y omega)
    filter_upwards [hmono, hcenter] with omega hle heq
    simpa only [heq] using hle
  have hsecondU : mu[fun omega => U omega ^ 2 | m] ≤ᵐ[mu]
      fun _ => second := by
    have hmono := condExp_mono (m := m) hUsq hDsq
      (ae_of_all mu fun omega => sq_upperTruncation_le_sq_self D hy omega)
    exact hmono.trans hsecond
  have hmomentU : ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega => (max (U omega) 0) ^ k | m] ≤ᵐ[mu]
        fun _ => moment k := by
    intro k hk
    have hmono := condExp_mono (m := m) (hUpow k hk) (hpow k hk)
      (ae_of_all mu fun omega =>
        pow_max_upperTruncation_zero_le_pow_max_self D y k omega)
    exact hmono.trans (hmoment k hk)
  exact condExp_exp_mul_le_exp_strongMomentTaylorExponent
    hm U q hq ht hy hU hUsq hUpow
      (ae_of_all mu fun omega => upperTruncation_le D y omega)
      hcenterU hsecondU moment hmomentU

end ProbabilityTheory
