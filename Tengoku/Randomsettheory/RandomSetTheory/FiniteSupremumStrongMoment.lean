/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumMartingaleBernstein
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentSeriesMartingale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strong-moment bounds for finite process suprema

This file connects the exact-series strong-moment martingale inequality to a
finite supremum.  The terminal supremum is expanded along its canonical Doob
martingale; adaptedness, centring, integrability, and telescoping are then
discharged internally.

The remaining assumptions are precisely deterministic upper bounds on the
conditional second and positive-part moments of the Doob differences.  In an
independent-coordinate application these bounds are supplied by a
replace-one/Efron--Stein argument.  Consequently the theorem below is a
genuine maximal CVaR endpoint, but it does not yet claim the specific moment
proxies or the optimized constants of the Rio--Marchina theorem.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T : Type*} {mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

variable (filtration : Filtration ℕ mOmega)

/-! ## Almost-everywhere invariance of CVaR -/

/-- Conditional value at risk only depends on the almost-everywhere class of
an integrable random variable.
@isnad1 id=eq.5h6v.s6.15f049ec5962 from=translated src=- shape=e1412f0a vocab=940e6a9d
-/
theorem conditionalValueAtRisk_congr_ae
    [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Integrable X mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hXY : X =ᵐ[mu] Y) :
    conditionalValueAtRisk alpha X mu =
      conditionalValueAtRisk alpha Y mu := by
  apply le_antisymm
  · exact conditionalValueAtRisk_mono_ae
      hX hY halpha0 halpha1 hXY.le
  · exact conditionalValueAtRisk_mono_ae
      hY hX halpha0 halpha1 hXY.symm.le

/-! ## Finite maximal endpoint -/

/-- Exact-series strong-moment CVaR bound for a finite process supremum
centred by its expectation.

The index `0` is the initial centred Doob increment and indices `k+1` are
conditioned on `filtration k`.  All structural martingale hypotheses and the
terminal telescoping identity are proved in this theorem.  Only the
deterministic conditional moment bounds remain as inputs.
@isnad1 id=le.16h15v.s10.fe2435ddae85 from=translated src=- shape=8483b4f4 vocab=a0f7a0bb
-/
theorem conditionalValueAtRisk_finiteProcessSupremum_sub_integral_le_strongMomentSeries
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu filtration]
    (s : Finset T) (hs : s.Nonempty) (X : T → Omega → ℝ)
    (A : Omega → ℝ) (hA : Integrable A mu)
    (hX : ∀ u ∈ s, Measurable (X u))
    (hdom : ∀ omega u, u ∈ s → |X u omega| ≤ |A omega|)
    (second : ℕ → ℝ) (moment : ℕ → ℕ → ℝ)
    (n q : ℕ) (hq : 3 ≤ q)
    (hterminal : mu[finiteProcessSupremum s hs X | filtration n]
      =ᵐ[mu] finiteProcessSupremum s hs X)
    (hDsq : ∀ i < n + 1, Integrable (fun omega ↦
      doobCenteredDifference filtration mu
        (finiteProcessSupremum s hs X) i omega ^ 2) mu)
    (hpow : ∀ i < n + 1, ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega ↦
        (max (doobCenteredDifference filtration mu
          (finiteProcessSupremum s hs X) i omega) 0) ^ k) mu)
    (hsecond0 : (∫ omega,
      doobCenteredDifference filtration mu
        (finiteProcessSupremum s hs X) 0 omega ^ 2 ∂mu) ≤ second 0)
    (hsecondSucc : ∀ i < n,
      mu[fun omega ↦ doobCenteredDifference filtration mu
          (finiteProcessSupremum s hs X) (i + 1) omega ^ 2 |
        filtration i] ≤ᵐ[mu] fun _ ↦ second (i + 1))
    (hmoment0 : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (doobCenteredDifference filtration mu
        (finiteProcessSupremum s hs X) 0 omega) 0) ^ k ∂mu) ≤
        moment 0 k)
    (hmomentSucc : ∀ i < n, ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega ↦ (max (doobCenteredDifference filtration mu
          (finiteProcessSupremum s hs X) (i + 1) omega) 0) ^ k |
        filtration i] ≤ᵐ[mu] fun _ ↦ moment (i + 1) k)
    {y alpha t : ℝ} (hy : 0 < y)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) (ht : 0 < t) :
    conditionalValueAtRisk alpha
        (fun omega ↦ finiteProcessSupremum s hs X omega -
          ∫ z, finiteProcessSupremum s hs X z ∂mu) mu ≤
      (strongMomentSeriesExponent q t y
          (∑ i ∈ Finset.range (n + 1), second i)
          (fun k ↦ ∑ i ∈ Finset.range (n + 1), moment i k) -
        Real.log alpha) / t +
      alpha⁻¹ *
        ((∑ i ∈ Finset.range (n + 1), moment i q) /
          ((q : ℝ) * y ^ (q - 1))) := by
  let F : Omega → ℝ := finiteProcessSupremum s hs X
  let D : ℕ → Omega → ℝ :=
    doobCenteredDifference filtration mu F
  have hFint : Integrable F mu :=
    integrable_finiteProcessSupremum s hs X A hA hX hdom
  have hDint : ∀ i < n + 1, Integrable (D i) mu := by
    intro i _hi
    cases i with
    | zero =>
        change Integrable
          (fun omega ↦ mu[F | filtration 0] omega - ∫ z, F z ∂mu) mu
        exact integrable_condExp.sub (integrable_const _)
    | succ i =>
        change Integrable
          (fun omega ↦ mu[F | filtration (i + 1)] omega -
            mu[F | filtration i] omega) mu
        exact integrable_condExp.sub integrable_condExp
  have hDAdapted : StronglyAdapted filtration D :=
    stronglyAdapted_doobCenteredDifference filtration mu F
  have hDsq' : ∀ i < n + 1,
      Integrable (fun omega ↦ D i omega ^ 2) mu := by
    intro i hi
    simpa only [D, F] using hDsq i hi
  have hpow' : ∀ i < n + 1, ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega ↦ (max (D i omega) 0) ^ k) mu := by
    intro i hi k hk
    simpa only [D, F] using hpow i hi k hk
  have hcenter0 : ∫ omega, D 0 omega ∂mu = 0 :=
    integral_doobCenteredDifference_zero filtration F
  have hcenterSucc : ∀ i < n + 1 - 1,
      mu[D (i + 1) | filtration i] =ᵐ[mu] 0 := by
    intro i _hi
    exact condExp_doobCenteredDifference_succ_ae_eq_zero filtration F i
  have hsecond0' : (∫ omega, D 0 omega ^ 2 ∂mu) ≤ second 0 := by
    simpa only [D, F] using hsecond0
  have hsecondSucc' : ∀ i < n + 1 - 1,
      mu[fun omega ↦ D (i + 1) omega ^ 2 | filtration i] ≤ᵐ[mu]
        fun _ ↦ second (i + 1) := by
    intro i hi
    simpa only [D, F] using hsecondSucc i (by omega)
  have hmoment0' : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (D 0 omega) 0) ^ k ∂mu) ≤ moment 0 k := by
    intro k hk
    simpa only [D, F] using hmoment0 k hk
  have hmomentSucc' : ∀ i < n + 1 - 1, ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega ↦ (max (D (i + 1) omega) 0) ^ k |
        filtration i] ≤ᵐ[mu] fun _ ↦ moment (i + 1) k := by
    intro i hi k hk
    simpa only [D, F] using hmomentSucc i (by omega) k hk
  have hsum :=
    conditionalValueAtRisk_sum_le_strongMomentSeriesExponent_add_residual
      filtration D hDAdapted second moment (n + 1) q (by omega) hq hy
        hDint hDsq' hpow' hcenter0 hcenterSucc hsecond0'
        hsecondSucc' hmoment0' hmomentSucc' halpha0 halpha1 ht
  have hsumEq : (fun omega ↦ ∑ i ∈ Finset.range (n + 1), D i omega)
      =ᵐ[mu] fun omega ↦ F omega - ∫ z, F z ∂mu := by
    filter_upwards [hterminal] with omega hterminalOmega
    rw [sum_doobCenteredDifference filtration mu F n omega]
    exact sub_left_inj.mpr hterminalOmega
  have hcenteredInt : Integrable
      (fun omega ↦ F omega - ∫ z, F z ∂mu) mu :=
    hFint.sub (integrable_const _)
  have hsumInt : Integrable
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1), D i omega) mu :=
    hcenteredInt.congr hsumEq.symm
  have hcvarEq := conditionalValueAtRisk_congr_ae
    hsumInt hcenteredInt halpha0 halpha1 hsumEq
  rw [← hcvarEq]
  simpa only [F] using hsum

end ProbabilityTheory
