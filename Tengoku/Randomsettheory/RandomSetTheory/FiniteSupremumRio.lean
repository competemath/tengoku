/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumStrongMoment
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentRioMartingale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An explicit Rio endpoint for a finite process supremum

This file combines the canonical Doob expansion of a finite supremum with the
fully optimized strong-moment martingale theorem.  All martingale structure is
constructed internally.  The only remaining probabilistic interface consists
of deterministic conditional-moment proxies for the Doob differences and
their aggregate Hölder interpolation bounds.

Together with `FiniteSupremumStrongMomentEfronStein`, this isolates the last
product-space step: identify each concrete Doob increment with the appropriate
centred ghost fibre.  No passage to an infinite or continuous index class is
claimed here.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T : Type*} {mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

variable (filtration : Filtration ℕ mOmega)

/-- Optimized strong-moment CVaR bound for a finite process supremum around
its expectation.  The finite class cardinality does not occur in the bound.
@isnad1 id=le.21h16v.s10.561a997fb71e from=translated src=- shape=3d3e0a8c vocab=04881728
-/
theorem conditionalValueAtRisk_finiteProcessSupremum_sub_integral_le_rioStrongMoment
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu filtration]
    (s : Finset T) (hs : s.Nonempty) (X : T → Omega → ℝ)
    (A : Omega → ℝ) (hA : Integrable A mu)
    (hX : ∀ u ∈ s, Measurable (X u))
    (hdom : ∀ omega u, u ∈ s → |X u omega| ≤ |A omega|)
    (second : ℕ → ℝ) (moment : ℕ → ℕ → ℝ)
    (n q : ℕ) (hq : 3 ≤ q)
    {V Q y alpha : ℝ} (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y)
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
    (hsecond : (∑ i ∈ Finset.range (n + 1), second i) ≤ V)
    (hmiddle : ∀ k ∈ Finset.Ico 3 q,
      (∑ i ∈ Finset.range (n + 1), moment i k) ≤
        interpolatedStrongMomentCoefficient q V Q k)
    (hmomentQ : (∑ i ∈ Finset.range (n + 1), moment i q) ≤ Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hscale : Q * Real.exp (-Real.log alpha) ≤ y ^ q) :
    conditionalValueAtRisk alpha
        (fun omega ↦ finiteProcessSupremum s hs X omega -
          ∫ z, finiteProcessSupremum s hs X z ∂mu) mu ≤
      Real.sqrt (2 * V * (-Real.log alpha)) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
        alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) := by
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
  have hsum := conditionalValueAtRisk_sum_le_rioStrongMoment_explicit
    filtration D hDAdapted second moment (n + 1) q (by omega) hq
      hV hQ hy hDint hDsq' hpow' hcenter0 hcenterSucc hsecond0'
      hsecondSucc' hmoment0' hmomentSucc' hsecond hmiddle hmomentQ
      halpha0 halpha1 hscale
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
    hsumInt hcenteredInt halpha0 halpha1.le hsumEq
  rw [← hcvarEq]
  simpa only [F] using hsum

end ProbabilityTheory
