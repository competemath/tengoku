/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.MartingaleVarianceBernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bernstein concentration for finite process suprema

This file combines the finite-supremum and Doob-difference infrastructure of
`MartingaleTruncation` with the variance-sensitive martingale inequality from
`MartingaleVarianceBernstein`.

For a finite nonempty class, measurability and integrability of the supremum
are derived from a common envelope.  Its Doob differences are automatically
adapted, conditionally centred and bounded by twice a deterministic bound on
the supremum.  Consequently, the only variance-sensitive hypotheses left in
the main theorem are deterministic bounds on the initial and conditional
second moments of those Doob differences.

The missing Efron--Stein bridge is deliberately explicit.  On a product space
of independent observations one normally bounds these conditional second
moments by introducing a ghost replacement of coordinate `k`, using
`abs_finset_sup'_sum_replace_one_le_add_envelopes`, and integrating out the
ghost coordinate.  Mathlib currently has no Efron--Stein/tensorisation API,
and the present project does not yet expose the required product-coordinate
replacement kernel.  The theorem below therefore stops exactly at the
conditional-second-moment interface rather than assuming a concentration
certificate for the supremum itself.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T : Type*} {mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

variable (filtration : Filtration ℕ mOmega)

/-- A uniformly bounded terminal variable has Doob differences bounded by
twice the terminal bound.  This includes the initial centred difference.-/
theorem ae_abs_doobCenteredDifference_le_two_mul
    [IsProbabilityMeasure mu]
    (F : Omega → ℝ) {B : ℝ}
    (hFbound : ∀ᵐ omega ∂mu, |F omega| ≤ B) (k : ℕ) :
    ∀ᵐ omega ∂mu,
      |doobCenteredDifference filtration mu F k omega| ≤ 2 * B := by
  have hFboundNorm : ∀ᵐ omega ∂mu, ‖F omega‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using hFbound
  have hmean : |∫ omega, F omega ∂mu| ≤ B := by
    have h := norm_integral_le_of_norm_le_const hFboundNorm
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  cases k with
  | zero =>
      have hcond : ∀ᵐ omega ∂mu, ‖mu[F | filtration 0] omega‖ ≤ B :=
        ae_bdd_norm_condExp_of_ae_bdd_norm hFboundNorm
      filter_upwards [hcond] with omega hcondOmega
      change |mu[F | filtration 0] omega - ∫ z, F z ∂mu| ≤ 2 * B
      calc
        |mu[F | filtration 0] omega - ∫ z, F z ∂mu| ≤
            |mu[F | filtration 0] omega| + |∫ z, F z ∂mu| := abs_sub _ _
        _ ≤ B + B := by
          exact add_le_add (by simpa only [Real.norm_eq_abs] using hcondOmega) hmean
        _ = 2 * B := by ring
  | succ k =>
      have hcondNext : ∀ᵐ omega ∂mu,
          ‖mu[F | filtration (k + 1)] omega‖ ≤ B :=
        ae_bdd_norm_condExp_of_ae_bdd_norm hFboundNorm
      have hcondPrev : ∀ᵐ omega ∂mu,
          ‖mu[F | filtration k] omega‖ ≤ B :=
        ae_bdd_norm_condExp_of_ae_bdd_norm hFboundNorm
      filter_upwards [hcondNext, hcondPrev]
        with omega hnextOmega hprevOmega
      change |mu[F | filtration (k + 1)] omega -
        mu[F | filtration k] omega| ≤ 2 * B
      calc
        |mu[F | filtration (k + 1)] omega -
            mu[F | filtration k] omega| ≤
            |mu[F | filtration (k + 1)] omega| +
              |mu[F | filtration k] omega| := abs_sub _ _
        _ ≤ B + B := by
          exact add_le_add
            (by simpa only [Real.norm_eq_abs] using hnextOmega)
            (by simpa only [Real.norm_eq_abs] using hprevOmega)
        _ = 2 * B := by ring

/-- The preceding deterministic bound gives every finite Doob difference all
finite moments, in particular `L²`.-/
theorem memLp_doobCenteredDifference_two_of_ae_abs_le
    [IsProbabilityMeasure mu]
    (F : Omega → ℝ) {B : ℝ}
    (hFbound : ∀ᵐ omega ∂mu, |F omega| ≤ B) (k : ℕ) :
    MemLp (doobCenteredDifference filtration mu F k) 2 mu := by
  apply MemLp.of_bound
    (((stronglyAdapted_doobCenteredDifference filtration mu F k).mono
      (filtration.le k)).aestronglyMeasurable) (2 * B)
  simpa only [Real.norm_eq_abs] using
    ae_abs_doobCenteredDifference_le_two_mul filtration F hFbound k

end ProbabilityTheory
