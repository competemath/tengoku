/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.BoundedSupportChaining
import Tengoku.Randomsettheory.RandomSetTheory.CenteredProcessEnvelope
import Tengoku.Randomsettheory.RandomSetTheory.MixedSupportChaining
import Tengoku.Randomsettheory.RandomSetTheory.MomentConcentration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gaussian--polynomial chaining on a Euclidean ball

This file gives a uniform heavy-tail interface which is deliberately stronger
than a direction-by-direction union bound.  A process `Z` is compared
pathwise with a continuous light-tailed process `G`; the difference is
controlled simultaneously in every direction by one scalar envelope `A`.
The light process is handled by countable Euclidean chaining, whereas the
single exceptional-envelope event is handled by the order-`q` Markov bound.
Consequently the polynomial term pays no covering-number factor.

The main confidence bound has the expected form

`Gaussian(d,x) + C_q K_q delta^(-1/q) n^(-1+1/q)`.

There is an important correction to the statement labelled
`lem:poly_support_chaining` (and hence `prop:poly_K`) in the report.  The
coefficient supplied by Marchina's maximal Fuk--Nagaev theorem is

`C_q = 3 * (2 + max (4/3) (q/3))`,

so it depends explicitly (and linearly for large `q`) on the moment order.
It cannot be advertised as a universal constant independent of `q` when that
theorem is the cited input.  We keep this dependence visible below.

This module proves the composition from a uniform remainder envelope; it does
not claim that the scalar truncation lemmas alone imply Marchina's maximal
empirical-process theorem.  Establishing such a decomposition/certificate for
a concrete empirical process remains an explicit hypothesis in the theorem.
-/

open Filter Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology
open RandomSetTheory

noncomputable section

namespace ProbabilityTheory

/-- The `mu_q` factor in Marchina's maximal Fuk--Nagaev inequality, for a
natural moment order `q`.-/
def fukNagaevMu (q : ℕ) : ℝ :=
  2 + max (4 / 3 : ℝ) ((q : ℝ) / 3)

/-- Explicit polynomial coefficient furnished by the maximal Fuk--Nagaev
inequality used in the report.  In particular, this is not uniform in `q`.-/
def fukNagaevConstant (q : ℕ) : ℝ :=
  3 * fukNagaevMu q

/-- An equivalent form which makes the linear dependence on `q` manifest.
@isnad1 id=eq.0h1v.s5.946b2eaf3a6e from=translated src=- shape=d6b177b6 vocab=285fafa4
-/
theorem fukNagaevConstant_eq_six_add_max (q : ℕ) :
    fukNagaevConstant q = 6 + max 4 (q : ℝ) := by
  unfold fukNagaevConstant fukNagaevMu
  rw [mul_add]
  norm_num
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1 <;> ring

/--
@isnad1 id=le.0h1v.s3.094c31625c23 from=translated src=- shape=b9369acb vocab=2ab9303c
-/
theorem one_le_fukNagaevConstant (q : ℕ) :
    1 ≤ fukNagaevConstant q := by
  unfold fukNagaevConstant fukNagaevMu
  have hmax : 0 ≤ max (4 / 3 : ℝ) ((q : ℝ) / 3) := by
    exact (by norm_num : (0 : ℝ) ≤ 4 / 3) |>.trans (le_max_left _ _)
  nlinarith

/--
@isnad1 id=le.0h1v.s3.d4eb45730459 from=translated src=- shape=b9369acb vocab=2ab9303c
-/
theorem fukNagaevConstant_nonneg (q : ℕ) :
    0 ≤ fukNagaevConstant q :=
  (zero_le_one.trans (one_le_fukNagaevConstant q))

/-- Marchina's coefficient dominates the moment order itself.  This makes
precise why the cited theorem cannot furnish a numerical constant uniform in
`q`.
@isnad1 id=le.0h1v.s3.7287b61c9612 from=translated src=- shape=1ed09587 vocab=eaeaf238
-/
theorem natCast_le_fukNagaevConstant (q : ℕ) :
    (q : ℝ) ≤ fukNagaevConstant q := by
  rw [fukNagaevConstant_eq_six_add_max]
  exact (le_max_right 4 (q : ℝ)).trans (by linarith)

/-- There is no finite real number which bounds all the coefficients
`fukNagaevConstant q`.  Thus a conclusion advertised with a constant
independent of `q` is not a consequence of Marchina's Theorem 2.1 with
`p = q`.
@isnad1 id=not.0h0v.s3.f784e5071343 from=translated src=- shape=e7309eea vocab=2ab9303c
-/
theorem not_exists_forall_fukNagaevConstant_le :
    ¬ ∃ C : ℝ, ∀ q : ℕ, fukNagaevConstant q ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨q, hq⟩ := exists_nat_gt C
  have hqC := (natCast_le_fukNagaevConstant q).trans (hC q)
  exact (not_lt_of_ge hqC) hq

/-- The closed-form threshold delivered by mixed Euclidean chaining.-/
def mixedEuclideanProcessBound (sigma2 sigma1 : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  6 * sigma2 * Real.sqrt (2 * x) +
    72 * sigma2 * Real.sqrt (d + 1 : ℝ) +
    12 * sigma1 * x + 144 * sigma1 * (d + 1 : ℝ)

/--
@isnad1 id=le.3h4v.s5.ef9cb3efd15e from=translated src=- shape=0d47e803 vocab=53f1bb43
-/
theorem mixedEuclideanProcessBound_nonneg
    {sigma2 sigma1 x : ℝ} (hsigma2 : 0 ≤ sigma2)
    (hsigma1 : 0 ≤ sigma1) (d : ℕ) (hx : 0 ≤ x) :
    0 ≤ mixedEuclideanProcessBound sigma2 sigma1 d x := by
  unfold mixedEuclideanProcessBound
  positivity

/-- Fully geometric mixed-tail chaining on the Euclidean unit ball.  The
dyadic nets, projections, and local edge graphs are constructed internally.
This is the mixed Bernstein analogue of
`measureReal_unitBall_subgaussianProcess_largeDeviation_le`.
@isnad1 id=le.6h7v.s8.71bdba0d3604 from=translated src=- shape=f8be0369 vocab=6139a945
-/
theorem measureReal_unitBall_mixedProcess_largeDeviation_le
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (Z : Omega → EuclideanUnitBall E → ℝ)
    {sigma2 sigma1 x : ℝ}
    (hsigma2 : 0 ≤ sigma2) (hsigma1 : 0 ≤ sigma1) (hx : 0 ≤ x)
    (hcontinuous : ∀ omega, Continuous (Z omega))
    (hzero : ∀ omega, Z omega ⟨0, by simp⟩ = 0)
    (hmixed : ∀ (s t : EuclideanUnitBall E) (y : ℝ), 0 ≤ y →
      mu.real {omega |
        sigma2 * dist s t * Real.sqrt (2 * y) +
            2 * sigma1 * dist s t * y <
          |Z omega s - Z omega t|} ≤
        2 * Real.exp (-y)) :
    mu.real {omega | ∃ t : EuclideanUnitBall E,
        mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x <
          |Z omega t|} ≤
      Real.exp (-x) := by
  obtain ⟨N, proj, hNzero, hNcard, hprojMem, _hprojNear, hedge,
      hprojDist⟩ := RandomSetTheory.exists_unitBall_dyadic_chainingData (E := E)
  let edges : ℕ → Finset (EuclideanUnitBall E × EuclideanUnitBall E) :=
    RandomSetTheory.unitBallLocalDyadicEdges N
  have hbase : ∀ t, proj 0 t ∈ N 0 := hprojMem 0
  have hbaseZero : ∀ omega, ∀ u ∈ N 0, Z omega u = 0 := by
    intro omega u hu
    have huval : (u : E) = 0 := hNzero u hu
    have hu0 : u = (⟨0, by simp⟩ : EuclideanUnitBall E) := by
      apply Subtype.ext
      exact huval
    rw [hu0]
    exact hzero omega
  have hedgeDist : ∀ k, ∀ e ∈ edges k,
      dist e.1 e.2 ≤ 3 * ((1 / 2 : ℝ) ^ k) := by
    intro k e he
    simpa only [edges, RandomSetTheory.dyadicResolution] using
      RandomSetTheory.dist_le_three_mul_dyadicResolution_of_mem_localEdges N he
  have hedgeCard : ∀ k, ((edges k).card : ℝ) ≤
      Real.exp (4 * (finrank ℝ E : ℝ) * (k + 2 : ℝ)) := by
    intro k
    exact RandomSetTheory.card_unitBallLocalDyadicEdges_real_le_exp N
      (finrank ℝ E) hNcard k
  have hproj : ∀ t, Tendsto (fun k ↦ proj k t) atTop (nhds t) := by
    intro t
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [dist_comm] using hprojDist t
  simpa only [mixedEuclideanProcessBound] using
    (measureReal_mixedEuclideanContinuousProcess_largeDeviation_le
      Z (N 0) edges proj (finrank ℝ E) hsigma2 hsigma1 hx hcontinuous
      hbase (by simpa only [edges] using hedge) hproj hbaseZero hedgeDist
      hedgeCard hmixed)

section PolynomialPerturbation

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- A uniform perturbation of a mixed-tail Euclidean process has a genuine
Gaussian-plus-polynomial tail.  The polynomial contribution comes from one
scalar envelope event, so its probability is not multiplied by the number of
net points or edges.

The factor `fukNagaevConstant q` is retained explicitly to match the
q-dependent coefficient in the maximal inequality cited by the report.
@isnad1 id=le.10h12v.s9.0a98a242e325 from=translated src=- shape=57933837 vocab=00cece1c
-/
theorem measureReal_unitBall_mixedPolynomialProcess_largeDeviation_le
    (Z G : Omega → EuclideanUnitBall E → ℝ) (A : Omega → ℝ)
    {q : ℕ} {sigma2 sigma1 rho x y : ℝ}
    (hsigma2 : 0 ≤ sigma2) (hsigma1 : 0 ≤ sigma1)
    (hrho : 0 ≤ rho) (hx : 0 ≤ x) (hy : 0 < y)
    (hGcontinuous : ∀ omega, Continuous (G omega))
    (hGzero : ∀ omega, G omega ⟨0, by simp⟩ = 0)
    (hGmixed : ∀ (s t : EuclideanUnitBall E) (z : ℝ), 0 ≤ z →
      mu.real {omega |
        sigma2 * dist s t * Real.sqrt (2 * z) +
            2 * sigma1 * dist s t * z <
          |G omega s - G omega t|} ≤
        2 * Real.exp (-z))
    (hAq : Integrable (fun omega ↦ |A omega| ^ q) mu)
    (hdom : ∀ omega t, |Z omega t - G omega t| ≤ rho * |A omega|) :
    mu.real {omega | ∃ t : EuclideanUnitBall E,
        mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
            fukNagaevConstant q * rho * y < |Z omega t|} ≤
      Real.exp (-x) + absoluteMoment A q mu / y ^ q := by
  let lightBad : Set Omega := {omega | ∃ t : EuclideanUnitBall E,
    mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x <
      |G omega t|}
  let heavyBad : Set Omega := {omega | y ≤ |A omega|}
  have hsubset :
      {omega | ∃ t : EuclideanUnitBall E,
          mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
              fukNagaevConstant q * rho * y < |Z omega t|} ⊆
        lightBad ∪ heavyBad := by
    intro omega homega
    obtain ⟨t, ht⟩ := homega
    by_cases hlight : omega ∈ lightBad
    · exact Or.inl hlight
    by_cases hheavy : omega ∈ heavyBad
    · exact Or.inr hheavy
    exfalso
    have hG : |G omega t| ≤
        mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x := by
      by_contra hnot
      apply hlight
      exact ⟨t, lt_of_not_ge hnot⟩
    have hA : |A omega| < y := by
      exact lt_of_not_ge hheavy
    have hrhoA : rho * |A omega| ≤ rho * y :=
      (mul_le_mul_of_nonneg_left hA.le hrho)
    have hC : rho * y ≤ fukNagaevConstant q * rho * y := by
      have hry : 0 ≤ rho * y := mul_nonneg hrho hy.le
      nlinarith [one_le_fukNagaevConstant q]
    have htriangle : |Z omega t| ≤
        |G omega t| + |Z omega t - G omega t| := by
      calc
        |Z omega t| = |G omega t + (Z omega t - G omega t)| := by ring_nf
        _ ≤ |G omega t| + |Z omega t - G omega t| := abs_add_le _ _
    have hupper : |Z omega t| ≤
        mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
          fukNagaevConstant q * rho * y := by
      calc
        |Z omega t| ≤ |G omega t| + |Z omega t - G omega t| := htriangle
        _ ≤ mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
            rho * |A omega| := add_le_add hG (hdom omega t)
        _ ≤ mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
            rho * y := add_le_add le_rfl hrhoA
        _ ≤ mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
            fukNagaevConstant q * rho * y := add_le_add le_rfl hC
    exact (not_lt_of_ge hupper) ht
  have hlight : mu.real lightBad ≤ Real.exp (-x) := by
    simpa only [lightBad] using
      measureReal_unitBall_mixedProcess_largeDeviation_le G hsigma2 hsigma1 hx
        hGcontinuous hGzero hGmixed
  have hheavy : mu.real heavyBad ≤ absoluteMoment A q mu / y ^ q := by
    simpa only [heavyBad] using
      measureReal_abs_ge_le_absoluteMoment_div A q hAq hy
  calc
    mu.real {omega | ∃ t : EuclideanUnitBall E,
        mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
            fukNagaevConstant q * rho * y < |Z omega t|} ≤
        mu.real (lightBad ∪ heavyBad) := measureReal_mono hsubset
    _ ≤ mu.real lightBad + mu.real heavyBad := measureReal_union_le _ _
    _ ≤ Real.exp (-x) + absoluteMoment A q mu / y ^ q :=
      add_le_add hlight hheavy

/-- Confidence form of the preceding Gaussian--polynomial bound.  If
`E|A|^q ≤ K_q^q`, the single envelope event contributes at most `delta` at
threshold `K_q delta^(-1/q)`.
@isnad1 id=le.13h13v.s9.fb780bf52427 from=translated src=- shape=f1b66fca vocab=ac98239d
-/
theorem measureReal_unitBall_mixedPolynomialProcess_confidence_le
    (Z G : Omega → EuclideanUnitBall E → ℝ) (A : Omega → ℝ)
    {q : ℕ} (hq : 0 < q)
    {sigma2 sigma1 rho x Kq delta : ℝ}
    (hsigma2 : 0 ≤ sigma2) (hsigma1 : 0 ≤ sigma1)
    (hrho : 0 ≤ rho) (hx : 0 ≤ x)
    (hKq : 0 < Kq) (hdelta : 0 < delta)
    (hGcontinuous : ∀ omega, Continuous (G omega))
    (hGzero : ∀ omega, G omega ⟨0, by simp⟩ = 0)
    (hGmixed : ∀ (s t : EuclideanUnitBall E) (z : ℝ), 0 ≤ z →
      mu.real {omega |
        sigma2 * dist s t * Real.sqrt (2 * z) +
            2 * sigma1 * dist s t * z <
          |G omega s - G omega t|} ≤
        2 * Real.exp (-z))
    (hAq : Integrable (fun omega ↦ |A omega| ^ q) mu)
    (hAmoment : absoluteMoment A q mu ≤ Kq ^ q)
    (hdom : ∀ omega t, |Z omega t - G omega t| ≤ rho * |A omega|) :
    mu.real {omega | ∃ t : EuclideanUnitBall E,
        mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
            fukNagaevConstant q * rho *
              (Kq * (1 / delta) ^ (1 / (q : ℝ))) <
          |Z omega t|} ≤
      Real.exp (-x) + delta := by
  let r : ℝ := 1 / delta
  let y : ℝ := Kq * r ^ (1 / (q : ℝ))
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : 0 < r := one_div_pos.mpr hdelta
  have hy : 0 < y := mul_pos hKq (Real.rpow_pos_of_pos hr _)
  have hrootPow : (r ^ (1 / (q : ℝ))) ^ q = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    rw [one_div, inv_mul_cancel₀ hqreal.ne', Real.rpow_one]
  have hyPow : y ^ q = Kq ^ q * r := by
    simp only [y, mul_pow, hrootPow]
  have hpoly : absoluteMoment A q mu / y ^ q ≤ delta := by
    calc
      absoluteMoment A q mu / y ^ q ≤ Kq ^ q / y ^ q := by
        exact div_le_div_of_nonneg_right hAmoment (pow_nonneg hy.le q)
      _ = delta := by
        rw [hyPow]
        have hKpow : Kq ^ q ≠ 0 := pow_ne_zero q hKq.ne'
        dsimp only [r]
        field_simp
  have hbase := measureReal_unitBall_mixedPolynomialProcess_largeDeviation_le
    Z G A hsigma2 hsigma1 hrho hx hy hGcontinuous hGzero hGmixed hAq hdom
  simpa only [y, r] using hbase.trans (add_le_add le_rfl hpoly)

/-- Empirical-rate specialization.  The scale of the uniform heavy remainder
is `n^(-1+1/q)`, making the polynomial term in the conclusion explicit.
@isnad1 id=le.13h13v.s9.248cb8d2e812 from=translated src=- shape=4de418b9 vocab=ac98239d
-/
theorem measureReal_unitBall_mixedPolynomialEmpiricalProcess_confidence_le
    (Z G : Omega → EuclideanUnitBall E → ℝ) (A : Omega → ℝ)
    {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    {sigma2 sigma1 x Kq delta : ℝ}
    (hsigma2 : 0 ≤ sigma2) (hsigma1 : 0 ≤ sigma1) (hx : 0 ≤ x)
    (hKq : 0 < Kq) (hdelta : 0 < delta)
    (hGcontinuous : ∀ omega, Continuous (G omega))
    (hGzero : ∀ omega, G omega ⟨0, by simp⟩ = 0)
    (hGmixed : ∀ (s t : EuclideanUnitBall E) (z : ℝ), 0 ≤ z →
      mu.real {omega |
        sigma2 * dist s t * Real.sqrt (2 * z) +
            2 * sigma1 * dist s t * z <
          |G omega s - G omega t|} ≤
        2 * Real.exp (-z))
    (hAq : Integrable (fun omega ↦ |A omega| ^ q) mu)
    (hAmoment : absoluteMoment A q mu ≤ Kq ^ q)
    (hdom : ∀ omega t,
      |Z omega t - G omega t| ≤
        (n : ℝ) ^ (-1 + 1 / (q : ℝ)) * |A omega|) :
    mu.real {omega | ∃ t : EuclideanUnitBall E,
        mixedEuclideanProcessBound sigma2 sigma1 (finrank ℝ E) x +
            fukNagaevConstant q * Kq *
              (1 / delta) ^ (1 / (q : ℝ)) *
              (n : ℝ) ^ (-1 + 1 / (q : ℝ)) <
          |Z omega t|} ≤
      Real.exp (-x) + delta := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hrho : 0 ≤ (n : ℝ) ^ (-1 + 1 / (q : ℝ)) :=
    (Real.rpow_pos_of_pos hnreal _).le
  have h := measureReal_unitBall_mixedPolynomialProcess_confidence_le
    Z G A hq hsigma2 hsigma1 hrho hx hKq hdelta hGcontinuous hGzero
      hGmixed hAq hAmoment hdom
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- Sub-Gaussian specialization of the empirical bound.  This is the direct
Euclidean-ball interface with rate

`K_2 (sqrt x + sqrt (d+1)) / sqrt n
  + C_q K_q delta^(-1/q) n^(-1+1/q)`.

All constants are displayed in the formal statement, and the exceptional
polynomial event is paid only once.
@isnad1 id=le.12h12v.s9.f13b5ac62b5f from=translated src=- shape=5b0fcde5 vocab=f658902a
-/
theorem measureReal_unitBall_subgaussianPolynomialEmpiricalProcess_confidence_le
    (Z G : Omega → EuclideanUnitBall E → ℝ) (A : Omega → ℝ)
    {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    {K2 Kq x delta : ℝ} (hK2 : 0 ≤ K2) (hx : 0 ≤ x)
    (hKq : 0 < Kq) (hdelta : 0 < delta)
    (hGcontinuous : ∀ omega, Continuous (G omega))
    (hGzero : ∀ omega, G omega ⟨0, by simp⟩ = 0)
    (hGsubgaussian : ∀ (s t : EuclideanUnitBall E) (z : ℝ), 0 ≤ z →
      mu.real {omega |
        (K2 / Real.sqrt n) * dist s t * Real.sqrt (2 * z) <
          |G omega s - G omega t|} ≤
        2 * Real.exp (-z))
    (hAq : Integrable (fun omega ↦ |A omega| ^ q) mu)
    (hAmoment : absoluteMoment A q mu ≤ Kq ^ q)
    (hdom : ∀ omega t,
      |Z omega t - G omega t| ≤
        (n : ℝ) ^ (-1 + 1 / (q : ℝ)) * |A omega|) :
    mu.real {omega | ∃ t : EuclideanUnitBall E,
        6 * (K2 / Real.sqrt n) * Real.sqrt (2 * x) +
            72 * (K2 / Real.sqrt n) *
              Real.sqrt (finrank ℝ E + 1 : ℝ) +
            fukNagaevConstant q * Kq *
              (1 / delta) ^ (1 / (q : ℝ)) *
              (n : ℝ) ^ (-1 + 1 / (q : ℝ)) <
          |Z omega t|} ≤
      Real.exp (-x) + delta := by
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsigma : 0 ≤ K2 / Real.sqrt n := div_nonneg hK2 hsqrt
  have h := measureReal_unitBall_mixedPolynomialEmpiricalProcess_confidence_le
    Z G A hn hq hsigma (show (0 : ℝ) ≤ 0 by norm_num) hx hKq hdelta
      hGcontinuous hGzero (by
        intro s t z hz
        simpa using hGsubgaussian s t z hz) hAq hAmoment hdom
  simpa only [mixedEuclideanProcessBound, mul_zero, zero_mul, add_zero] using h

end PolynomialPerturbation

end ProbabilityTheory
