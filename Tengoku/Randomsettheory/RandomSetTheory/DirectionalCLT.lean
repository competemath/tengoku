/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.DirectionalConcentration
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableSupport
import Tengoku.Seed.Probability.CentralLimitTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A central limit theorem in a fixed support direction

This file is a deliberately one-dimensional bridge between random-set
averages and Mathlib's scalar central limit theorem.  For a fixed direction
`u`, the support error of a Minkowski average is exactly the average of the
scalar random variables `directionalSupportDeviation S L u i`.

Consequently, an iid `L²` hypothesis on these scalar variables gives a CLT
for the support function in that direction.  This is a directional CLT only:
it does not assert convergence in a function space, uniformly over
directions, or in Hausdorff distance.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators InnerProductSpace ProbabilityTheory Topology

noncomputable section

namespace RandomSetTheory

/-- Subtracting the deterministic target support does not change the
variance in a fixed direction.  This identifies the variance appearing in
the directional Gaussian limit with the variance of the raw support
function.
@isnad1 id=eq.1h6v.s6.e75b4142192f from=translated src=- shape=31b9ae90 vocab=686dc252
-/
theorem variance_directionalSupportDeviation_eq_supportFunction
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (S : ℕ → Omega → Set E) (L : Set E) (u : E)
    (hmeas : AEStronglyMeasurable
      (fun omega => supportFunction (S 0 omega) u) mu) :
    Var[directionalSupportDeviation S L u 0; mu] =
      Var[fun omega => supportFunction (S 0 omega) u; mu] := by
  change Var[fun omega =>
    supportFunction (S 0 omega) u - supportFunction L u; mu] = _
  exact variance_sub_const hmeas (supportFunction L u)

/-- Centering two support directions by deterministic target supports does
not change their covariance.  The right-hand side is the covariance kernel
that would govern finite-dimensional Gaussian limits across directions.
@isnad1 id=eq.2h7v.s7.84e702483f2b from=translated src=- shape=252cdbfd vocab=a24db2f3
-/
theorem covariance_directionalSupportDeviation_eq_supportFunction
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (S : ℕ → Omega → Set E) (L : Set E) (u v : E)
    (hu : Integrable (fun omega => supportFunction (S 0 omega) u) mu)
    (hv : Integrable (fun omega => supportFunction (S 0 omega) v) mu) :
    cov[directionalSupportDeviation S L u 0,
        directionalSupportDeviation S L v 0; mu] =
      cov[fun omega => supportFunction (S 0 omega) u,
        fun omega => supportFunction (S 0 omega) v; mu] := by
  change cov[fun omega =>
      supportFunction (S 0 omega) u - supportFunction L u,
    fun omega => supportFunction (S 0 omega) v - supportFunction L v; mu] = _
  rw [covariance_sub_const_left hu, covariance_sub_const_right hv]

/-- Scalar CLT for the sum of centered directional support deviations.

This is the raw probabilistic statement underlying the random-set version
below.  The limiting variance is the variance of the support deviation in
the fixed direction `u`; Mathlib's Gaussian convention also covers the
degenerate zero-variance case.
@isnad1 id=tendstoi.5h9v.s8.b1806d3e28eb from=translated src=- shape=8127ac94 vocab=b35c6b54
-/
theorem tendstoInDistribution_directionalSupportDeviation_sum
    {Omega Omega' E : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (S : ℕ → Omega → Set E) (L : Set E) (u : E) (Y : Omega' → ℝ)
    (hY : HasLaw Y
      (gaussianReal 0
        Var[directionalSupportDeviation S L u 0; mu].toNNReal) mu')
    (hL2 : MemLp (directionalSupportDeviation S L u 0) 2 mu)
    (hindep : iIndepFun (directionalSupportDeviation S L u) mu)
    (hident : ∀ i, IdentDistrib
      (directionalSupportDeviation S L u i)
      (directionalSupportDeviation S L u 0) mu mu)
    (hcenter : mu[directionalSupportDeviation S L u 0] = 0) :
    TendstoInDistribution
      (fun (n : ℕ) omega => (√n)⁻¹ *
        ∑ i ∈ Finset.range n, directionalSupportDeviation S L u i omega)
      atTop Y (fun _ => mu) mu' := by
  simpa only [hcenter, Nat.cast_zero, mul_zero, sub_zero] using
    (tendstoInDistribution_inv_sqrt_mul_sum_sub hY hL2 hindep hident)

/-- Scalar CLT for the same sum, indexed by `Finset.range (n + 1)`.

The shift avoids the empty empirical average and division by zero while
leaving the limiting distribution unchanged.
@isnad1 id=tendstoi.5h9v.s8.914769effe5d from=translated src=- shape=a9a28472 vocab=24734004
-/
theorem tendstoInDistribution_directionalSupportDeviation_sum_succ
    {Omega Omega' E : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (S : ℕ → Omega → Set E) (L : Set E) (u : E) (Y : Omega' → ℝ)
    (hY : HasLaw Y
      (gaussianReal 0
        Var[directionalSupportDeviation S L u 0; mu].toNNReal) mu')
    (hL2 : MemLp (directionalSupportDeviation S L u 0) 2 mu)
    (hindep : iIndepFun (directionalSupportDeviation S L u) mu)
    (hident : ∀ i, IdentDistrib
      (directionalSupportDeviation S L u i)
      (directionalSupportDeviation S L u 0) mu mu)
    (hcenter : mu[directionalSupportDeviation S L u 0] = 0) :
    TendstoInDistribution
      (fun (n : ℕ) omega => (√((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ Finset.range (n + 1),
          directionalSupportDeviation S L u i omega)
      atTop Y (fun _ => mu) mu' := by
  let h := tendstoInDistribution_directionalSupportDeviation_sum
    S L u Y hY hL2 hindep hident hcenter
  exact
    { forall_aemeasurable := fun n => h.forall_aemeasurable (n + 1)
      aemeasurable_limit := h.aemeasurable_limit
      tendsto := h.tendsto.comp (tendsto_add_atTop_nat 1) }

/-- **Directional random-set CLT.**

For a fixed direction `u`, the support function of the empirical Minkowski
average, centered at `supportFunction L u` and scaled by `sqrt (n + 1)`,
converges in distribution to the centered Gaussian whose variance is that
of one directional support deviation.

Compactness and nonemptiness are used only to identify the support of the
Minkowski average with the average of the individual support functions.
@isnad1 id=tendstoi.7h9v.s8.8115023f2f08 from=translated src=- shape=fa9bfa2a vocab=ce557053
-/
theorem tendstoInDistribution_sqrt_mul_supportFunction_minkowskiAverage_sub
    {Omega Omega' E : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (S : ℕ → Omega → Set E) (L : Set E) (u : E) (Y : Omega' → ℝ)
    (hScompact : ∀ i omega, IsCompact (S i omega))
    (hSne : ∀ i omega, (S i omega).Nonempty)
    (hY : HasLaw Y
      (gaussianReal 0
        Var[directionalSupportDeviation S L u 0; mu].toNNReal) mu')
    (hL2 : MemLp (directionalSupportDeviation S L u 0) 2 mu)
    (hindep : iIndepFun (directionalSupportDeviation S L u) mu)
    (hident : ∀ i, IdentDistrib
      (directionalSupportDeviation S L u i)
      (directionalSupportDeviation S L u 0) mu mu)
    (hcenter : mu[directionalSupportDeviation S L u 0] = 0) :
    TendstoInDistribution
      (fun (n : ℕ) omega => √((n + 1 : ℕ) : ℝ) *
        (supportFunction
            (minkowskiAverage (Finset.range (n + 1)) (fun i => S i omega)) u -
          supportFunction L u))
      atTop Y (fun _ => mu) mu' := by
  have hclt :=
    tendstoInDistribution_directionalSupportDeviation_sum_succ
      S L u Y hY hL2 hindep hident hcenter
  apply hclt.congr
  · intro n
    filter_upwards [] with omega
    rw [supportFunction_minkowskiAverage_sub_eq_average_deviation
      S L (Finset.range (n + 1)) (by simp)
      (fun i _hi omega' => hScompact i omega')
      (fun i _hi omega' => hSne i omega')]
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hsqrt : √(n + 1 : ℕ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    field_simp
    rw [Finset.card_range, Real.sq_sqrt hn.le]
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Observation-level iid specialization of the directional random-set CLT.

Here the random sets are `F (X i)`.  Effros measurability of `F` supplies the
measurable scalar support map, so independence and identical distribution of
the observations are automatically transported to every fixed support
direction.  The population support identity centers the scalar variables.

The `L²` assumption is stated only for the resulting support deviation; it
also supplies the integrability needed to justify centering.
@isnad1 id=tendstoi.8h11v.s8.c2bb869100b9 from=translated src=- shape=773a3712 vocab=e5311ca2
-/
theorem tendstoInDistribution_iid_supportFunction_minkowskiAverage
    {Omega Omega' Z E : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Omega'] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (X : ℕ → Omega → Z)
    (hindep : iIndepFun X mu)
    (hident : ∀ i, IdentDistrib (X i) (X 0) mu mu)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (L : Set E) (u : E) (Y : Omega' → ℝ)
    (hY : HasLaw Y
      (gaussianReal 0
        Var[directionalSupportDeviation
          (fun i omega => F (X i omega)) L u 0; mu].toNNReal) mu')
    (hL2 : MemLp
      (directionalSupportDeviation
        (fun i omega => F (X i omega)) L u 0) 2 mu)
    (hLsupport : supportFunction L u =
      ∫ omega, supportFunction (F (X 0 omega)) u ∂mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega => √((n + 1 : ℕ) : ℝ) *
        (supportFunction
            (minkowskiAverage (Finset.range (n + 1))
              (fun i => F (X i omega))) u -
          supportFunction L u))
      atTop Y (fun _ => mu) mu' := by
  let S : ℕ → Omega → Set E := fun i omega => F (X i omega)
  have hsupp : Measurable (fun z => supportFunction (F z) u) :=
    measurable_supportFunction hF hFcompact hFne u
  have hdev : Measurable
      (fun z => supportFunction (F z) u - supportFunction L u) :=
    hsupp.sub_const (supportFunction L u)
  have hindepDev : iIndepFun (directionalSupportDeviation S L u) mu := by
    have h := hindep.comp
      (fun _ z => supportFunction (F z) u - supportFunction L u)
      (fun _ => hdev)
    change iIndepFun
      (fun i omega => supportFunction (F (X i omega)) u - supportFunction L u) mu
    simpa only [Function.comp_def] using h
  have hidentDev : ∀ i, IdentDistrib
      (directionalSupportDeviation S L u i)
      (directionalSupportDeviation S L u 0) mu mu := by
    intro i
    change IdentDistrib
      (fun omega => supportFunction (F (X i omega)) u - supportFunction L u)
      (fun omega => supportFunction (F (X 0 omega)) u - supportFunction L u)
      mu mu
    simpa only [Function.comp_def] using (hident i).comp hdev
  have hdevInt : Integrable (directionalSupportDeviation S L u 0) mu :=
    hL2.integrable (by norm_num)
  have hsuppInt : Integrable
      (fun omega => supportFunction (F (X 0 omega)) u) mu := by
    have h := hdevInt.add (integrable_const (supportFunction L u))
    apply h.congr
    filter_upwards [] with omega
    change (supportFunction (F (X 0 omega)) u - supportFunction L u) +
      supportFunction L u = supportFunction (F (X 0 omega)) u
    ring
  have hcenter : mu[directionalSupportDeviation S L u 0] = 0 := by
    change ∫ omega,
      (supportFunction (F (X 0 omega)) u - supportFunction L u) ∂mu = 0
    rw [integral_sub hsuppInt (integrable_const (supportFunction L u)),
      ← hLsupport]
    simp
  exact tendstoInDistribution_sqrt_mul_supportFunction_minkowskiAverage_sub
    S L u Y
    (fun i omega => hFcompact (X i omega))
    (fun i omega => hFne (X i omega))
    hY hL2 hindepDev hidentDev hcenter

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
