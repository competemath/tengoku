/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.Seed.Algebra.Order.Archimedean.Basic
import Tengoku.Seed.Algebra.Order.Field.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional value at risk

Mathlib currently has no API for quantiles, value at risk, or conditional
value at risk.  This file starts the missing layer with the
Rockafellar--Uryasev variational definition.  For a loss `X` and upper-tail
mass `alpha`, the objective at threshold `t` is

`t + alpha⁻¹ * E[(X - t)₊]`.

For an integrable loss on a probability space and `0 < alpha ≤ 1`, the range
of this objective is bounded below.  Consequently its real infimum is
well-behaved.  The main result below proves subadditivity of conditional value
at risk directly from `(x + y)₊ ≤ x₊ + y₊`.

This is one of the deterministic CVaR ingredients in the martingale
Fuk--Nagaev argument used by Marchina.  It does not yet supply the martingale
Fuk--Nagaev inequality itself or identify this variational definition with an
integral of upper quantiles.
-/

open Real Set MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The variational objective whose infimum is upper-tail conditional value
at risk.  The parameter `alpha` is the upper-tail probability mass.-/
def cvarObjective (alpha : ℝ) (X : Omega → ℝ)
    (mu : Measure Omega) (t : ℝ) : ℝ :=
  t + alpha⁻¹ * ∫ omega, max (X omega - t) 0 ∂mu

/-- Upper-tail conditional value at risk, in variational form.-/
def conditionalValueAtRisk (alpha : ℝ) (X : Omega → ℝ)
    (mu : Measure Omega) : ℝ :=
  sInf (Set.range (cvarObjective alpha X mu))

/-- The positive excess over a fixed threshold is integrable whenever the
loss is integrable on a finite measure space.-/
theorem integrable_cvarExcess [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu) (t : ℝ) :
    Integrable (fun omega ↦ max (X omega - t) 0) mu := by
  exact (hX.sub (integrable_const t)).sup (integrable_const 0)

/-- Positive parts are subadditive.-/
theorem max_sub_add_sub_le (x y s t : ℝ) :
    max (x + y - (s + t)) 0 ≤ max (x - s) 0 + max (y - t) 0 := by
  have hx : x - s ≤ max (x - s) 0 := le_max_left _ _
  have hy : y - t ≤ max (y - t) 0 := le_max_left _ _
  have hzero : 0 ≤ max (x - s) 0 + max (y - t) 0 :=
    add_nonneg (le_max_right _ _) (le_max_right _ _)
  rw [max_le_iff]
  constructor
  · linarith
  · exact hzero

/-- The CVaR objective of a sum at the sum of two thresholds is bounded by
the sum of the two objectives.-/
theorem cvarObjective_add_le [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} (hX : Integrable X mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha : 0 ≤ alpha) (s t : ℝ) :
    cvarObjective alpha (fun omega ↦ X omega + Y omega) mu (s + t) ≤
      cvarObjective alpha X mu s + cvarObjective alpha Y mu t := by
  have hXs := integrable_cvarExcess hX s
  have hYt := integrable_cvarExcess hY t
  have hXY := integrable_cvarExcess (hX.add hY) (s + t)
  have hsum : Integrable
      (fun omega ↦ max (X omega - s) 0 + max (Y omega - t) 0) mu :=
    hXs.add hYt
  have hint :
      (∫ omega, max (X omega + Y omega - (s + t)) 0 ∂mu) ≤
        ∫ omega, max (X omega - s) 0 + max (Y omega - t) 0 ∂mu := by
    exact integral_mono hXY hsum (fun omega ↦
      max_sub_add_sub_le (X omega) (Y omega) s t)
  rw [integral_add hXs hYt] at hint
  unfold cvarObjective
  have hinv : 0 ≤ alpha⁻¹ := inv_nonneg.mpr halpha
  nlinarith [mul_le_mul_of_nonneg_left hint hinv]

/-- The CVaR objective is monotone in the loss.-/
theorem cvarObjective_mono_ae [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} (hX : Integrable X mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hXY : X ≤ᵐ[mu] Y) (t : ℝ) :
    cvarObjective alpha X mu t ≤ cvarObjective alpha Y mu t := by
  have hXt := integrable_cvarExcess hX t
  have hYt := integrable_cvarExcess hY t
  have hpoint :
      (fun omega ↦ max (X omega - t) 0) ≤ᵐ[mu]
        (fun omega ↦ max (Y omega - t) 0) := by
    filter_upwards [hXY] with omega homega
    exact max_le_max (sub_le_sub_right homega t) le_rfl
  have hint := integral_mono_ae hXt hYt hpoint
  unfold cvarObjective
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr halpha)) t

/-- The mean of an integrable loss is a lower bound for every CVaR
objective when `0 < alpha ≤ 1`.-/
theorem integral_le_cvarObjective [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) (t : ℝ) :
    (∫ omega, X omega ∂mu) ≤ cvarObjective alpha X mu t := by
  have hpos := integrable_cvarExcess hX t
  have hconstPos : Integrable
      (fun omega : Omega ↦ t + max (X omega - t) 0) mu :=
    (integrable_const t).add hpos
  have hpoint : ∀ omega,
      X omega ≤ t + max (X omega - t) 0 := by
    intro omega
    exact le_add_of_sub_left_le (le_max_left _ _)
  have hint :
      (∫ omega, X omega ∂mu) ≤
        ∫ omega, t + max (X omega - t) 0 ∂mu :=
    integral_mono hX hconstPos hpoint
  have hposInt : 0 ≤ ∫ omega, max (X omega - t) 0 ∂mu :=
    integral_nonneg (fun omega ↦ le_max_right _ _)
  have hinv : 1 ≤ alpha⁻¹ := by
    simpa only [inv_one] using
      (inv_le_inv₀ (show (0 : ℝ) < 1 by norm_num) halpha0).2 halpha1
  rw [integral_add (integrable_const t) hpos, integral_const] at hint
  simp only [probReal_univ, smul_eq_mul] at hint
  unfold cvarObjective
  have hscale := le_mul_of_one_le_left hposInt hinv
  nlinarith

/-- The family of variational objectives is bounded below under the natural
CVaR assumptions.-/
theorem bddBelow_range_cvarObjective [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    BddBelow (Set.range (cvarObjective alpha X mu)) := by
  refine ⟨∫ omega, X omega ∂mu, ?_⟩
  intro y hy
  obtain ⟨t, ht⟩ := hy
  rw [← ht]
  exact integral_le_cvarObjective hX halpha0 halpha1 t

/-- Conditional value at risk is no smaller than the mean.-/
theorem integral_le_conditionalValueAtRisk [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (∫ omega, X omega ∂mu) ≤ conditionalValueAtRisk alpha X mu := by
  unfold conditionalValueAtRisk
  apply le_csInf (Set.range_nonempty _)
  intro y hy
  obtain ⟨t, ht⟩ := hy
  rw [← ht]
  exact integral_le_cvarObjective hX halpha0 halpha1 t

/-- Subadditivity of upper-tail conditional value at risk.-/
theorem conditionalValueAtRisk_add_le [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Integrable X mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    conditionalValueAtRisk alpha (fun omega ↦ X omega + Y omega) mu ≤
      conditionalValueAtRisk alpha X mu + conditionalValueAtRisk alpha Y mu := by
  let fX : ℝ → ℝ := cvarObjective alpha X mu
  let fY : ℝ → ℝ := cvarObjective alpha Y mu
  let fXY : ℝ → ℝ := cvarObjective alpha (fun omega ↦ X omega + Y omega) mu
  have hbXY : BddBelow (Set.range fXY) := by
    exact bddBelow_range_cvarObjective (hX.add hY) halpha0 halpha1
  refine le_of_forall_pos_le_add fun epsilon hepsilon ↦ ?_
  obtain ⟨ax, ⟨sx, hsx⟩, hax⟩ :=
    Real.lt_sInf_add_pos (Set.range_nonempty fX) (half_pos hepsilon)
  obtain ⟨ay, ⟨sy, hsy⟩, hay⟩ :=
    Real.lt_sInf_add_pos (Set.range_nonempty fY) (half_pos hepsilon)
  subst ax
  subst ay
  have hinf : sInf (Set.range fXY) ≤ fXY (sx + sy) :=
    csInf_le hbXY ⟨sx + sy, rfl⟩
  have hadd : fXY (sx + sy) ≤ fX sx + fY sy := by
    exact cvarObjective_add_le hX hY halpha0.le sx sy
  change sInf (Set.range fXY) ≤
    sInf (Set.range fX) + sInf (Set.range fY) + epsilon
  calc
    sInf (Set.range fXY) ≤ fXY (sx + sy) := hinf
    _ ≤ fX sx + fY sy := hadd
    _ ≤ (sInf (Set.range fX) + epsilon / 2) +
        (sInf (Set.range fY) + epsilon / 2) := (add_lt_add hax hay).le
    _ = sInf (Set.range fX) + sInf (Set.range fY) + epsilon := by ring

/-- Conditional value at risk is monotone under almost-everywhere order.-/
theorem conditionalValueAtRisk_mono_ae [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Integrable X mu) (hY : Integrable Y mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hXY : X ≤ᵐ[mu] Y) :
    conditionalValueAtRisk alpha X mu ≤ conditionalValueAtRisk alpha Y mu := by
  have hbX : BddBelow (Set.range (cvarObjective alpha X mu)) :=
    bddBelow_range_cvarObjective hX halpha0 halpha1
  refine le_of_forall_pos_le_add fun epsilon hepsilon ↦ ?_
  obtain ⟨ay, ⟨t, ht⟩, hay⟩ :=
    Real.lt_sInf_add_pos
      (Set.range_nonempty (cvarObjective alpha Y mu)) hepsilon
  rw [← ht] at hay
  unfold conditionalValueAtRisk
  calc
    sInf (Set.range (cvarObjective alpha X mu)) ≤
        cvarObjective alpha X mu t :=
      csInf_le hbX ⟨t, rfl⟩
    _ ≤ cvarObjective alpha Y mu t :=
      cvarObjective_mono_ae hX hY halpha0.le hXY t
    _ ≤ sInf (Set.range (cvarObjective alpha Y mu)) + epsilon := hay.le

/-- CVaR of a deterministic loss is that loss.-/
theorem conditionalValueAtRisk_const [IsProbabilityMeasure mu]
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) (c : ℝ) :
    conditionalValueAtRisk alpha (fun _ : Omega ↦ c) mu = c := by
  have hc : Integrable (fun _ : Omega ↦ c) mu := integrable_const c
  have hb : BddBelow
      (Set.range (cvarObjective alpha (fun _ : Omega ↦ c) mu)) :=
    bddBelow_range_cvarObjective hc halpha0 halpha1
  apply le_antisymm
  · unfold conditionalValueAtRisk
    have h := csInf_le hb
      (show cvarObjective alpha (fun _ : Omega ↦ c) mu c ∈
        Set.range (cvarObjective alpha (fun _ : Omega ↦ c) mu) from ⟨c, rfl⟩)
    simpa [cvarObjective] using h
  · have hmean := integral_le_conditionalValueAtRisk hc halpha0 halpha1
    simpa using hmean

/-- Translation equivariance of conditional value at risk.-/
theorem conditionalValueAtRisk_add_const [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) (c : ℝ) :
    conditionalValueAtRisk alpha (fun omega ↦ X omega + c) mu =
      conditionalValueAtRisk alpha X mu + c := by
  have hc : Integrable (fun _ : Omega ↦ c) mu := integrable_const c
  have hnegc : Integrable (fun _ : Omega ↦ -c) mu := integrable_const (-c)
  have hXc : Integrable (fun omega ↦ X omega + c) mu := hX.add hc
  apply le_antisymm
  · have h := conditionalValueAtRisk_add_le hX hc halpha0 halpha1
    rw [conditionalValueAtRisk_const halpha0 halpha1 c] at h
    exact h
  · have h := conditionalValueAtRisk_add_le hXc hnegc halpha0 halpha1
    rw [conditionalValueAtRisk_const halpha0 halpha1 (-c)] at h
    have hsimplify :
        (fun omega ↦ (X omega + c) + -c) = X := by
      funext omega
      ring
    rw [hsimplify] at h
    linarith

/-! ## Eventwise upper-tail bounds -/

/-- The integral over an event is controlled by any threshold plus the full
positive excess above that threshold.  This elementary inequality is the
eventwise core of the dual description of CVaR.-/
theorem setIntegral_le_measureReal_mul_add_cvarExcess
    [IsFiniteMeasure mu] {X : Omega → ℝ} (hX : Integrable X mu)
    {A : Set Omega} (hA : MeasurableSet A) (t : ℝ) :
    (∫ omega in A, X omega ∂mu) ≤
      mu.real A * t + ∫ omega, max (X omega - t) 0 ∂mu := by
  have hleft : Integrable (A.indicator X) mu := hX.indicator hA
  have hconst : Integrable (A.indicator (fun _ : Omega ↦ t)) mu :=
    (integrable_const t).indicator hA
  have hpos := integrable_cvarExcess hX t
  have hright : Integrable
      (fun omega ↦ A.indicator (fun _ : Omega ↦ t) omega +
        max (X omega - t) 0) mu := hconst.add hpos
  have hpoint : ∀ omega,
      A.indicator X omega ≤
        A.indicator (fun _ : Omega ↦ t) omega + max (X omega - t) 0 := by
    intro omega
    by_cases homega : omega ∈ A
    · simp only [Set.indicator_of_mem homega]
      exact le_add_of_sub_left_le (le_max_left _ _)
    · simp only [Set.indicator_of_notMem homega, zero_add]
      exact le_max_right _ _
  have hint := integral_mono hleft hright hpoint
  rw [integral_add hconst hpos, integral_indicator hA,
    integral_indicator_const t hA, smul_eq_mul] at hint
  exact hint

/-- If an event has exactly upper-tail mass `alpha`, its partial expectation
is at most `alpha` times CVaR.  Equality of the event mass is essential for
signed losses: the analogous statement with only `mu.real A ≤ alpha` is
false, for instance for a negative constant loss and the empty event.-/
theorem setIntegral_le_mul_conditionalValueAtRisk_of_measureReal_eq
    [IsProbabilityMeasure mu] {X : Omega → ℝ} (hX : Integrable X mu)
    {A : Set Omega} (hA : MeasurableSet A)
    {alpha : ℝ} (halpha0 : 0 < alpha) (_halpha1 : alpha ≤ 1)
    (hmeasure : mu.real A = alpha) :
    (∫ omega in A, X omega ∂mu) ≤
      alpha * conditionalValueAtRisk alpha X mu := by
  have hnormalized :
      (∫ omega in A, X omega ∂mu) / alpha ≤
        conditionalValueAtRisk alpha X mu := by
    unfold conditionalValueAtRisk
    apply le_csInf (Set.range_nonempty _)
    intro y hy
    obtain ⟨t, ht⟩ := hy
    rw [← ht]
    have hthreshold :=
      setIntegral_le_measureReal_mul_add_cvarExcess hX hA t
    rw [hmeasure] at hthreshold
    unfold cvarObjective
    apply (div_le_iff₀ halpha0).2
    calc
      (∫ omega in A, X omega ∂mu) ≤
          alpha * t + ∫ omega, max (X omega - t) 0 ∂mu := hthreshold
      _ = (t + alpha⁻¹ * ∫ omega, max (X omega - t) 0 ∂mu) * alpha := by
        field_simp [halpha0.ne']
  simpa only [mul_comm] using (div_le_iff₀ halpha0).1 hnormalized

/-- For a nonnegative loss, equality of the event mass can be relaxed to an
upper bound.  The nonnegativity assumption is necessary: for a negative
constant loss and the empty event the left side is zero whereas
`alpha * CVaR` is negative.-/
theorem setIntegral_le_mul_conditionalValueAtRisk_of_measureReal_le_of_nonneg
    [IsProbabilityMeasure mu] {X : Omega → ℝ} (hX : Integrable X mu)
    (hXnonneg : 0 ≤ᵐ[mu] X) {A : Set Omega} (hA : MeasurableSet A)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hmeasure : mu.real A ≤ alpha) :
    (∫ omega in A, X omega ∂mu) ≤
      alpha * conditionalValueAtRisk alpha X mu := by
  have hnormalized :
      (∫ omega in A, X omega ∂mu) / alpha ≤
        conditionalValueAtRisk alpha X mu := by
    unfold conditionalValueAtRisk
    apply le_csInf (Set.range_nonempty _)
    intro y hy
    obtain ⟨t, htEq⟩ := hy
    rw [← htEq]
    apply (div_le_iff₀ halpha0).2
    by_cases ht : 0 ≤ t
    · have hthreshold :=
        setIntegral_le_measureReal_mul_add_cvarExcess hX hA t
      have hmeasureMul : mu.real A * t ≤ alpha * t :=
        mul_le_mul_of_nonneg_right hmeasure ht
      unfold cvarObjective
      calc
        (∫ omega in A, X omega ∂mu) ≤
            mu.real A * t +
              ∫ omega, max (X omega - t) 0 ∂mu := hthreshold
        _ ≤ alpha * t + ∫ omega, max (X omega - t) 0 ∂mu :=
          add_le_add_left hmeasureMul _
        _ = (t + alpha⁻¹ *
            ∫ omega, max (X omega - t) 0 ∂mu) * alpha := by
          field_simp [halpha0.ne']
    · have htneg : t < 0 := lt_of_not_ge ht
      have hmax :
          (fun omega ↦ max (X omega - t) 0) =ᵐ[mu]
            (fun omega ↦ X omega - t) := by
        filter_upwards [hXnonneg] with omega homega
        change 0 ≤ X omega at homega
        rw [max_eq_left]
        linarith
      have hexcess :
          (∫ omega, max (X omega - t) 0 ∂mu) =
            (∫ omega, X omega ∂mu) - t := by
        rw [integral_congr_ae hmax,
          integral_sub hX (integrable_const t), integral_const]
        simp only [probReal_univ, smul_eq_mul, one_mul]
      have hpartial :
          (∫ omega in A, X omega ∂mu) ≤ ∫ omega, X omega ∂mu :=
        setIntegral_le_integral hX hXnonneg
      have hcorrection : 0 ≤ (alpha - 1) * t :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr halpha1) htneg.le
      unfold cvarObjective
      rw [hexcess]
      calc
        (∫ omega in A, X omega ∂mu) ≤ ∫ omega, X omega ∂mu := hpartial
        _ ≤ (t + alpha⁻¹ * ((∫ omega, X omega ∂mu) - t)) * alpha := by
          field_simp [halpha0.ne']
          nlinarith
  simpa only [mul_comm] using (div_le_iff₀ halpha0).1 hnormalized

/-- A measurable upper-tail event separated by a threshold realizes the
eventwise CVaR bound.  This gives the exact event-dual formula whenever a
top-`alpha` event exists without requiring a general quantile API.-/
theorem mul_conditionalValueAtRisk_eq_setIntegral_of_thresholdEvent
    [IsProbabilityMeasure mu] {X : Omega → ℝ} (hX : Integrable X mu)
    {A : Set Omega} (hA : MeasurableSet A)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hmeasure : mu.real A = alpha) (t : ℝ)
    (hupper : ∀ omega ∈ A, t ≤ X omega)
    (hlower : ∀ omega ∉ A, X omega ≤ t) :
    alpha * conditionalValueAtRisk alpha X mu =
      ∫ omega in A, X omega ∂mu := by
  have hevent :=
    setIntegral_le_mul_conditionalValueAtRisk_of_measureReal_eq
      hX hA halpha0 halpha1 hmeasure
  have hfun :
      (fun omega ↦ max (X omega - t) 0) =
        A.indicator (fun omega ↦ X omega - t) := by
    funext omega
    by_cases homega : omega ∈ A
    · rw [Set.indicator_of_mem homega, max_eq_left]
      exact sub_nonneg.mpr (hupper omega homega)
    · rw [Set.indicator_of_notMem homega, max_eq_right]
      exact sub_nonpos.mpr (hlower omega homega)
  have hexcess :
      (∫ omega, max (X omega - t) 0 ∂mu) =
        (∫ omega in A, X omega ∂mu) - alpha * t := by
    rw [hfun, integral_indicator hA,
      integral_sub hX.integrableOn (integrable_const t),
      setIntegral_const, smul_eq_mul, hmeasure]
  have hb : BddBelow (Set.range (cvarObjective alpha X mu)) :=
    bddBelow_range_cvarObjective hX halpha0 halpha1
  have hcvarObj :
      conditionalValueAtRisk alpha X mu ≤ cvarObjective alpha X mu t := by
    unfold conditionalValueAtRisk
    exact csInf_le hb ⟨t, rfl⟩
  have hscaled := mul_le_mul_of_nonneg_left hcvarObj halpha0.le
  unfold cvarObjective at hscaled
  rw [hexcess] at hscaled
  apply le_antisymm
  · calc
      alpha * conditionalValueAtRisk alpha X mu ≤
          alpha * (t + alpha⁻¹ *
            ((∫ omega in A, X omega ∂mu) - alpha * t)) := hscaled
      _ = ∫ omega in A, X omega ∂mu := by
        field_simp [halpha0.ne']
        ring
  · exact hevent

/-! ## Exponential-moment bounds -/

/-- Exponential domination of the positive part, with the normalization that
makes the optimized CVaR bound have no additive constant.-/
theorem max_le_exp_mul_sub_one_div {lambda : ℝ} (hlambda : 0 < lambda)
    (x : ℝ) :
    max x 0 ≤ Real.exp (lambda * x - 1) / lambda := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    apply (le_div_iff₀ hlambda).2
    have h := Real.add_one_le_exp (lambda * x - 1)
    simpa only [sub_add_cancel, mul_comm] using h
  · rw [max_eq_right (le_of_not_ge hx)]
    positivity

/-- Every threshold objective is bounded by an exponential moment.-/
theorem cvarObjective_le_of_exponentialMoment
    [IsFiniteMeasure mu] {X : Omega → ℝ} (hX : Integrable X mu)
    {alpha lambda : ℝ} (halpha : 0 ≤ alpha) (hlambda : 0 < lambda)
    (hExp : Integrable (fun omega ↦ Real.exp (lambda * X omega)) mu)
    (t : ℝ) :
    cvarObjective alpha X mu t ≤
      t + alpha⁻¹ *
        ((Real.exp (-lambda * t - 1) / lambda) *
          ∫ omega, Real.exp (lambda * X omega) ∂mu) := by
  have hpos := integrable_cvarExcess hX t
  have hright : Integrable
      (fun omega ↦ (Real.exp (-lambda * t - 1) / lambda) *
        Real.exp (lambda * X omega)) mu :=
    hExp.const_mul (Real.exp (-lambda * t - 1) / lambda)
  have hpoint : ∀ omega,
      max (X omega - t) 0 ≤
        (Real.exp (-lambda * t - 1) / lambda) *
          Real.exp (lambda * X omega) := by
    intro omega
    calc
      max (X omega - t) 0 ≤
          Real.exp (lambda * (X omega - t) - 1) / lambda :=
        max_le_exp_mul_sub_one_div hlambda (X omega - t)
      _ = (Real.exp (-lambda * t - 1) / lambda) *
          Real.exp (lambda * X omega) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          Real.exp (lambda * (X omega - t) - 1) * lambda⁻¹ =
              (Real.exp (-lambda * t - 1) *
                Real.exp (lambda * X omega)) * lambda⁻¹ := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
          _ = Real.exp (-lambda * t - 1) * lambda⁻¹ *
              Real.exp (lambda * X omega) := by ring
  have hint := integral_mono hpos hright hpoint
  rw [integral_const_mul] at hint
  unfold cvarObjective
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr halpha)) t

/-- An integrable exponential has strictly positive integral on a probability
space.-/
theorem integral_exp_mul_pos [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (lambda : ℝ)
    (hExp : Integrable (fun omega ↦ Real.exp (lambda * X omega)) mu) :
    0 < ∫ omega, Real.exp (lambda * X omega) ∂mu := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (ae_of_all mu fun omega ↦ (Real.exp_pos _).le) hExp).2
  have hsupport :
      Function.support (fun omega ↦ Real.exp (lambda * X omega)) = Set.univ := by
    ext omega
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hsupport, measure_univ]
  norm_num

/-- Chernoff/log-MGF upper bound for CVaR.-/
theorem conditionalValueAtRisk_le_log_integral_exp_div
    [IsProbabilityMeasure mu] {X : Omega → ℝ} (hX : Integrable X mu)
    {alpha lambda : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hlambda : 0 < lambda)
    (hExp : Integrable (fun omega ↦ Real.exp (lambda * X omega)) mu) :
    conditionalValueAtRisk alpha X mu ≤
      Real.log ((∫ omega, Real.exp (lambda * X omega) ∂mu) / alpha) / lambda := by
  let M : ℝ := ∫ omega, Real.exp (lambda * X omega) ∂mu
  let t : ℝ := (Real.log (M / alpha) - 1) / lambda
  have hExpIntegral : 0 < M := integral_exp_mul_pos X lambda hExp
  have hratio : 0 < M / alpha := div_pos hExpIntegral halpha0
  have hMne : M ≠ 0 := hExpIntegral.ne'
  have hb : BddBelow (Set.range (cvarObjective alpha X mu)) :=
    bddBelow_range_cvarObjective hX halpha0 halpha1
  have hcvarObj :
      conditionalValueAtRisk alpha X mu ≤ cvarObjective alpha X mu t := by
    unfold conditionalValueAtRisk
    exact csInf_le hb ⟨t, rfl⟩
  have hobjExp :
      cvarObjective alpha X mu t ≤
        t + alpha⁻¹ * ((Real.exp (-lambda * t - 1) / lambda) * M) := by
    exact cvarObjective_le_of_exponentialMoment
      hX halpha0.le hlambda hExp t
  have hexponent :
      -lambda * t - 1 = -Real.log (M / alpha) := by
    dsimp only [t]
    field_simp [hlambda.ne']
    ring
  change conditionalValueAtRisk alpha X mu ≤ Real.log (M / alpha) / lambda
  calc
    conditionalValueAtRisk alpha X mu ≤ cvarObjective alpha X mu t := hcvarObj
    _ ≤ t + alpha⁻¹ * ((Real.exp (-lambda * t - 1) / lambda) * M) := hobjExp
    _ = Real.log (M / alpha) / lambda := by
      rw [hexponent, Real.exp_neg, Real.exp_log hratio]
      dsimp only [t]
      field_simp [halpha0.ne', hlambda.ne', hMne]
      ring

end ProbabilityTheory
