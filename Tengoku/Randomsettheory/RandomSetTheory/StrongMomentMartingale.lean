/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.OneSidedMartingaleMGF
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentTruncationMGF
import Tengoku.Randomsettheory.RandomSetTheory.CVaRQuantile

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strong-moment one-sided martingale bounds

This file assembles the scalar and conditional Taylor estimates along a
filtration.  For martingale differences `D i`, it applies the estimates to
the upper truncations `min (D i) y`, composes the conditional MGFs, and
collects all deterministic moment proxies into a single Taylor exponent.

The resulting Chernoff and CVaR inequalities are the analytic martingale
core of Rio's strong-moment Fuk--Nagaev proof.  Optimization of the
intermediate moments is intentionally kept separate.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}

/-! ## Upper-truncation residuals -/

/-- The nonnegative part discarded by upper truncation at height `y`.-/
def upperTruncationResidual (X : Omega → ℝ) (y : ℝ) : Omega → ℝ :=
  fun omega => X omega - upperTruncation X y omega

/--
@isnad1 id=eq.0h4v.s5.94e85a95864a from=translated src=- shape=9919ee3a vocab=583857d5
-/
@[simp] theorem upperTruncationResidual_apply
    (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    upperTruncationResidual X y omega = X omega - min (X omega) y := rfl

/-- Upper truncation and its residual reconstruct the original variable
pointwise.
@isnad1 id=eq.0h4v.s5.55bd592c258b from=translated src=- shape=8513dff0 vocab=6d9a085e
-/
theorem upperTruncation_add_residual
    (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    upperTruncation X y omega + upperTruncationResidual X y omega =
      X omega := by
  unfold upperTruncationResidual
  ring

/-- The residual of an upper truncation is nonnegative.
@isnad1 id=le.0h4v.s4.a4b13e19e0ed from=translated src=- shape=be7e24f4 vocab=1eed4bc0
-/
theorem upperTruncationResidual_nonneg
    (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    0 ≤ upperTruncationResidual X y omega := by
  unfold upperTruncationResidual upperTruncation
  exact sub_nonneg.mpr (min_le_left _ _)

/-- The residual is the positive excess above the truncation height.
@isnad1 id=eq.0h4v.s5.2690927f18aa from=translated src=- shape=bf82df15 vocab=545a2fd8
-/
theorem upperTruncationResidual_eq_max_sub
    (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    upperTruncationResidual X y omega = max (X omega - y) 0 := by
  by_cases hxy : X omega ≤ y
  · rw [upperTruncationResidual_apply, min_eq_left hxy,
      max_eq_right (sub_nonpos.mpr hxy), sub_self]
  · have hyx : y ≤ X omega := le_of_lt (lt_of_not_ge hxy)
    rw [upperTruncationResidual_apply, min_eq_right hyx,
      max_eq_left (sub_nonneg.mpr hyx)]

/-- A positive `q`-moment controls the residual left by upper truncation.
This is the deterministic Markov bound used in the strong-moment
Fuk--Nagaev decomposition.
@isnad1 id=le.2h5v.s6.d80ca17a8255 from=translated src=- shape=14b4bdca vocab=ac690e26
-/
theorem upperTruncationResidual_le_pow_div
    (X : Omega → ℝ) {y : ℝ} (hy : 0 < y)
    (q : ℕ) (hq : 1 ≤ q) (omega : Omega) :
    upperTruncationResidual X y omega ≤
      (max (X omega) 0) ^ q / y ^ (q - 1) := by
  by_cases hxy : X omega ≤ y
  · rw [upperTruncationResidual_apply, min_eq_left hxy]
    simp only [sub_self]
    positivity
  · have hyx : y < X omega := lt_of_not_ge hxy
    have hx : 0 < X omega := hy.trans hyx
    have hpowPos : 0 < y ^ (q - 1) := pow_pos hy _
    have hpowLe : y ^ (q - 1) ≤ X omega ^ (q - 1) :=
      pow_le_pow_left₀ hy.le hyx.le _
    have hxScaled : X omega * y ^ (q - 1) ≤
        X omega * X omega ^ (q - 1) :=
      mul_le_mul_of_nonneg_left hpowLe hx.le
    have hqEq : q - 1 + 1 = q := Nat.sub_add_cancel hq
    rw [upperTruncationResidual_apply, min_eq_right hyx.le,
      max_eq_left hx.le]
    apply (le_div_iff₀ hpowPos).2
    calc
      (X omega - y) * y ^ (q - 1) ≤ X omega * y ^ (q - 1) := by
        exact mul_le_mul_of_nonneg_right (sub_le_self _ hy.le) hpowPos.le
      _ ≤ X omega * X omega ^ (q - 1) := hxScaled
      _ = X omega ^ q := by
        rw [← pow_succ', hqEq]

/-- Sharp form of the truncation-residual estimate.  Bernoulli's inequality
gives the factor `1 / q` which appears in Rio's constant `beta_q`.
@isnad1 id=le.2h5v.s6.f9434f5ad38e from=translated src=- shape=40e846af vocab=31441e77
-/
theorem upperTruncationResidual_le_pow_div_natCast_mul
    (X : Omega → ℝ) {y : ℝ} (hy : 0 < y)
    (q : ℕ) (hq : 1 ≤ q) (omega : Omega) :
    upperTruncationResidual X y omega ≤
      (max (X omega) 0) ^ q /
        ((q : ℝ) * y ^ (q - 1)) := by
  by_cases hxy : X omega ≤ y
  · rw [upperTruncationResidual_apply, min_eq_left hxy]
    simp only [sub_self]
    positivity
  · have hyx : y < X omega := lt_of_not_ge hxy
    have hx : 0 < X omega := hy.trans hyx
    have hqReal : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hyPow : 0 < y ^ (q - 1) := pow_pos hy _
    have hden : 0 < (q : ℝ) * y ^ (q - 1) := mul_pos hqReal hyPow
    let r : ℝ := X omega / y
    have hr : 1 ≤ r := (le_div_iff₀ hy).2 (by simpa using hyx.le)
    have hbern := one_add_mul_sub_le_pow
      (a := r) (show (-1 : ℝ) ≤ r by linarith) q
    have hcore : (q : ℝ) * (r - 1) ≤ r ^ q := by
      nlinarith
    have hyq : 0 ≤ y ^ q := (pow_pos hy q).le
    have hscaled := mul_le_mul_of_nonneg_right hcore hyq
    rw [upperTruncationResidual_apply, min_eq_right hyx.le,
      max_eq_left hx.le]
    apply (le_div_iff₀ hden).2
    dsimp only [r] at hscaled
    rw [div_pow] at hscaled
    field_simp [hy.ne'] at hscaled
    have hqEq : q - 1 + 1 = q := Nat.sub_add_cancel hq
    have hyPowEq : y ^ (q - 1) * y = y ^ q := by
      rw [← pow_succ, hqEq]
    apply (mul_le_mul_iff_right₀ hy).mp
    calc
      y * ((X omega - y) * ((q : ℝ) * y ^ (q - 1))) =
          (q : ℝ) * (X omega - y) * (y ^ (q - 1) * y) := by ring
      _ = (q : ℝ) * (X omega - y) * y ^ q := by rw [hyPowEq]
      _ ≤ y * X omega ^ q := hscaled

/-- Integrability is preserved by passing from a variable to its upper
truncation residual.
@isnad1 id=integrab.1h5v.s6.a8d1cc8ebf40 from=translated src=- shape=82d6c675 vocab=fde3a70c
-/
theorem integrable_upperTruncationResidual [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu) (y : ℝ) :
    Integrable (upperTruncationResidual X y) mu := by
  exact hX.sub (integrable_upperTruncation hX y)

/-! ## Upper-truncation certificates -/

/-- The ordinary upper-truncation estimate packaged as a one-sided MGF
certificate with deterministic moment proxies.
@isnad1 id=hasonesi.8h8v.s8.2e83a6afaf55 from=translated src=- shape=720b88d6 vocab=3c108b23
-/
theorem hasOneSidedMGF_upperTruncation_of_strongMoment
    [IsProbabilityMeasure mu]
    (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {y second : ℝ} (hy : 0 ≤ y)
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
      (fun t => strongMomentTaylorExponent q t y second moment) mu := by
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
    exact integral_exp_mul_upperTruncation_le_exp_strongMomentTaylorExponent
      D q hq ht hy hD hDsq hpow hcenter hsecond moment hmoment

/-- Conditional upper-truncation estimate packaged as a one-sided MGF
certificate.
@isnad1 id=hascondo.9h9v.s8.66bb09f9302a from=translated src=- shape=cc765d53 vocab=3609e608
-/
theorem hasCondOneSidedMGF_upperTruncation_of_strongMoment
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) (D : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {y second : ℝ} (hy : 0 ≤ y)
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
      (fun t => strongMomentTaylorExponent q t y second moment) mu := by
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
    exact condExp_exp_mul_upperTruncation_le_exp_strongMomentTaylorExponent
      hm D q hq ht hy hD hDsq hpow hcenter hsecond moment hmoment

/-! ## Composition along a filtration -/

variable (filtration : Filtration ℕ mOmega)

/-- A finite adapted sequence of upper-truncated martingale differences has
the strong-moment Taylor exponent obtained by summing its deterministic
moment proxies.
@isnad1 id=hasonesi.13h10v.s9.c80106ae231f from=translated src=- shape=5c44b448 vocab=e59b47bb
-/
theorem hasOneSidedMGF_sum_upperTruncation_of_strongMoment
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hAdapted : StronglyAdapted filtration D)
    (second : ℕ → ℝ) (moment : ℕ → ℕ → ℝ)
    (n q : ℕ) (hn : 0 < n) (hq : 3 ≤ q)
    {y : ℝ} (hy : 0 ≤ y)
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
      (fun t => strongMomentTaylorExponent q t y
        (∑ i ∈ Finset.range n, second i)
        (fun k => ∑ i ∈ Finset.range n, moment i k)) mu := by
  let U : ℕ → Omega → ℝ := fun i => upperTruncation (D i) y
  let psi : ℕ → ℝ → ℝ := fun i t =>
    strongMomentTaylorExponent q t y (second i) (moment i)
  let B : ℕ → ℝ := fun _ => y
  have hUAdapted : StronglyAdapted filtration U := by
    intro i
    change StronglyMeasurable[filtration i]
      (fun omega => min (D i omega) y)
    exact ((hAdapted i).measurable.min measurable_const).stronglyMeasurable
  have hzero : HasOneSidedMGF (U 0) (psi 0) mu := by
    dsimp only [U, psi]
    exact hasOneSidedMGF_upperTruncation_of_strongMoment
      (D 0) q hq hy (hD 0 hn) (hDsq 0 hn) (hpow 0 hn)
        hcenter0 hsecond0 (moment 0) hmoment0
  have hcond : ∀ i < n - 1,
      HasCondOneSidedMGF (filtration i) (filtration.le i)
        (U (i + 1)) (psi (i + 1)) mu := by
    intro i hi
    dsimp only [U, psi]
    exact hasCondOneSidedMGF_upperTruncation_of_strongMoment
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
  exact (sum_strongMomentTaylorExponent
    (Finset.range n) q t y second moment).symm

/-! ## Generic consequences of a one-sided MGF certificate -/

/-- Chernoff bound associated with a generic one-sided exponent.
@isnad1 id=le.2h7v.s6.b55a4c7e2745 from=translated src=- shape=81164f64 vocab=8f15fbf1
-/
theorem HasOneSidedMGF.measureReal_ge_le
    [IsFiniteMeasure mu] {X : Omega → ℝ} {psi : ℝ → ℝ}
    (hX : HasOneSidedMGF X psi mu) {epsilon t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | epsilon ≤ X omega} ≤
      Real.exp (-t * epsilon + psi t) := by
  calc
    mu.real {omega | epsilon ≤ X omega} ≤
        Real.exp (-t * epsilon) * mgf X mu t :=
      measure_ge_le_exp_mul_mgf epsilon ht (hX.integrable_exp_mul t ht)
    _ ≤ Real.exp (-t * epsilon) * Real.exp (psi t) := by
      exact mul_le_mul_of_nonneg_left (hX.mgf_le t ht) (Real.exp_nonneg _)
    _ = Real.exp (-t * epsilon + psi t) := by rw [Real.exp_add]

/-- CVaR bound associated with a generic one-sided exponent.
@isnad1 id=le.5h7v.s6.698c8c1c3232 from=translated src=- shape=a3341af6 vocab=9b4d56e5
-/
theorem HasOneSidedMGF.conditionalValueAtRisk_le
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {psi : ℝ → ℝ}
    (hmgf : HasOneSidedMGF X psi mu) (hX : Integrable X mu)
    {alpha t : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (ht : 0 < t) :
    conditionalValueAtRisk alpha X mu ≤
      (psi t - Real.log alpha) / t := by
  let I : ℝ := ∫ omega, Real.exp (t * X omega) ∂mu
  have hExp := hmgf.integrable_exp_mul t ht.le
  have hIpos : 0 < I := integral_exp_mul_pos X t hExp
  have hmgfLe : I ≤ Real.exp (psi t) := by
    simpa only [mgf, I] using hmgf.mgf_le t ht.le
  have hratioLe : I / alpha ≤ Real.exp (psi t) / alpha :=
    div_le_div_of_nonneg_right hmgfLe halpha0.le
  have hlogLe : Real.log (I / alpha) ≤
      Real.log (Real.exp (psi t) / alpha) :=
    Real.log_le_log (div_pos hIpos halpha0) hratioLe
  have hbase := conditionalValueAtRisk_le_log_integral_exp_div
    hX halpha0 halpha1 ht hExp
  calc
    conditionalValueAtRisk alpha X mu ≤ Real.log (I / alpha) / t := by
      simpa only [I] using hbase
    _ ≤ Real.log (Real.exp (psi t) / alpha) / t :=
      div_le_div_of_nonneg_right hlogLe ht.le
    _ = (psi t - Real.log alpha) / t := by
      rw [Real.log_div (Real.exp_pos _).ne' halpha0.ne', Real.log_exp]

/-! ## CVaR control of upper-truncation residuals -/

/-- The CVaR of a nonnegative integrable loss is at most its mean divided
by the upper-tail mass.  This is the threshold-zero candidate in the
Rockafellar--Uryasev variational formula.
@isnad1 id=le.4h5v.s7.10e7ab1d24ad from=translated src=- shape=4188cfcd vocab=ab624ab2
-/
theorem conditionalValueAtRisk_le_inv_mul_integral_of_nonneg
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu) (hXnonneg : 0 ≤ᵐ[mu] X)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    conditionalValueAtRisk alpha X mu ≤
      alpha⁻¹ * ∫ omega, X omega ∂mu := by
  have hb : BddBelow (Set.range (cvarObjective alpha X mu)) :=
    bddBelow_range_cvarObjective hX halpha0 halpha1
  unfold conditionalValueAtRisk
  calc
    sInf (Set.range (cvarObjective alpha X mu)) ≤
        cvarObjective alpha X mu 0 :=
      csInf_le hb ⟨0, rfl⟩
    _ = alpha⁻¹ * ∫ omega, X omega ∂mu := by
      unfold cvarObjective
      simp only [zero_add, sub_zero]
      congr 1
      apply integral_congr_ae
      filter_upwards [hXnonneg] with omega homega
      exact max_eq_left homega

/-- CVaR bound for one upper-truncation residual in terms of its positive
`q`-moment.
@isnad1 id=le.6h7v.s7.9d9628207237 from=translated src=- shape=84e91737 vocab=7569a708
-/
theorem conditionalValueAtRisk_upperTruncationResidual_le
    [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (hX : Integrable X mu)
    (q : ℕ) (hq : 1 ≤ q)
    (hpow : Integrable (fun omega => (max (X omega) 0) ^ q) mu)
    {y alpha : ℝ} (hy : 0 < y)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    conditionalValueAtRisk alpha (upperTruncationResidual X y) mu ≤
      alpha⁻¹ *
        ((∫ omega, (max (X omega) 0) ^ q ∂mu) /
          ((q : ℝ) * y ^ (q - 1))) := by
  have hR : Integrable (upperTruncationResidual X y) mu :=
    integrable_upperTruncationResidual hX y
  have hmajor : Integrable
      (fun omega => (max (X omega) 0) ^ q /
        ((q : ℝ) * y ^ (q - 1))) mu :=
    hpow.div_const _
  have hint :
      (∫ omega, upperTruncationResidual X y omega ∂mu) ≤
        ∫ omega, (max (X omega) 0) ^ q /
          ((q : ℝ) * y ^ (q - 1)) ∂mu := by
    exact integral_mono hR hmajor
      (fun omega =>
        upperTruncationResidual_le_pow_div_natCast_mul X hy q hq omega)
  calc
    conditionalValueAtRisk alpha (upperTruncationResidual X y) mu ≤
        alpha⁻¹ * ∫ omega, upperTruncationResidual X y omega ∂mu :=
      conditionalValueAtRisk_le_inv_mul_integral_of_nonneg hR
        (ae_of_all mu fun omega => upperTruncationResidual_nonneg X y omega)
        halpha0 halpha1
    _ ≤ alpha⁻¹ *
        ∫ omega, (max (X omega) 0) ^ q /
          ((q : ℝ) * y ^ (q - 1)) ∂mu :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr halpha0.le)
    _ = alpha⁻¹ *
        ((∫ omega, (max (X omega) 0) ^ q ∂mu) /
          ((q : ℝ) * y ^ (q - 1))) := by
      rw [integral_div]

/-- Finite-sum form of the residual CVaR estimate.
@isnad1 id=le.6h8v.s8.bc03a882c305 from=translated src=- shape=28ad0fd6 vocab=0b65d303
-/
theorem conditionalValueAtRisk_sum_upperTruncationResidual_le
    [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (n q : ℕ) (hq : 1 ≤ q)
    (hD : ∀ i < n, Integrable (D i) mu)
    (hpow : ∀ i < n,
      Integrable (fun omega => (max (D i omega) 0) ^ q) mu)
    {y alpha : ℝ} (hy : 0 < y)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    conditionalValueAtRisk alpha
        (fun omega => ∑ i ∈ Finset.range n,
          upperTruncationResidual (D i) y omega) mu ≤
      alpha⁻¹ *
        ((∑ i ∈ Finset.range n,
          ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
            ((q : ℝ) * y ^ (q - 1))) := by
  have hR : ∀ i ∈ Finset.range n,
      Integrable (upperTruncationResidual (D i) y) mu := by
    intro i hi
    exact integrable_upperTruncationResidual (hD i (Finset.mem_range.mp hi)) y
  have hRsum : Integrable
      (fun omega => ∑ i ∈ Finset.range n,
        upperTruncationResidual (D i) y omega) mu :=
    integrable_finsetSum (Finset.range n) hR
  have hIntLe :
      (∫ omega, ∑ i ∈ Finset.range n,
          upperTruncationResidual (D i) y omega ∂mu) ≤
        (∑ i ∈ Finset.range n,
          ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
            ((q : ℝ) * y ^ (q - 1)) := by
    rw [integral_finsetSum (Finset.range n) hR, Finset.sum_div]
    exact Finset.sum_le_sum fun i hi => by
      have hmajor : Integrable
          (fun omega => (max (D i omega) 0) ^ q /
            ((q : ℝ) * y ^ (q - 1))) mu :=
        (hpow i (Finset.mem_range.mp hi)).div_const _
      have hiInt := integral_mono (hR i hi) hmajor
        (fun omega =>
          upperTruncationResidual_le_pow_div_natCast_mul (D i) hy q hq omega)
      simpa only [integral_div] using hiInt
  calc
    conditionalValueAtRisk alpha
        (fun omega => ∑ i ∈ Finset.range n,
          upperTruncationResidual (D i) y omega) mu ≤
        alpha⁻¹ *
          ∫ omega, ∑ i ∈ Finset.range n,
            upperTruncationResidual (D i) y omega ∂mu :=
      conditionalValueAtRisk_le_inv_mul_integral_of_nonneg hRsum
        (ae_of_all mu fun omega => Finset.sum_nonneg fun i _ =>
          upperTruncationResidual_nonneg (D i) y omega)
        halpha0 halpha1
    _ ≤ alpha⁻¹ *
        ((∑ i ∈ Finset.range n,
          ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
            ((q : ℝ) * y ^ (q - 1))) :=
      mul_le_mul_of_nonneg_left hIntLe (inv_nonneg.mpr halpha0.le)

/-- A one-sided MGF certificate for the upper-truncated sum, together with
positive `q`-moments of the original summands, gives a parameterized CVaR
bound for the original sum.  No optimization in `t` or `y` is performed.
@isnad1 id=le.8h10v.s8.0523c67b01cd from=translated src=- shape=2d63d991 vocab=35e9b08c
-/
theorem conditionalValueAtRisk_sum_le_of_upperTruncation_mgf
    [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (n q : ℕ) (hq : 1 ≤ q)
    (hD : ∀ i < n, Integrable (D i) mu)
    (hpow : ∀ i < n,
      Integrable (fun omega => (max (D i omega) 0) ^ q) mu)
    (psi : ℝ → ℝ)
    {y alpha t : ℝ} (hy : 0 < y)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) (ht : 0 < t)
    (hmgf : HasOneSidedMGF
      (fun omega => ∑ i ∈ Finset.range n,
        upperTruncation (D i) y omega) psi mu) :
    conditionalValueAtRisk alpha
        (fun omega => ∑ i ∈ Finset.range n, D i omega) mu ≤
      (psi t - Real.log alpha) / t +
        alpha⁻¹ *
          ((∑ i ∈ Finset.range n,
            ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
              ((q : ℝ) * y ^ (q - 1))) := by
  let U : Omega → ℝ := fun omega => ∑ i ∈ Finset.range n,
    upperTruncation (D i) y omega
  let R : Omega → ℝ := fun omega => ∑ i ∈ Finset.range n,
    upperTruncationResidual (D i) y omega
  have hUInt : Integrable U mu := by
    dsimp only [U]
    apply integrable_finsetSum
    intro i hi
    exact integrable_upperTruncation (hD i (Finset.mem_range.mp hi)) y
  have hRInt : Integrable R mu := by
    dsimp only [R]
    apply integrable_finsetSum
    intro i hi
    exact integrable_upperTruncationResidual
      (hD i (Finset.mem_range.mp hi)) y
  have hdecomp :
      (fun omega => ∑ i ∈ Finset.range n, D i omega) =
        (fun omega => U omega + R omega) := by
    funext omega
    dsimp only [U, R]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (upperTruncation_add_residual (D i) y omega).symm
  rw [hdecomp]
  calc
    conditionalValueAtRisk alpha (fun omega => U omega + R omega) mu ≤
        conditionalValueAtRisk alpha U mu +
          conditionalValueAtRisk alpha R mu :=
      conditionalValueAtRisk_add_le hUInt hRInt halpha0 halpha1
    _ ≤ (psi t - Real.log alpha) / t +
        alpha⁻¹ *
          ((∑ i ∈ Finset.range n,
            ∫ omega, (max (D i omega) 0) ^ q ∂mu) /
              ((q : ℝ) * y ^ (q - 1))) := by
      apply add_le_add
      · exact hmgf.conditionalValueAtRisk_le hUInt halpha0 halpha1 ht
      · dsimp only [R]
        exact conditionalValueAtRisk_sum_upperTruncationResidual_le
          D n q hq hD hpow hy halpha0 halpha1

/-- The complete, unoptimized strong-moment martingale CVaR bound.  The
first term is Rio's finite Taylor exponent for the upper-truncated
martingale; the second term is the exact `q`-moment cost of restoring the
discarded residuals.
@isnad1 id=le.16h12v.s9.94fca8ee6cd9 from=translated src=- shape=a98fd2e6 vocab=0c48dbbc
-/
theorem conditionalValueAtRisk_sum_le_strongMomentTaylorExponent_add_residual
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
      (strongMomentTaylorExponent q t y
          (∑ i ∈ Finset.range n, second i)
          (fun k => ∑ i ∈ Finset.range n, moment i k) -
        Real.log alpha) / t +
      alpha⁻¹ *
        ((∑ i ∈ Finset.range n, moment i q) /
          ((q : ℝ) * y ^ (q - 1))) := by
  have hqOne : 1 ≤ q := by omega
  have hqIcc : q ∈ Finset.Icc 2 q := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hpowq : ∀ i < n,
      Integrable (fun omega => (max (D i omega) 0) ^ q) mu := by
    intro i hi
    exact hpow i hi q hqIcc
  have hmgf := hasOneSidedMGF_sum_upperTruncation_of_strongMoment
    filtration D hAdapted second moment n q hn hq hy.le hD hDsq hpow
      hcenter0 hcenterSucc hsecond0 hsecondSucc hmoment0 hmomentSucc
  have hraw := conditionalValueAtRisk_sum_le_of_upperTruncation_mgf
      D n q hqOne hD hpowq
        (fun t => strongMomentTaylorExponent q t y
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
