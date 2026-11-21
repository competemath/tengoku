/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.TruncationConcentration
import Tengoku.Seed.Probability.Moments.SubGaussian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Truncation of martingale differences

This file develops the conditional truncation step needed in a direct
Fuk--Nagaev argument for a Doob martingale.  Unlike observation-level hard
truncation, truncating the martingale differences preserves the natural
`1 / n` scale of the exceptional part.

The first result is a conditional version of Hoeffding's lemma.  It is not
currently exposed by Mathlib's sub-Gaussian API: an almost surely bounded
random variable whose conditional expectation is zero is conditionally
sub-Gaussian.  The proof applies the ordinary Hoeffding lemma to the regular
conditional distributions furnished by `condExpKernel`.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} {m : MeasurableSpace Omega}
  [mOmega : MeasurableSpace Omega]
  {mu : Measure Omega}

/-- Conditional Hoeffding lemma.  If `X` lies almost surely in `[a,b]` and
has conditional expectation zero with respect to `m`, then its conditional
sub-Gaussian variance proxy is `((b-a)/2)^2`.

This is proved from the unconditional Hoeffding lemma on the fibres of the
regular conditional distribution; it is not an assumed concentration
certificate.
@isnad1 id=hasconds.4h6v.s7.d746f57646ca from=translated src=- shape=6f7e1c34 vocab=93c41974
-/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_ae_eq_zero
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) {X : Omega → ℝ} {a b : ℝ}
    (hX : AEMeasurable X mu)
    (hb : ∀ᵐ omega ∂mu, X omega ∈ Icc a b)
    (hcenter : mu[X | m] =ᵐ[mu] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) mu := by
  have hXint : Integrable X mu := Integrable.of_mem_Icc a b hX hb
  have hXkernel : ∀ᵐ omega ∂mu.trim hm,
      Integrable X (condExpKernel mu m omega) := by
    apply Measure.ae_integrable_of_integrable_comp
    rw [condExpKernel_comp_trim hm]
    exact hXint
  have hbkernel : ∀ᵐ omega ∂mu.trim hm,
      ∀ᵐ z ∂condExpKernel mu m omega, X z ∈ Icc a b := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim hm]
    exact hb
  have hcondKernel : mu[X | m] =ᵐ[mu.trim hm]
      fun omega ↦ ∫ z, X z ∂condExpKernel mu m omega :=
    condExp_ae_eq_trim_integral_condExpKernel hm hXint
  have hcenterTrim : mu[X | m] =ᵐ[mu.trim hm] 0 := by
    exact stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable
      hm stronglyMeasurable_zero hcenter
  rw [HasCondSubgaussianMGF]
  constructor
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX hb
  · filter_upwards [hXkernel, hbkernel, hcondKernel, hcenterTrim]
      with omega hXi hbi hcond hzero
    have hmean : ∫ z, X z ∂condExpKernel mu m omega = 0 := by
      rw [← hcond, hzero]
      rfl
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hXi.aemeasurable hbi hmean).mgf_le

/-! ## Conditional centring after truncation -/

/-- Truncate a random variable at level `y`, then subtract its conditional
expectation with respect to `m`.-/
def conditionallyCenteredTruncation (mu : Measure Omega)
    (m : MeasurableSpace Omega) (X : Omega → ℝ) (y : ℝ)
    (omega : Omega) : ℝ :=
  truncation X y omega -
    @condExp Omega ℝ m mOmega _ _ mu (truncation X y) omega

/--
@isnad1 id=aemeasur.2h5v.s5.38f05306e5b4 from=translated src=- shape=4844f3a4 vocab=ac736390
-/
theorem aemeasurable_conditionallyCenteredTruncation
    [IsFiniteMeasure mu] {X : Omega → ℝ} (hX : AEMeasurable X mu)
    (hm : m ≤ mOmega) (y : ℝ) :
    AEMeasurable (conditionallyCenteredTruncation mu m X y) mu := by
  unfold conditionallyCenteredTruncation
  have hCEmeas : AEMeasurable (mu[truncation X y | m]) mu :=
    (stronglyMeasurable_condExp (m := m) (μ := mu)
      (f := truncation X y)).mono hm |>.aemeasurable
  exact hX.aestronglyMeasurable.truncation.aemeasurable.sub hCEmeas

/--
@isnad1 id=integrab.1h5v.s5.0edd2bf8ae2f from=translated src=- shape=8ed93995 vocab=f803420a
-/
theorem integrable_conditionallyCenteredTruncation
    [IsFiniteMeasure mu] {X : Omega → ℝ} (hX : AEMeasurable X mu)
    (y : ℝ) :
    Integrable (conditionallyCenteredTruncation mu m X y) mu := by
  unfold conditionallyCenteredTruncation
  exact hX.aestronglyMeasurable.integrable_truncation.sub integrable_condExp

/-- Conditional centring gives a martingale difference.
@isnad1 id=eventual.2h5v.s6.022c9fe8ad9d from=translated src=- shape=21fc0b42 vocab=641b09f7
-/
theorem condExp_conditionallyCenteredTruncation_ae_eq_zero
    [IsProbabilityMeasure mu] (hm : m ≤ mOmega)
    {X : Omega → ℝ} (hX : AEMeasurable X mu) (y : ℝ) :
    mu[conditionallyCenteredTruncation mu m X y | m] =ᵐ[mu] 0 := by
  let W : Omega → ℝ := truncation X y
  have hWint : Integrable W mu :=
    hX.aestronglyMeasurable.integrable_truncation
  have hCEint : Integrable (mu[W | m]) mu := integrable_condExp
  have hsub := condExp_sub hWint hCEint m
  have htwice : mu[mu[W | m] | m] =ᵐ[mu] mu[W | m] :=
    condExp_of_aestronglyMeasurable' hm
      stronglyMeasurable_condExp.aestronglyMeasurable integrable_condExp
  change mu[W - mu[W | m] | m] =ᵐ[mu] 0
  exact hsub.trans (htwice.mono fun omega homega ↦ by simp [homega])

/-- A conditionally centred truncation lies in
`[-2|y|, 2|y|]`.
@isnad1 id=eventual.0h5v.s6.b081999e3211 from=translated src=- shape=b8137a41 vocab=a7dac6f0
-/
theorem conditionallyCenteredTruncation_mem_Icc
    [IsProbabilityMeasure mu] (X : Omega → ℝ) (y : ℝ) :
    ∀ᵐ omega ∂mu,
      conditionallyCenteredTruncation mu m X y omega ∈
        Icc (-2 * |y|) (2 * |y|) := by
  let W : Omega → ℝ := truncation X y
  have hWbound : ∀ᵐ omega ∂mu, ‖W omega‖ ≤ |y| :=
    ae_of_all mu fun omega ↦ by
      simpa only [W, Real.norm_eq_abs] using
        abs_truncation_le_bound X y omega
  have hmeanBound : ∀ᵐ omega ∂mu, ‖mu[W | m] omega‖ ≤ |y| :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hWbound
  filter_upwards [hmeanBound] with omega hmean
  have hpoint : |W omega| ≤ |y| := by
    simpa only [Real.norm_eq_abs] using
      abs_truncation_le_bound X y omega
  have hmean' : |mu[W | m] omega| ≤ |y| := by
    simpa only [Real.norm_eq_abs] using hmean
  have habs : |W omega - mu[W | m] omega| ≤ 2 * |y| := by
    calc
      |W omega - mu[W | m] omega| ≤
          |W omega| + |mu[W | m] omega| := abs_sub _ _
      _ ≤ |y| + |y| := add_le_add hpoint hmean'
      _ = 2 * |y| := by ring
  change W omega - mu[W | m] omega ∈ Icc (-2 * |y|) (2 * |y|)
  rcases abs_le.mp habs with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- A conditionally centred truncation is conditionally sub-Gaussian.  Its
proxy is `4 y²`, corresponding to an interval of width `4|y|`.
@isnad1 id=hasconds.2h5v.s7.aef723781e51 from=translated src=- shape=3547a226 vocab=524ad462
-/
theorem hasCondSubgaussianMGF_conditionallyCenteredTruncation
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (hm : m ≤ mOmega) {X : Omega → ℝ} (hX : AEMeasurable X mu)
    (y : ℝ) :
    HasCondSubgaussianMGF m hm
      (conditionallyCenteredTruncation mu m X y)
      ((‖(2 * |y|) - (-2 * |y|)‖₊ / 2) ^ 2) mu := by
  apply hasCondSubgaussianMGF_of_mem_Icc_of_condExp_ae_eq_zero hm
    (aemeasurable_conditionallyCenteredTruncation hX hm y)
    (conditionallyCenteredTruncation_mem_Icc X y)
  exact condExp_conditionallyCenteredTruncation_ae_eq_zero hm hX y

/-- Conditional truncation bias controlled by a conditional `q`-moment.
This is the conditional analogue of
`abs_integral_truncation_sub_integral_le_absoluteMoment_div`.
@isnad1 id=eventual.6h6v.s8.ec2664ad3dee from=translated src=- shape=4f6b5f89 vocab=9118dd49
-/
theorem abs_condExp_truncation_le_condExp_abs_pow_div
    [IsProbabilityMeasure mu] (_hm : m ≤ mOmega)
    {X : Omega → ℝ} (hX : AEMeasurable X mu)
    (hcenter : mu[X | m] =ᵐ[mu] 0)
    {q : ℕ} (hq : 1 ≤ q)
    (hXq : Integrable (fun omega ↦ |X omega| ^ q) mu)
    {y : ℝ} (hy : 0 < y) :
    ∀ᵐ omega ∂mu,
      |mu[truncation X y | m] omega| ≤
        mu[fun z ↦ |X z| ^ q / y ^ (q - 1) | m] omega := by
  have hXint : Integrable X mu := by
    apply (integrable_norm_iff hX.aestronglyMeasurable).1
    have hpow : Integrable (fun omega ↦ ‖X omega‖ ^ q) mu := by
      simpa only [Real.norm_eq_abs] using hXq
    simpa only [pow_one] using
      (integrable_norm_pow_of_le hX.aestronglyMeasurable hq hpow :
        Integrable (fun omega ↦ ‖X omega‖ ^ 1) mu)
  have htrunc : Integrable (truncation X y) mu :=
    hX.aestronglyMeasurable.integrable_truncation
  have herr : Integrable (fun omega ↦ truncation X y omega - X omega) mu :=
    htrunc.sub hXint
  have hbound : Integrable
      (fun omega ↦ |X omega| ^ q / y ^ (q - 1)) mu :=
    hXq.div_const (y ^ (q - 1))
  have hsub := condExp_sub htrunc hXint m
  have herrorCenter :
      mu[fun omega ↦ truncation X y omega - X omega | m] =ᵐ[mu]
        mu[truncation X y | m] :=
    hsub.trans (hcenter.mono fun omega homega ↦ by simp [homega])
  have habs := abs_condExp_ae_le_condExp_abs
    (m := m) (μ := mu) (fun omega ↦ truncation X y omega - X omega)
  have hmono := condExp_mono (m := m) herr.abs hbound
    (ae_of_all mu fun omega ↦
      abs_truncation_sub_le_abs_pow_div X hq hy omega)
  filter_upwards [herrorCenter, habs, hmono] with omega heq habs hle
  rw [← heq]
  exact habs.trans hle

/-- If the conditional `q`-moment is bounded by `K`, then the predictable
truncation centre is at most `K / y^(q-1)`.
@isnad1 id=eventual.7h7v.s8.a4f9da02369a from=translated src=- shape=9519e97e vocab=9118dd49
-/
theorem abs_condExp_truncation_le_moment_div
    [IsProbabilityMeasure mu] (hm : m ≤ mOmega)
    {X : Omega → ℝ} (hX : AEMeasurable X mu)
    (hcenter : mu[X | m] =ᵐ[mu] 0)
    {q : ℕ} (hq : 1 ≤ q)
    (hXq : Integrable (fun omega ↦ |X omega| ^ q) mu)
    {K y : ℝ} (hy : 0 < y)
    (hcondMoment : ∀ᵐ omega ∂mu,
      mu[fun z ↦ |X z| ^ q | m] omega ≤ K) :
    ∀ᵐ omega ∂mu,
      |mu[truncation X y | m] omega| ≤ K / y ^ (q - 1) := by
  have hbase := abs_condExp_truncation_le_condExp_abs_pow_div
    hm hX hcenter hq hXq hy
  have hscale := condExp_smul (𝕜 := ℝ) (μ := mu)
    ((y ^ (q - 1))⁻¹) (fun z ↦ |X z| ^ q) m
  have hinv : 0 ≤ (y ^ (q - 1))⁻¹ := (pow_pos hy _).le |> inv_nonneg.mpr
  filter_upwards [hbase, hscale, hcondMoment]
      with omega hbase hscale hmoment
  calc
    |mu[truncation X y | m] omega| ≤
        mu[fun z ↦ |X z| ^ q / y ^ (q - 1) | m] omega := hbase
    _ = (y ^ (q - 1))⁻¹ *
        mu[fun z ↦ |X z| ^ q | m] omega := by
      have hfun : (fun z ↦ |X z| ^ q / y ^ (q - 1)) =
          (y ^ (q - 1))⁻¹ • (fun z ↦ |X z| ^ q) := by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
      rw [hfun, hscale]
      rfl
    _ ≤ (y ^ (q - 1))⁻¹ * K :=
      mul_le_mul_of_nonneg_left hmoment hinv
    _ = K / y ^ (q - 1) := by rw [div_eq_inv_mul]

/-- Simplified real form of the conditional Hoeffding proxy.
@isnad1 id=eq.0h1v.s7.658283757992 from=translated src=- shape=c747b2dd vocab=163db27e
-/
theorem centeredTruncation_proxy_coe (y : ℝ) :
    (((‖(2 * |y|) - (-2 * |y|)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) =
      4 * y ^ 2 := by
  push_cast
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · ring_nf
    rw [sq_abs]
  · linarith [abs_nonneg y]

/-! ## A canonical truncated martingale-difference process -/

variable (filtration : Filtration ℕ mOmega)

/-- The first increment is centred by its ordinary expectation; every later
increment is centred conditionally on the preceding sigma-algebra.-/
def martingaleCenteredTruncation (mu : Measure Omega)
    (D : ℕ → Omega → ℝ) (y : ℝ) : ℕ → Omega → ℝ
  | 0 => centeredTruncation (D 0) y mu
  | k + 1 => conditionallyCenteredTruncation mu (filtration k) (D (k + 1)) y

/-- The predictable centre removed in `martingaleCenteredTruncation`.-/
def martingaleTruncationCenter (mu : Measure Omega)
    (D : ℕ → Omega → ℝ) (y : ℝ) : ℕ → Omega → ℝ
  | 0 => fun _ ↦ ∫ z, truncation (D 0) y z ∂mu
  | k + 1 => mu[truncation (D (k + 1)) y | filtration k]

/-- Before truncation occurs, one increment is exactly the sum of its
conditionally centred truncation and its predictable centre.
@isnad1 id=eq.1h7v.s6.83178497baa1 from=translated src=- shape=de34a38a vocab=3f06619e
-/
theorem martingaleCenteredTruncation_add_center_eq
    (mu : Measure Omega) (D : ℕ → Omega → ℝ) (y : ℝ)
    (k : ℕ) (omega : Omega) (hsmall : |D k omega| < y) :
    martingaleCenteredTruncation filtration mu D y k omega +
        martingaleTruncationCenter filtration mu D y k omega =
      D k omega := by
  cases k with
  | zero =>
      simp only [martingaleCenteredTruncation, martingaleTruncationCenter,
        centeredTruncation]
      rw [truncation_eq_self hsmall]
      ring
  | succ k =>
      simp only [martingaleCenteredTruncation, martingaleTruncationCenter,
        conditionallyCenteredTruncation]
      rw [truncation_eq_self hsmall]
      ring

/-- Sum form of the preceding exact identity.
@isnad1 id=eq.1h7v.s6.5c310679acd0 from=translated src=- shape=3aecdf7b vocab=cd18aa44
-/
theorem sum_martingaleCenteredTruncation_add_center_eq
    (mu : Measure Omega) (D : ℕ → Omega → ℝ) (y : ℝ)
    (n : ℕ) (omega : Omega)
    (hsmall : ∀ k < n, |D k omega| < y) :
    (∑ k ∈ range n,
        martingaleCenteredTruncation filtration mu D y k omega) +
      (∑ k ∈ range n,
        martingaleTruncationCenter filtration mu D y k omega) =
      ∑ k ∈ range n, D k omega := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  exact martingaleCenteredTruncation_add_center_eq filtration mu D y k omega
    (hsmall k (mem_range.mp hk))

/-- Strong measurability is preserved by the hard truncation used here.
@isnad1 id=strongly.1h4v.s5.973ba28d7309 from=translated src=- shape=7308114e vocab=b80380a0
-/
theorem StronglyMeasurable.truncation
    {m' : MeasurableSpace Omega} {X : Omega → ℝ}
    (hX : StronglyMeasurable[m'] X) (y : ℝ) :
    StronglyMeasurable[m'] (ProbabilityTheory.truncation X y) := by
  unfold ProbabilityTheory.truncation
  exact (stronglyMeasurable_id.indicator measurableSet_Ioc).comp_measurable
    hX.measurable

/-- Conditional centring preserves adaptation: the centre at time `k+1` is
measurable already at time `k`.
@isnad1 id=strongly.1h5v.s6.99604c04a569 from=translated src=- shape=53b327f9 vocab=025bacac
-/
theorem stronglyAdapted_martingaleCenteredTruncation
    [IsFiniteMeasure mu] (D : ℕ → Omega → ℝ) (y : ℝ)
    (hD : StronglyAdapted filtration D) :
    StronglyAdapted filtration
      (martingaleCenteredTruncation filtration mu D y) := by
  intro k
  cases k with
  | zero =>
      change StronglyMeasurable[filtration 0]
        (fun omega ↦ truncation (D 0) y omega -
          ∫ z, truncation (D 0) y z ∂mu)
      exact (StronglyMeasurable.truncation (hD 0) y).sub
        stronglyMeasurable_const
  | succ k =>
      change StronglyMeasurable[filtration (k + 1)]
        (fun omega ↦ truncation (D (k + 1)) y omega -
          mu[truncation (D (k + 1)) y | filtration k] omega)
      exact (StronglyMeasurable.truncation (hD (k + 1)) y).sub
        (stronglyMeasurable_condExp.mono
          (filtration.mono (Nat.le_succ k)))

/-- The first truncated difference is sub-Gaussian with the same coarse
proxy as all subsequent conditionally centred differences.
@isnad1 id=hassubga.1h5v.s7.1b2c84879c0a from=translated src=- shape=b17498f8 vocab=769065f4
-/
theorem hasSubgaussianMGF_martingaleCenteredTruncation_zero
    [IsProbabilityMeasure mu] (D : ℕ → Omega → ℝ)
    (hD0 : AEMeasurable (D 0) mu) (y : ℝ) :
    HasSubgaussianMGF
      (martingaleCenteredTruncation filtration mu D y 0)
      ((‖(2 * |y|) - (-2 * |y|)‖₊ / 2) ^ 2) mu := by
  change HasSubgaussianMGF (centeredTruncation (D 0) y mu)
    ((‖(2 * |y|) - (-2 * |y|)‖₊ / 2) ^ 2) mu
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (aemeasurable_centeredTruncation hD0 y)
  · exact ae_of_all mu fun omega ↦ centeredTruncation_mem_Icc (D 0) y omega
  · exact integral_centeredTruncation hD0 y

/-- Every later truncated difference is sub-Gaussian conditionally on the
preceding filtration level.
@isnad1 id=hasconds.1h6v.s7.27c1022a4d97 from=translated src=- shape=7f519e04 vocab=9ee069dc
-/
theorem hasCondSubgaussianMGF_martingaleCenteredTruncation_succ
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hD : StronglyAdapted filtration D)
    (y : ℝ) (k : ℕ) :
    HasCondSubgaussianMGF (filtration k) (filtration.le k)
      (martingaleCenteredTruncation filtration mu D y (k + 1))
      ((‖(2 * |y|) - (-2 * |y|)‖₊ / 2) ^ 2) mu := by
  change HasCondSubgaussianMGF (filtration k) (filtration.le k)
    (conditionallyCenteredTruncation mu (filtration k) (D (k + 1)) y)
    ((‖(2 * |y|) - (-2 * |y|)‖₊ / 2) ^ 2) mu
  apply hasCondSubgaussianMGF_conditionallyCenteredTruncation
    (filtration.le k)
  exact ((hD (k + 1)).mono (filtration.le (k + 1))).aemeasurable

/-- Azuma--Hoeffding for the canonically truncated martingale differences.
The explicit denominator `8 n y²` records the factor-four loss caused by
conditional recentering.
@isnad1 id=le.2h7v.s7.40c9a154e729 from=translated src=- shape=6a7b8982 vocab=8ae5121e
-/
theorem measureReal_sum_martingaleCenteredTruncation_ge_le
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hD : StronglyAdapted filtration D)
    (y : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | t ≤
        ∑ k ∈ range n,
          martingaleCenteredTruncation filtration mu D y k omega} ≤
      exp (-t ^ 2 / (8 * (n : ℝ) * y ^ 2)) := by
  let c : ℝ≥0 := (‖(2 * |y|) - (-2 * |y|)‖₊ / 2) ^ 2
  let Y : ℕ → Omega → ℝ :=
    martingaleCenteredTruncation filtration mu D y
  have hYadapted : StronglyAdapted filtration Y :=
    stronglyAdapted_martingaleCenteredTruncation filtration D y hD
  have hYzero : HasSubgaussianMGF (Y 0) c mu := by
    exact hasSubgaussianMGF_martingaleCenteredTruncation_zero
      filtration D ((hD 0).mono (filtration.le 0) |>.aemeasurable) y
  have hYsucc : ∀ i < n - 1,
      HasCondSubgaussianMGF (filtration i) (filtration.le i)
        (Y (i + 1)) c mu := by
    intro i _hi
    exact hasCondSubgaussianMGF_martingaleCenteredTruncation_succ
      filtration D hD y i
  have htail := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (Y := Y) (cY := fun _ ↦ c) (ℱ := filtration) (μ := mu)
    hYadapted hYzero n hYsucc ht
  change mu.real {omega | t ≤ ∑ k ∈ range n, Y k omega} ≤ _
  rw [show (8 : ℝ) * n * y ^ 2 =
      2 * ∑ _k ∈ range n, (c : ℝ) by
    simp only [sum_const, card_range, nsmul_eq_mul, c,
      centeredTruncation_proxy_coe]
    ring]
  simpa only [NNReal.coe_sum] using htail

/-! ## Fuk--Nagaev event reduction for martingale differences -/

/-- A large martingale sum forces either a large raw difference or a large
sum of the conditionally centred truncations.  The predictable truncation
centre remains visible in the threshold; bounding it is the next, genuinely
moment-sensitive, step of the argument.
@isnad1 id=le.0h7v.s7.ca41bab3d0a6 from=translated src=- shape=876762b2 vocab=1aedc7b2
-/
theorem martingale_sum_large_subset_iUnion_large_or_truncation
    (mu : Measure Omega) (D : ℕ → Omega → ℝ)
    (y t : ℝ) (n : ℕ) :
    {omega | t +
        |∑ k ∈ range n,
          martingaleTruncationCenter filtration mu D y k omega| ≤
        ∑ k ∈ range n, D k omega} ⊆
      (⋃ k ∈ range n, {omega | y ≤ |D k omega|}) ∪
        {omega | t ≤
          ∑ k ∈ range n,
            martingaleCenteredTruncation filtration mu D y k omega} := by
  intro omega homega
  by_cases hlarge : ∃ k < n, y ≤ |D k omega|
  · left
    obtain ⟨k, hk, hky⟩ := hlarge
    exact Set.mem_iUnion.2 ⟨k,
      Set.mem_iUnion.2 ⟨mem_range.mpr hk, hky⟩⟩
  · right
    have hsmall : ∀ k < n, |D k omega| < y := by
      intro k hk
      exact lt_of_not_ge fun hky ↦ hlarge ⟨k, hk, hky⟩
    have hid := sum_martingaleCenteredTruncation_add_center_eq
      filtration mu D y n omega hsmall
    let S : ℝ := ∑ k ∈ range n,
      martingaleCenteredTruncation filtration mu D y k omega
    let C : ℝ := ∑ k ∈ range n,
      martingaleTruncationCenter filtration mu D y k omega
    change t ≤ S
    change t + |C| ≤ ∑ k ∈ range n, D k omega at homega
    change S + C = ∑ k ∈ range n, D k omega at hid
    rw [← hid] at homega
    linarith [le_abs_self C]

/-- Probability form of the martingale truncation reduction.
@isnad1 id=le.0h7v.s7.03493543fd56 from=translated src=- shape=24e7a993 vocab=700cf536
-/
theorem measureReal_martingale_sum_large_le_sum_large_add_truncation
    [IsFiniteMeasure mu] (D : ℕ → Omega → ℝ)
    (y t : ℝ) (n : ℕ) :
    mu.real {omega | t +
        |∑ k ∈ range n,
          martingaleTruncationCenter filtration mu D y k omega| ≤
        ∑ k ∈ range n, D k omega} ≤
      (∑ k ∈ range n, mu.real {omega | y ≤ |D k omega|}) +
        mu.real {omega | t ≤
          ∑ k ∈ range n,
            martingaleCenteredTruncation filtration mu D y k omega} := by
  let U : Set Omega := ⋃ k ∈ range n, {omega | y ≤ |D k omega|}
  let T : Set Omega := {omega | t ≤
    ∑ k ∈ range n,
      martingaleCenteredTruncation filtration mu D y k omega}
  calc
    mu.real {omega | t +
        |∑ k ∈ range n,
          martingaleTruncationCenter filtration mu D y k omega| ≤
        ∑ k ∈ range n, D k omega} ≤ mu.real (U ∪ T) :=
      measureReal_mono
        (martingale_sum_large_subset_iUnion_large_or_truncation
          filtration mu D y t n)
    _ ≤ mu.real U + mu.real T := measureReal_union_le _ _
    _ ≤ (∑ k ∈ range n, mu.real {omega | y ≤ |D k omega|}) +
        mu.real T := by
      apply add_le_add
      · simpa only [U] using measureReal_biUnion_finset_le (range n)
          (fun k ↦ {omega | y ≤ |D k omega|})
      · exact le_rfl
    _ = (∑ k ∈ range n, mu.real {omega | y ≤ |D k omega|}) +
        mu.real {omega | t ≤
          ∑ k ∈ range n,
            martingaleCenteredTruncation filtration mu D y k omega} := rfl

/-- A fully proved martingale Fuk--Nagaev reduction obtained by combining
conditional truncation, Azuma--Hoeffding, and one scalar Markov bound per
difference.  No maximal-tail conclusion is assumed.

The Gaussian denominator still contains `y²`; this is the explicit loss of
the elementary Azuma route compared with Rio's variance-sensitive theorem.
The random predictable centre is also retained in the deviation threshold.
@isnad1 id=le.4h8v.s8.c85c6db20185 from=translated src=- shape=56dde32b vocab=ca888189
-/
theorem measureReal_martingale_sum_large_le_moment_div_add_exp
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hD : StronglyAdapted filtration D)
    {q : ℕ}
    (hDq : ∀ k < n, Integrable (fun omega ↦ |D k omega| ^ q) mu)
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    mu.real {omega | t +
        |∑ k ∈ range n,
          martingaleTruncationCenter filtration mu D y k omega| ≤
        ∑ k ∈ range n, D k omega} ≤
      (∑ k ∈ range n, absoluteMoment (D k) q mu) / y ^ q +
        exp (-t ^ 2 / (8 * (n : ℝ) * y ^ 2)) := by
  have hdecomp :=
    measureReal_martingale_sum_large_le_sum_large_add_truncation
      (mu := mu) filtration D y t n
  have htrunc := measureReal_sum_martingaleCenteredTruncation_ge_le
    (mu := mu) filtration D hD y n ht
  calc
    mu.real {omega | t +
        |∑ k ∈ range n,
          martingaleTruncationCenter filtration mu D y k omega| ≤
        ∑ k ∈ range n, D k omega} ≤
      (∑ k ∈ range n, mu.real {omega | y ≤ |D k omega|}) +
        mu.real {omega | t ≤
          ∑ k ∈ range n,
            martingaleCenteredTruncation filtration mu D y k omega} := hdecomp
    _ ≤ (∑ k ∈ range n, absoluteMoment (D k) q mu / y ^ q) +
        exp (-t ^ 2 / (8 * (n : ℝ) * y ^ 2)) := by
      apply add_le_add
      · gcongr with k hk
        exact measureReal_abs_ge_le_absoluteMoment_div
          (D k) q (hDq k (mem_range.mp hk)) hy
      · exact htrunc
    _ = (∑ k ∈ range n, absoluteMoment (D k) q mu) / y ^ q +
        exp (-t ^ 2 / (8 * (n : ℝ) * y ^ 2)) := by
      rw [sum_div]

/-- Conditional `q`-moment bounds control the full predictable centre created
by truncating a finite sequence of martingale differences.
@isnad1 id=eventual.8h8v.s8.d9f19d455737 from=translated src=- shape=0a7b395c vocab=4b79e467
-/
theorem abs_sum_martingaleTruncationCenter_le_moment_div
    [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hD : StronglyAdapted filtration D)
    {q : ℕ} (hq : 1 ≤ q)
    (hDq : ∀ k < n, Integrable (fun omega ↦ |D k omega| ^ q) mu)
    (hcenter0 : ∫ omega, D 0 omega ∂mu = 0)
    (hcenterSucc : ∀ k < n - 1,
      mu[D (k + 1) | filtration k] =ᵐ[mu] 0)
    (K : ℕ → ℝ)
    (hmoment0 : absoluteMoment (D 0) q mu ≤ K 0)
    (hcondMoment : ∀ k < n - 1, ∀ᵐ omega ∂mu,
      mu[fun z ↦ |D (k + 1) z| ^ q | filtration k] omega ≤ K (k + 1))
    {y : ℝ} (hy : 0 < y) :
    ∀ᵐ omega ∂mu,
      |∑ k ∈ range n,
          martingaleTruncationCenter filtration mu D y k omega| ≤
        (∑ k ∈ range n, K k) / y ^ (q - 1) := by
  have hDmeas : ∀ k, AEMeasurable (D k) mu := fun k ↦
    ((hD k).mono (filtration.le k)).aemeasurable
  have hcenterEach : ∀ k < n, ∀ᵐ omega ∂mu,
      |martingaleTruncationCenter filtration mu D y k omega| ≤
        K k / y ^ (q - 1) := by
    intro k hk
    cases k with
    | zero =>
        have hbias :=
          abs_integral_truncation_sub_integral_le_absoluteMoment_div
            (hDmeas 0) hq (hDq 0 hk) hy
        exact ae_of_all mu fun omega ↦ by
          change |∫ z, truncation (D 0) y z ∂mu| ≤ K 0 / y ^ (q - 1)
          calc
            |∫ z, truncation (D 0) y z ∂mu| =
                |(∫ z, truncation (D 0) y z ∂mu) -
                  ∫ z, D 0 z ∂mu| := by rw [hcenter0, sub_zero]
            _ ≤ absoluteMoment (D 0) q mu / y ^ (q - 1) := hbias
            _ ≤ K 0 / y ^ (q - 1) := by
              exact div_le_div_of_nonneg_right hmoment0
                (pow_nonneg hy.le (q - 1))
    | succ k =>
        have hk' : k < n - 1 := by omega
        change ∀ᵐ omega ∂mu,
          |mu[truncation (D (k + 1)) y | filtration k] omega| ≤
            K (k + 1) / y ^ (q - 1)
        exact abs_condExp_truncation_le_moment_div
          (filtration.le k) (hDmeas (k + 1)) (hcenterSucc k hk')
          hq (hDq (k + 1) hk) hy (hcondMoment k hk')
  have hcenterAll : ∀ᵐ omega ∂mu, ∀ k, k < n →
      |martingaleTruncationCenter filtration mu D y k omega| ≤
        K k / y ^ (q - 1) := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k < n
    · exact (hcenterEach k hk).mono fun omega homega _ ↦ homega
    · exact ae_of_all mu fun _ hk' ↦ (hk hk').elim
  filter_upwards [hcenterAll] with omega hall
  calc
    |∑ k ∈ range n,
        martingaleTruncationCenter filtration mu D y k omega| ≤
        ∑ k ∈ range n,
          |martingaleTruncationCenter filtration mu D y k omega| :=
      Finset.abs_sum_le_sum_abs _ (range n)
    _ ≤ ∑ k ∈ range n, K k / y ^ (q - 1) := by
      gcongr with k hk
      exact hall k (mem_range.mp hk)
    _ = (∑ k ∈ range n, K k) / y ^ (q - 1) := by rw [sum_div]

/-- **Explicit martingale truncation inequality.**  Conditional moment
bounds eliminate the random predictable centre from the preceding
Fuk--Nagaev reduction.

This theorem is unconditional in the relevant sense: its hypotheses are
adaptation, martingale centring, measurability, and moment bounds, rather
than a pre-packaged concentration certificate.  Its exponential term is
Azuma's `exp (-t² / (8 n y²))`; replacing that denominator by the quadratic
variation is precisely the stronger Rio step still needed for Marchina's
optimal Gaussian-plus-polynomial rate.
@isnad1 id=le.9h9v.s9.bfc9967ca5e5 from=translated src=- shape=c4d1c8a5 vocab=c4a0d1f4
-/
theorem measureReal_martingale_sum_large_le_condMoment_bias_add_exp
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    (D : ℕ → Omega → ℝ) (hD : StronglyAdapted filtration D)
    {q : ℕ} (hq : 1 ≤ q)
    (hDq : ∀ k < n, Integrable (fun omega ↦ |D k omega| ^ q) mu)
    (hcenter0 : ∫ omega, D 0 omega ∂mu = 0)
    (hcenterSucc : ∀ k < n - 1,
      mu[D (k + 1) | filtration k] =ᵐ[mu] 0)
    (K : ℕ → ℝ)
    (hmoment0 : absoluteMoment (D 0) q mu ≤ K 0)
    (hcondMoment : ∀ k < n - 1, ∀ᵐ omega ∂mu,
      mu[fun z ↦ |D (k + 1) z| ^ q | filtration k] omega ≤ K (k + 1))
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    mu.real {omega |
        t + (∑ k ∈ range n, K k) / y ^ (q - 1) ≤
          ∑ k ∈ range n, D k omega} ≤
      (∑ k ∈ range n, absoluteMoment (D k) q mu) / y ^ q +
        exp (-t ^ 2 / (8 * (n : ℝ) * y ^ 2)) := by
  let B : ℝ := (∑ k ∈ range n, K k) / y ^ (q - 1)
  let C : Omega → ℝ := fun omega ↦
    ∑ k ∈ range n,
      martingaleTruncationCenter filtration mu D y k omega
  have hcenterBound : ∀ᵐ omega ∂mu, |C omega| ≤ B := by
    simpa only [B, C] using
      abs_sum_martingaleTruncationCenter_le_moment_div
        filtration D hD hq hDq hcenter0 hcenterSucc K hmoment0
          hcondMoment hy
  have hmono :
      mu.real {omega | t + B ≤ ∑ k ∈ range n, D k omega} ≤
        mu.real {omega | t + |C omega| ≤
          ∑ k ∈ range n, D k omega} := by
    rw [measureReal_def, measureReal_def]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hcenterBound] with omega hcenter
    intro homega
    change t + B ≤ ∑ k ∈ range n, D k omega at homega
    change t + |C omega| ≤ ∑ k ∈ range n, D k omega
    linarith
  have hbase := measureReal_martingale_sum_large_le_moment_div_add_exp
    (mu := mu) filtration D hD hDq hy ht
  change mu.real {omega | t + B ≤ ∑ k ∈ range n, D k omega} ≤ _
  exact hmono.trans (by simpa only [C] using hbase)

/-! ## Canonical Doob differences -/

/-- Differences of the Doob martingale of an integrable terminal random
variable, with the initial value centred by the ordinary expectation.-/
def doobCenteredDifference (mu : Measure Omega) (F : Omega → ℝ) :
    ℕ → Omega → ℝ
  | 0 => fun omega ↦ mu[F | filtration 0] omega - ∫ z, F z ∂mu
  | k + 1 => fun omega ↦
      mu[F | filtration (k + 1)] omega - mu[F | filtration k] omega

/-- The Doob differences telescope exactly to the current conditional
expectation minus the terminal expectation.
@isnad1 id=eq.0h6v.s6.05c88fd572d3 from=translated src=- shape=abdc2a5b vocab=b2625192
-/
theorem sum_doobCenteredDifference
    (mu : Measure Omega) (F : Omega → ℝ) (n : ℕ) (omega : Omega) :
    ∑ k ∈ range (n + 1), doobCenteredDifference filtration mu F k omega =
      mu[F | filtration n] omega - ∫ z, F z ∂mu := by
  induction n with
  | zero => simp [doobCenteredDifference]
  | succ n ih =>
      rw [sum_range_succ]
      rw [ih]
      simp only [doobCenteredDifference]
      ring

/-- The canonical Doob differences are adapted.
@isnad1 id=strongly.0h4v.s5.1034d76863d7 from=translated src=- shape=e9a96910 vocab=95095079
-/
theorem stronglyAdapted_doobCenteredDifference
    (mu : Measure Omega) (F : Omega → ℝ) :
    StronglyAdapted filtration (doobCenteredDifference filtration mu F) := by
  intro k
  cases k with
  | zero =>
      change StronglyMeasurable[filtration 0]
        (fun omega ↦ mu[F | filtration 0] omega - ∫ z, F z ∂mu)
      exact stronglyMeasurable_condExp.sub stronglyMeasurable_const
  | succ k =>
      change StronglyMeasurable[filtration (k + 1)]
        (fun omega ↦ mu[F | filtration (k + 1)] omega -
          mu[F | filtration k] omega)
      exact stronglyMeasurable_condExp.sub
        (stronglyMeasurable_condExp.mono
          (filtration.mono (Nat.le_succ k)))

/-- The initial Doob difference has ordinary expectation zero.
@isnad1 id=eq.0h4v.s6.c0a223060201 from=translated src=- shape=8d5c1842 vocab=0faf5568
-/
theorem integral_doobCenteredDifference_zero
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu filtration]
    (F : Omega → ℝ) :
    ∫ omega, doobCenteredDifference filtration mu F 0 omega ∂mu = 0 := by
  change ∫ omega,
    (mu[F | filtration 0] omega - ∫ z, F z ∂mu) ∂mu = 0
  rw [integral_sub integrable_condExp (integrable_const _),
    integral_condExp (filtration.le 0)]
  simp

/-- Every later Doob difference has conditional expectation zero.
@isnad1 id=eventual.0h5v.s6.e5bcaee00f82 from=translated src=- shape=e347516a vocab=25a06769
-/
theorem condExp_doobCenteredDifference_succ_ae_eq_zero
    [IsFiniteMeasure mu] [SigmaFiniteFiltration mu filtration]
    (F : Omega → ℝ) (k : ℕ) :
    mu[doobCenteredDifference filtration mu F (k + 1) | filtration k]
      =ᵐ[mu] 0 := by
  let M : ℕ → Omega → ℝ := fun j ↦ mu[F | filtration j]
  have hM : Martingale M filtration mu := martingale_condExp F filtration mu
  have hsub := condExp_sub (hM.integrable (k + 1)) (hM.integrable k)
    (filtration k)
  have hnext : mu[M (k + 1) | filtration k] =ᵐ[mu] M k :=
    hM.condExp_ae_eq (Nat.le_succ k)
  have hself : mu[M k | filtration k] =ᵐ[mu] M k :=
    hM.condExp_ae_eq le_rfl
  have hdiff :
      mu[M (k + 1) | filtration k] - mu[M k | filtration k] =ᵐ[mu] 0 := by
    filter_upwards [hnext, hself] with omega hnext hself
    simp [hnext, hself]
  change mu[M (k + 1) - M k | filtration k] =ᵐ[mu] 0
  exact hsub.trans hdiff

/-! ## Finite-supremum replace-one estimates -/

variable {T : Type*}

/-- Pointwise supremum of a process over a nonempty finite class.-/
def finiteProcessSupremum (s : Finset T) (hs : s.Nonempty)
    (X : T → Omega → ℝ) (omega : Omega) : ℝ :=
  s.sup' hs (fun t ↦ X t omega)

/-- A finite supremum of measurable coordinates is measurable.
@isnad1 id=measurab.2h4v.s5.57d900296728 from=translated src=- shape=59c2ed99 vocab=2a3df695
-/
theorem measurable_finiteProcessSupremum
    (s : Finset T) (hs : s.Nonempty) (X : T → Omega → ℝ)
    (hX : ∀ t ∈ s, Measurable (X t)) :
    Measurable (finiteProcessSupremum s hs X) := by
  have heq : finiteProcessSupremum s hs X = s.sup' hs X := by
    funext omega
    exact (Finset.sup'_apply hs X omega).symm
  rw [heq]
  exact Finset.measurable_sup' hs hX

/-- A common absolute envelope also dominates the absolute value of the
finite supremum.
@isnad1 id=le.2h6v.s6.66246b3fe050 from=translated src=- shape=695a7255 vocab=7588d28b
-/
theorem abs_finiteProcessSupremum_le
    (s : Finset T) (hs : s.Nonempty) (X : T → Omega → ℝ)
    (A : Omega → ℝ)
    (hdom : ∀ omega t, t ∈ s → |X t omega| ≤ |A omega|)
    (omega : Omega) :
    |finiteProcessSupremum s hs X omega| ≤ |A omega| := by
  have hupper : finiteProcessSupremum s hs X omega ≤ |A omega| := by
    apply Finset.sup'_le hs
    intro t ht
    exact (le_abs_self (X t omega)).trans (hdom omega t ht)
  let t : T := hs.choose
  have ht : t ∈ s := hs.choose_spec
  have hlower : -|A omega| ≤ finiteProcessSupremum s hs X omega := by
    exact (neg_le_of_abs_le (hdom omega t ht)).trans
      (Finset.le_sup' (fun u ↦ X u omega) ht)
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Integrability of a common envelope implies integrability of the finite
process supremum, so its Doob martingale is available without any additional
maximal-integrability assumption.
@isnad1 id=integrab.4h6v.s7.ab0c7fc6456f from=translated src=- shape=6b7c9808 vocab=ccf4bc32
-/
theorem integrable_finiteProcessSupremum
    (s : Finset T) (hs : s.Nonempty) (X : T → Omega → ℝ)
    (A : Omega → ℝ) (hA : Integrable A mu)
    (hX : ∀ t ∈ s, Measurable (X t))
    (hdom : ∀ omega t, t ∈ s → |X t omega| ≤ |A omega|) :
    Integrable (finiteProcessSupremum s hs X) mu := by
  apply hA.norm.mono'
    (measurable_finiteProcessSupremum s hs X hX).aestronglyMeasurable
  exact ae_of_all mu fun omega ↦ by
    simpa only [Real.norm_eq_abs] using
      abs_finiteProcessSupremum_le s hs X A hdom omega

/-- A finite maximum changes by at most the largest coordinatewise absolute
change.  This avoids choosing a measurable argmax and is the deterministic
replace-one estimate behind the Doob increment bounds for empirical
suprema.
@isnad1 id=le.1h4v.s6.9d5f4f44817c from=translated src=- shape=c4032136 vocab=bdc78d94
-/
theorem abs_finset_sup'_sub_sup'_le_sup'_abs_sub
    (s : Finset T) (hs : s.Nonempty) (f g : T → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤
      s.sup' hs (fun t ↦ |f t - g t|) := by
  obtain ⟨tf, htf, htfmax⟩ := s.exists_mem_eq_sup' hs f
  obtain ⟨tg, htg, htgmax⟩ := s.exists_mem_eq_sup' hs g
  have hforward : s.sup' hs f - s.sup' hs g ≤
      s.sup' hs (fun t ↦ |f t - g t|) := by
    calc
      s.sup' hs f - s.sup' hs g = f tf - s.sup' hs g := by rw [htfmax]
      _ ≤ f tf - g tf := sub_le_sub_left (s.le_sup' g htf) _
      _ ≤ |f tf - g tf| := le_abs_self _
      _ ≤ s.sup' hs (fun t ↦ |f t - g t|) :=
        Finset.le_sup' (fun t : T ↦ |f t - g t|) htf
  have hbackward : -(s.sup' hs (fun t ↦ |f t - g t|)) ≤
      s.sup' hs f - s.sup' hs g := by
    have hreverse : s.sup' hs g - s.sup' hs f ≤
        s.sup' hs (fun t ↦ |f t - g t|) := by
      calc
        s.sup' hs g - s.sup' hs f = g tg - s.sup' hs f := by rw [htgmax]
        _ ≤ g tg - f tg := sub_le_sub_left (s.le_sup' f htg) _
        _ ≤ |f tg - g tg| := by rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ s.sup' hs (fun t ↦ |f t - g t|) :=
          Finset.le_sup' (fun t : T ↦ |f t - g t|) htg
    linarith
  exact abs_le.mpr ⟨hbackward, hforward⟩

/-- Replacing one observation in a finite empirical supremum costs at most
the largest coordinatewise change of that observation.
@isnad1 id=le.1h5v.s6.9c957f678abb from=translated src=- shape=45949576 vocab=760e8d3c
-/
theorem abs_finset_sup'_sum_replace_one_le
    (s : Finset T) (hs : s.Nonempty)
    (r : T → ℝ) (X X' : T → ℝ) :
    |s.sup' hs (fun t ↦ r t + X t) -
        s.sup' hs (fun t ↦ r t + X' t)| ≤
      s.sup' hs (fun t ↦ |X t - X' t|) := by
  simpa only [add_sub_add_left_eq_sub] using
    abs_finset_sup'_sub_sup'_le_sup'_abs_sub s hs
      (fun t ↦ r t + X t) (fun t ↦ r t + X' t)

/-- Envelope form of the replace-one estimate.  If the old and replacement
observations have scalar envelopes `A` and `A'`, the finite supremum changes
by at most `A + A'`.
@isnad1 id=le.3h7v.s7.e8079231089e from=translated src=- shape=fc9a3f1b vocab=a43b6b0d
-/
theorem abs_finset_sup'_sum_replace_one_le_add_envelopes
    (s : Finset T) (hs : s.Nonempty)
    (r : T → ℝ) (X X' : T → ℝ) {A A' : ℝ}
    (hX : ∀ t ∈ s, |X t| ≤ A)
    (hX' : ∀ t ∈ s, |X' t| ≤ A') :
    |s.sup' hs (fun t ↦ r t + X t) -
        s.sup' hs (fun t ↦ r t + X' t)| ≤ A + A' := by
  refine (abs_finset_sup'_sum_replace_one_le s hs r X X').trans ?_
  apply Finset.sup'_le hs
  intro t ht
  exact (abs_sub (X t) (X' t)).trans (add_le_add (hX t ht) (hX' t ht))

end ProbabilityTheory
