/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.MomentConcentration
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.CompareExp
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Envelopes of centred real processes

This file records the elementary envelope estimates which precede any
maximal Fuk--Nagaev inequality.  If a real process `X omega t` is dominated
by a scalar envelope `A omega`, then its centred version is dominated,
simultaneously in `t`, by

`|A omega| + integral |A|`.

On a probability space the latter envelope has `L^q` norm at most twice the
`L^q` norm of `A`.  In particular, the centred empirical process occurring
in Marchina's theorem has strong envelope norm at most `2 Kq` and wimpy
standard deviation at most `2 K2` when the raw envelope norms are bounded by
`Kq` and `K2`.

These estimates are genuine consequences of the moment assumptions.  They
do **not** include the maximal concentration step: Marchina's proof of that
step additionally uses a Doob-martingale decomposition, CVaR subadditivity,
convex-order comparison with extremal variables, and Rio's martingale
Fuk--Nagaev inequality.  None of those results currently exists in Mathlib.
-/

open Real Set MeasureTheory
open scoped ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Coordinatewise centring of a real process.-/
def centeredProcess (X : Omega → T → ℝ) (mu : Measure Omega)
    (omega : Omega) (t : T) : ℝ :=
  X omega t - ∫ z, X z t ∂mu

/-- The canonical scalar envelope after coordinatewise centring.-/
def centeredProcessEnvelope (A : Omega → ℝ) (mu : Measure Omega)
    (omega : Omega) : ℝ :=
  |A omega| + ∫ z, |A z| ∂mu

/--
@isnad1 id=le.0h4v.s4.1b1f4ef927a8 from=translated src=- shape=99fc114c vocab=ca2ef416
-/
theorem centeredProcessEnvelope_nonneg
    (A : Omega → ℝ) (mu : Measure Omega) (omega : Omega) :
    0 ≤ centeredProcessEnvelope A mu omega := by
  unfold centeredProcessEnvelope
  exact add_nonneg (abs_nonneg _) (integral_nonneg fun _ ↦ abs_nonneg _)

/-- A raw envelope dominates every centred coordinate after adding its mean
absolute size.  The conclusion is pointwise and uniform in the index.
@isnad1 id=le.3h7v.s6.d21f62208905 from=translated src=- shape=0546fda0 vocab=4e11040b
-/
theorem abs_centeredProcess_le_centeredProcessEnvelope
    (X : Omega → T → ℝ) (A : Omega → ℝ)
    (hA : Integrable A mu)
    (hX : ∀ t, AEMeasurable (fun omega ↦ X omega t) mu)
    (hdom : ∀ omega t, |X omega t| ≤ |A omega|)
    (omega : Omega) (t : T) :
    |centeredProcess X mu omega t| ≤ centeredProcessEnvelope A mu omega := by
  have hXt : Integrable (fun z ↦ X z t) mu := by
    apply hA.norm.mono' (hX t).aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_eq_abs] using hdom z t
  have hmean : |∫ z, X z t ∂mu| ≤ ∫ z, |A z| ∂mu := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le (f := fun z ↦ X z t) hA.norm
        (ae_of_all mu fun z ↦ by
          simpa only [Real.norm_eq_abs] using hdom z t))
  calc
    |centeredProcess X mu omega t| =
        |X omega t - ∫ z, X z t ∂mu| := rfl
    _ ≤ |X omega t| + |∫ z, X z t ∂mu| := abs_sub _ _
    _ ≤ |A omega| + ∫ z, |A z| ∂mu := add_le_add (hdom omega t) hmean
    _ = centeredProcessEnvelope A mu omega := rfl

/-- On a probability space, the `L^1` norm is bounded by every `L^q` norm
with `q ≥ 1`.  This real-valued wrapper avoids exposing `ENNReal.toReal` in
applications.
@isnad1 id=le.2h4v.s6.aa62bcc0ee28 from=translated src=- shape=1b5087ee vocab=a186ac7e
-/
theorem lpNorm_one_le_lpNorm_nat
    [IsProbabilityMeasure mu]
    (A : Omega → ℝ) {q : ℕ} (hq : 1 ≤ q)
    (hAq : MemLp A q mu) :
    lpNorm A 1 mu ≤ lpNorm A q mu := by
  have hpq : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast hq
  have hle : eLpNorm A 1 mu ≤ eLpNorm A q mu :=
    eLpNorm_le_eLpNorm_of_exponent_le hpq hAq.aestronglyMeasurable
  have hreal := ENNReal.toReal_mono hAq.eLpNorm_ne_top hle
  simpa only [toReal_eLpNorm hAq.aestronglyMeasurable] using hreal

/-- The mean absolute value is bounded by the `L^q` norm on a probability
space.
@isnad1 id=le.2h4v.s6.1a3095bb74ec from=translated src=- shape=21d3e528 vocab=f40df75c
-/
theorem integral_abs_le_lpNorm_nat
    [IsProbabilityMeasure mu]
    (A : Omega → ℝ) {q : ℕ} (hq : 1 ≤ q)
    (hAq : MemLp A q mu) :
    ∫ omega, |A omega| ∂mu ≤ lpNorm A q mu := by
  have hqone : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast hq
  have hAone : MemLp A 1 mu := hAq.mono_exponent hqone
  calc
    ∫ omega, |A omega| ∂mu = lpNorm A 1 mu := by
      rw [lpNorm_one_eq_integral_norm hAone.aestronglyMeasurable]
      simp only [Real.norm_eq_abs]
    _ ≤ lpNorm A q mu := lpNorm_one_le_lpNorm_nat A hq hAq

/-- Centring costs at most a factor two in every strong `L^q` envelope norm.
This is the exact generic estimate used to pass from the report's raw
envelope `A` to Marchina's centred envelope.
@isnad1 id=le.2h4v.s7.2b69aae0ef29 from=translated src=- shape=5d56da83 vocab=ae737769
-/
theorem lpNorm_centeredProcessEnvelope_le_two_mul
    [IsProbabilityMeasure mu]
    (A : Omega → ℝ) {q : ℕ} (hq : 1 ≤ q)
    (hAq : MemLp A q mu) :
    lpNorm (centeredProcessEnvelope A mu) q mu ≤
      2 * lpNorm A q mu := by
  let m : ℝ := ∫ z, |A z| ∂mu
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hq))
  have hsum : MemLp
      (fun omega ↦ |A omega| + m) q mu :=
    hAq.norm.add (memLp_const m)
  have htri :
      lpNorm (fun omega ↦ |A omega| + m) q mu ≤
        lpNorm (fun omega ↦ |A omega|) q mu +
          lpNorm (fun _ : Omega ↦ m) q mu :=
    lpNorm_add_le hAq.norm (by exact_mod_cast hq)
  have hm : m ≤ lpNorm A q mu := by
    exact integral_abs_le_lpNorm_nat A hq hAq
  have hconst : lpNorm (fun _ : Omega ↦ m) q mu = |m| := by
    rw [lpNorm_const hq0 (IsProbabilityMeasure.ne_zero mu) m]
    simp only [Real.norm_eq_abs, probReal_univ, one_rpow, mul_one]
  have hmnonneg : 0 ≤ m := integral_nonneg fun _ ↦ abs_nonneg _
  change lpNorm (fun omega ↦ |A omega| + m) q mu ≤
    2 * lpNorm A q mu
  calc
    lpNorm (fun omega ↦ |A omega| + m) q mu ≤
        lpNorm (fun omega ↦ |A omega|) q mu +
          lpNorm (fun _ : Omega ↦ m) q mu := htri
    _ = lpNorm A q mu + m := by
      rw [lpNorm_fun_abs hAq.aestronglyMeasurable, hconst,
        abs_of_nonneg hmnonneg]
    _ ≤ lpNorm A q mu + lpNorm A q mu := add_le_add le_rfl hm
    _ = 2 * lpNorm A q mu := by ring

/-- The canonical centred envelope belongs to `L^q` whenever the raw
envelope does.
@isnad1 id=memlp.1h4v.s6.e6670e352bc7 from=translated src=- shape=c2929148 vocab=9faef61e
-/
theorem memLp_centeredProcessEnvelope
    [IsProbabilityMeasure mu]
    (A : Omega → ℝ) {q : ℕ} (hAq : MemLp A q mu) :
    MemLp (centeredProcessEnvelope A mu) q mu := by
  unfold centeredProcessEnvelope
  exact hAq.norm.add (memLp_const (∫ z, |A z| ∂mu))

/-- The `q`-th absolute moment is the `q`-th power of the real `L^q` norm.
This bridge is useful because the existing polynomial-tail API is formulated
with `absoluteMoment`.
@isnad1 id=eq.2h4v.s6.858cb6be5f7b from=translated src=- shape=c3deea13 vocab=f5380969
-/
theorem absoluteMoment_eq_lpNorm_pow
    (A : Omega → ℝ) {q : ℕ} (hq : 0 < q)
    (hAq : MemLp A q mu) :
    absoluteMoment A q mu = lpNorm A q mu ^ q := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
  have hqtop : (q : ℝ≥0∞) ≠ ∞ := by simp
  have hmoment : 0 ≤ absoluteMoment A q mu := absoluteMoment_nonneg A q mu
  have hlp : lpNorm A q mu = (absoluteMoment A q mu) ^ ((q : ℝ)⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop hAq.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
      absoluteMoment]
  rw [hlp]
  exact (Real.rpow_inv_natCast_pow hmoment hq.ne').symm

/-- Strong moment form of the factor-two centred-envelope bound.
@isnad1 id=le.4h5v.s7.08df01bd14a9 from=translated src=- shape=8aa3f892 vocab=972f4c33
-/
theorem absoluteMoment_centeredProcessEnvelope_le
    [IsProbabilityMeasure mu]
    (A : Omega → ℝ) {q : ℕ} (hq : 1 ≤ q)
    (hAq : MemLp A q mu) {K : ℝ} (_hK : 0 ≤ K)
    (hAnorm : lpNorm A q mu ≤ K) :
    absoluteMoment (centeredProcessEnvelope A mu) q mu ≤ (2 * K) ^ q := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hcenterMem := memLp_centeredProcessEnvelope A hAq
  rw [absoluteMoment_eq_lpNorm_pow _ hqpos hcenterMem]
  exact pow_le_pow_left₀ (lpNorm_nonneg)
    ((lpNorm_centeredProcessEnvelope_le_two_mul A hq hAq).trans
      (mul_le_mul_of_nonneg_left hAnorm (by norm_num))) q

/-- A coordinatewise variance proxy follows immediately from the centred
envelope.  This is the `sigma ≤ 2 K2` part of Marchina's specialization;
it is independent of the maximal martingale argument.
@isnad1 id=le.5h7v.s7.0321811f8bbf from=translated src=- shape=5fa98703 vocab=0998feea
-/
theorem absoluteMoment_centeredProcess_two_le
    [IsProbabilityMeasure mu]
    (X : Omega → T → ℝ) (A : Omega → ℝ)
    (hA2 : MemLp A 2 mu)
    (hX : ∀ t, AEMeasurable (fun omega ↦ X omega t) mu)
    (hdom : ∀ omega t, |X omega t| ≤ |A omega|)
    {K2 : ℝ} (hK2 : 0 ≤ K2) (hAnorm : lpNorm A 2 mu ≤ K2)
    (t : T) :
    absoluteMoment (centeredProcess X mu · t) 2 mu ≤ (2 * K2) ^ 2 := by
  have _K2_nonneg : 0 ≤ K2 := hK2
  have hAint : Integrable A mu := hA2.integrable (by norm_num)
  have hcenterMem := memLp_centeredProcessEnvelope A hA2
  have hcoordMeas : AEStronglyMeasurable (centeredProcess X mu · t) mu := by
    exact (hX t).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hcoordMem : MemLp (centeredProcess X mu · t) 2 mu :=
    hcenterMem.mono' hcoordMeas (ae_of_all mu fun omega ↦ by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (centeredProcessEnvelope_nonneg A mu omega)] using
        abs_centeredProcess_le_centeredProcessEnvelope X A hAint hX hdom omega t)
  rw [absoluteMoment_eq_lpNorm_pow _ (by norm_num) hcoordMem]
  have hlp : lpNorm (centeredProcess X mu · t) 2 mu ≤
      lpNorm (centeredProcessEnvelope A mu) 2 mu := by
    apply lpNorm_mono_real hcenterMem
    intro omega
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (centeredProcessEnvelope_nonneg A mu omega)] using
      abs_centeredProcess_le_centeredProcessEnvelope X A hAint hX hdom omega t
  exact pow_le_pow_left₀ lpNorm_nonneg
    (hlp.trans ((lpNorm_centeredProcessEnvelope_le_two_mul A (by norm_num) hA2).trans
      (mul_le_mul_of_nonneg_left hAnorm (by norm_num)))) 2

/-! ## The coarse Marchina variance-correction estimate -/

/-- If an auxiliary variable is pointwise dominated by twice the centred
envelope, its `L²` norm is at most four times the raw-envelope `L²` norm.
Marchina's extremal variables `zeta_k` have precisely this domination: their
law is obtained by replacing a lower part of the law of twice the centred
envelope by zero.
@isnad1 id=le.5h5v.s7.6d00acf4daa5 from=translated src=- shape=089a2ec9 vocab=386dfaf7
-/
theorem absoluteMoment_auxiliary_le_sixteen_mul_sq
    [IsProbabilityMeasure mu]
    (A zeta : Omega → ℝ)
    (hA2 : MemLp A 2 mu) (hzeta : AEMeasurable zeta mu)
    (hdom : ∀ omega, |zeta omega| ≤
      2 * centeredProcessEnvelope A mu omega)
    {K2 : ℝ} (_hK2 : 0 ≤ K2) (hAnorm : lpNorm A 2 mu ≤ K2) :
    absoluteMoment zeta 2 mu ≤ 16 * K2 ^ 2 := by
  let B : Omega → ℝ := centeredProcessEnvelope A mu
  have hBMem : MemLp B 2 mu := memLp_centeredProcessEnvelope A hA2
  have htwoBMem : MemLp (fun omega ↦ 2 * B omega) 2 mu :=
    hBMem.const_mul 2
  have hzetaMem : MemLp zeta 2 mu := by
    apply htwoBMem.mono' hzeta.aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs]
    exact hdom omega
  have hlp : lpNorm zeta 2 mu ≤
      lpNorm (fun omega ↦ 2 * B omega) 2 mu := by
    apply lpNorm_mono_real htwoBMem
    intro omega
    rw [Real.norm_eq_abs]
    exact hdom omega
  have hscaled : lpNorm (fun omega ↦ 2 * B omega) 2 mu =
      2 * lpNorm B 2 mu := by
    change lpNorm (2 * B) 2 mu = 2 * lpNorm B 2 mu
    exact lpNorm_natCast_mul 2 B 2 mu
  have hfour : lpNorm zeta 2 mu ≤ 4 * K2 := by
    calc
      lpNorm zeta 2 mu ≤ lpNorm (fun omega ↦ 2 * B omega) 2 mu := hlp
      _ = 2 * lpNorm B 2 mu := hscaled
      _ ≤ 2 * (2 * lpNorm A 2 mu) := by
        gcongr
        exact lpNorm_centeredProcessEnvelope_le_two_mul A (by norm_num) hA2
      _ ≤ 2 * (2 * K2) := by gcongr
      _ = 4 * K2 := by ring
  rw [absoluteMoment_eq_lpNorm_pow zeta (by norm_num) hzetaMem]
  calc
    lpNorm zeta 2 mu ^ 2 ≤ (4 * K2) ^ 2 :=
      pow_le_pow_left₀ lpNorm_nonneg hfour 2
    _ = 16 * K2 ^ 2 := by ring

/-- The average second moment used as Marchina's correction `v_n`.-/
def averageAbsoluteSecondMoment {n : ℕ}
    (zeta : Fin n → Omega → ℝ) (mu : Measure Omega) : ℝ :=
  (∑ i, absoluteMoment (zeta i) 2 mu) / n

/-- Averaging the preceding pointwise-in-`k` estimate preserves the same
constant.  This is the report's coarse bound `v_n ≤ 16 K2²`.
@isnad1 id=le.2h5v.s6.857466a741dc from=translated src=- shape=d8516b90 vocab=4c26d9c7
-/
theorem averageAbsoluteSecondMoment_le_sixteen_mul_sq
    {n : ℕ} (hn : 0 < n) (zeta : Fin n → Omega → ℝ)
    {K2 : ℝ}
    (hzeta : ∀ i, absoluteMoment (zeta i) 2 mu ≤ 16 * K2 ^ 2) :
    averageAbsoluteSecondMoment zeta mu ≤ 16 * K2 ^ 2 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold averageAbsoluteSecondMoment
  rw [div_le_iff₀ hnreal]
  calc
    ∑ i : Fin n, absoluteMoment (zeta i) 2 mu ≤
        ∑ _i : Fin n, 16 * K2 ^ 2 := Finset.sum_le_sum fun i _ ↦ hzeta i
    _ = (n : ℝ) * (16 * K2 ^ 2) := by simp [mul_comm]
    _ = (16 * K2 ^ 2) * (n : ℝ) := by ring

end ProbabilityTheory
