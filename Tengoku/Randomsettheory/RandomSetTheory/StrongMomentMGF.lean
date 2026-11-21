/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.ExponentialTaylor
import Tengoku.Seed.MeasureTheory.Function.ConditionalExpectation.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One-sided strong-moment MGF estimates

This file develops the moment-generating-function step in the strong-moment
Fuk--Nagaev argument.  The central scalar input is
`exp_le_oneSidedExpTaylorBound`: above order two, only positive moments are
needed.  This is essential for an upper-tail martingale inequality.

The first endpoint below is deliberately stated for one probability measure.
It is later applied on the fibres of a conditional-expectation kernel.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Hard upper truncation, as used in Rio's one-sided Fuk--Nagaev proof.-/
def upperTruncation (X : Omega → ℝ) (y : ℝ) : Omega → ℝ :=
  fun omega => min (X omega) y

omit [MeasurableSpace Omega] in
/--
@isnad1 id=eq.0h4v.s4.1b1087702e1e from=translated src=- shape=a77a99ee vocab=d0bccca9
-/
@[simp] theorem upperTruncation_apply (X : Omega → ℝ) (y : ℝ)
    (omega : Omega) :
    upperTruncation X y omega = min (X omega) y := rfl

omit [MeasurableSpace Omega] in
/--
@isnad1 id=le.0h4v.s4.f19ab4eba4af from=translated src=- shape=77044d4e vocab=eaacda0c
-/
theorem upperTruncation_le (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    upperTruncation X y omega ≤ y :=
  min_le_right _ _

omit [MeasurableSpace Omega] in
/--
@isnad1 id=le.0h4v.s4.9d6b05259c9d from=translated src=- shape=b43819fa vocab=eaacda0c
-/
theorem upperTruncation_le_self (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    upperTruncation X y omega ≤ X omega :=
  min_le_left _ _

/--
@isnad1 id=measurab.1h3v.s4.1bca78b10b95 from=translated src=- shape=6b09dfb9 vocab=ea609541
-/
theorem measurable_upperTruncation {X : Omega → ℝ}
    (hX : Measurable X) (y : ℝ) :
    Measurable (upperTruncation X y) := by
  exact hX.min measurable_const

/--
@isnad1 id=aemeasur.1h4v.s5.cc4dc1291639 from=translated src=- shape=9de12b72 vocab=f2520b67
-/
theorem aemeasurable_upperTruncation {X : Omega → ℝ}
    (hX : AEMeasurable X mu) (y : ℝ) :
    AEMeasurable (upperTruncation X y) mu := by
  exact hX.min aemeasurable_const

/-- Positive parts commute with multiplication by a nonnegative scalar.
@isnad1 id=eq.1h2v.s5.99a253d2a7e5 from=translated src=- shape=f0886876 vocab=e8b42584
-/
theorem max_mul_eq_mul_max (t x : ℝ) (ht : 0 ≤ t) :
    max (t * x) 0 = t * max x 0 := by
  rw [mul_max_of_nonneg x 0 ht]
  simp

omit [MeasurableSpace Omega] in
/-- The positive part of an upper truncation is bounded by the truncation
height when that height is nonnegative.
@isnad1 id=le.1h4v.s5.67d0ff3f0bdc from=translated src=- shape=40713455 vocab=bf81fd5e
-/
theorem max_upperTruncation_zero_le
    (X : Omega → ℝ) {y : ℝ} (hy : 0 ≤ y) (omega : Omega) :
    max (upperTruncation X y omega) 0 ≤ y := by
  exact max_le (upperTruncation_le X y omega) hy

/-- Upper truncation preserves integrability under a finite measure.
@isnad1 id=integrab.1h4v.s6.eb7b8b1ab5f0 from=translated src=- shape=82d6c675 vocab=907d657b
-/
theorem integrable_upperTruncation [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu) (y : ℝ) :
    Integrable (upperTruncation X y) mu := by
  change Integrable (X ⊓ fun _ => y) mu
  exact hX.inf (integrable_const y)

omit [MeasurableSpace Omega] in
/-- Taking the positive part after upper truncation can only decrease it.
@isnad1 id=le.0h4v.s5.3bd573a6a3f7 from=translated src=- shape=b21867b3 vocab=bf81fd5e
-/
theorem max_upperTruncation_zero_le_max_self
    (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    max (upperTruncation X y omega) 0 ≤ max (X omega) 0 := by
  exact max_le_max (upperTruncation_le_self X y omega) le_rfl

omit [MeasurableSpace Omega] in
/-- Positive integer moments contract under upper truncation.
@isnad1 id=le.0h5v.s6.1050e06db469 from=translated src=- shape=16edd2d5 vocab=76130899
-/
theorem pow_max_upperTruncation_zero_le_pow_max_self
    (X : Omega → ℝ) (y : ℝ) (k : ℕ) (omega : Omega) :
    (max (upperTruncation X y omega) 0) ^ k ≤
      (max (X omega) 0) ^ k := by
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_upperTruncation_zero_le_max_self X y omega) k

omit [MeasurableSpace Omega] in
/-- When the truncation height is nonnegative, upper truncation cannot
increase the square.  The nonnegativity assumption is necessary: replacing a
small positive value by a negative cap could increase its absolute value.
@isnad1 id=le.1h4v.s6.73bba8e71758 from=translated src=- shape=56fc2b11 vocab=63968449
-/
theorem sq_upperTruncation_le_sq_self
    (X : Omega → ℝ) {y : ℝ} (hy : 0 ≤ y) (omega : Omega) :
    upperTruncation X y omega ^ 2 ≤ X omega ^ 2 := by
  by_cases hxy : X omega ≤ y
  · rw [upperTruncation_apply, min_eq_left hxy]
  · have hyx : y ≤ X omega := (le_of_lt (lt_of_not_ge hxy))
    rw [upperTruncation_apply, min_eq_right hyx]
    exact pow_le_pow_left₀ hy hyx 2

/-- Integrability of the square is preserved by nonnegative upper
truncation.
@isnad1 id=integrab.3h4v.s6.5d52197d864d from=translated src=- shape=6126e6c5 vocab=da66facc
-/
theorem integrable_sq_upperTruncation
    {X : Omega → ℝ} (hX : AEMeasurable X mu)
    (hXsq : Integrable (fun omega => X omega ^ 2) mu)
    {y : ℝ} (hy : 0 ≤ y) :
    Integrable (fun omega => upperTruncation X y omega ^ 2) mu := by
  apply Integrable.mono_nonneg hXsq
    ((aemeasurable_upperTruncation hX y).pow_const 2).aestronglyMeasurable
  · exact ae_of_all mu fun omega => sq_nonneg _
  · exact ae_of_all mu fun omega => sq_upperTruncation_le_sq_self X hy omega

/-- Integrability of every displayed positive moment is preserved by upper
truncation.
@isnad1 id=integrab.2h5v.s7.80f3e3e1adc7 from=translated src=- shape=e477d6f5 vocab=5b712570
-/
theorem integrable_pow_max_upperTruncation_zero
    {X : Omega → ℝ} (hX : AEMeasurable X mu) (y : ℝ) (k : ℕ)
    (hpow : Integrable (fun omega => (max (X omega) 0) ^ k) mu) :
    Integrable
      (fun omega => (max (upperTruncation X y omega) 0) ^ k) mu := by
  have hmeas : AEStronglyMeasurable
      (fun omega => (max (upperTruncation X y omega) 0) ^ k) mu :=
    (((aemeasurable_upperTruncation hX y).max aemeasurable_const).pow_const k)
      |>.aestronglyMeasurable
  apply Integrable.mono_nonneg hpow hmeas
  · exact ae_of_all mu fun omega => pow_nonneg (le_max_right _ _) k
  · exact ae_of_all mu fun omega =>
      pow_max_upperTruncation_zero_le_pow_max_self X y k omega

/-- Deterministic exponent obtained by integrating the one-sided Taylor
majorant.-/
def strongMomentTaylorExponent
    (q : ℕ) (t y second : ℝ) (moment : ℕ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * t ^ 2 * second +
    (∑ k ∈ Finset.Ico 3 q, t ^ k / (k.factorial : ℝ) * moment k) +
    t ^ q / (q.factorial : ℝ) * Real.exp (t * y) * moment q

/-- Strong-moment Taylor exponents add exactly when their deterministic
second- and higher-moment proxies add.
@isnad1 id=eq.0h7v.s6.7eb3a7ed436d from=translated src=- shape=75974dbf vocab=69c6c73f
-/
theorem sum_strongMomentTaylorExponent
    {ι : Type*} (s : Finset ι) (q : ℕ) (t y : ℝ)
    (second : ι → ℝ) (moment : ι → ℕ → ℝ) :
    (∑ i ∈ s, strongMomentTaylorExponent q t y (second i) (moment i)) =
      strongMomentTaylorExponent q t y
        (∑ i ∈ s, second i) (fun k => ∑ i ∈ s, moment i k) := by
  classical
  have hfirst :
      (∑ i ∈ s, (1 / 2 : ℝ) * t ^ 2 * second i) =
        (1 / 2 : ℝ) * t ^ 2 * ∑ i ∈ s, second i := by
    rw [Finset.mul_sum]
  have hmiddle :
      (∑ i ∈ s, ∑ k ∈ Finset.Ico 3 q,
        t ^ k / (k.factorial : ℝ) * moment i k) =
        ∑ k ∈ Finset.Ico 3 q,
          t ^ k / (k.factorial : ℝ) * ∑ i ∈ s, moment i k := by
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  have htail :
      (∑ i ∈ s,
        t ^ q / (q.factorial : ℝ) * Real.exp (t * y) * moment i q) =
        t ^ q / (q.factorial : ℝ) * Real.exp (t * y) *
          ∑ i ∈ s, moment i q := by
    rw [Finset.mul_sum]
  unfold strongMomentTaylorExponent
  simp only [Finset.sum_add_distrib]
  rw [hfirst, hmiddle, htail]

/-- The integrated one-sided Taylor estimate.

The function is only required to be bounded above by `y`; its negative tail
may be unbounded.  Integrability of the displayed positive moments is made
explicit so this lemma can be used both ordinarily and on conditional-law
fibres.
@isnad1 id=le.8h6v.s8.64cfc141137f from=translated src=- shape=bd81994b vocab=c5e6d2fa
-/
theorem integral_exp_mul_le_exp_strongMomentTaylorExponent
    [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (q : ℕ) (hq : 3 ≤ q)
    {t y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega => X omega ^ 2) mu)
    (hpow : ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega => (max (X omega) 0) ^ k) mu)
    (hupper : ∀ᵐ omega ∂mu, X omega ≤ y)
    (hcenter : (∫ omega, X omega ∂mu) ≤ 0) :
    (∫ omega, Real.exp (t * X omega) ∂mu) ≤
      Real.exp (strongMomentTaylorExponent q t y
        (∫ omega, X omega ^ 2 ∂mu)
        (fun k => ∫ omega, (max (X omega) 0) ^ k ∂mu)) := by
  let M : ℕ → ℝ := fun k => ∫ omega, (max (X omega) 0) ^ k ∂mu
  let V : ℝ := ∫ omega, X omega ^ 2 ∂mu
  let E : ℝ := strongMomentTaylorExponent q t y V M
  have hExp : Integrable (fun omega => Real.exp (t * X omega)) mu := by
    apply Integrable.of_bound
      ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (Real.exp (t * y))
    filter_upwards [hupper] with omega homega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_monotone (mul_le_mul_of_nonneg_left homega ht)
  have hMomentNonneg : ∀ k, 0 ≤ M k := by
    intro k
    exact integral_nonneg fun omega => pow_nonneg (le_max_right _ _) k
  have hVNonneg : 0 ≤ V := integral_nonneg fun omega => sq_nonneg _
  have hENonneg : 0 ≤ E := by
    unfold E strongMomentTaylorExponent
    have hsum : 0 ≤ ∑ k ∈ Finset.Ico 3 q,
        t ^ k / (k.factorial : ℝ) * M k := by
      positivity
    positivity
  have hfiniteInt : ∀ k ∈ Finset.Ico 3 q,
      Integrable (fun omega =>
        (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) mu := by
    intro k hk
    exact (hpow k (Finset.mem_Icc.mpr
      ⟨(mem_Ico.mp hk).1.trans' (by norm_num),
        (mem_Ico.mp hk).2.le⟩)).const_mul _
  have htailInt : Integrable (fun omega =>
      (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
        (max (X omega) 0) ^ q) mu :=
    (hpow q (Finset.mem_Icc.mpr
      ⟨hq.trans' (by norm_num), le_rfl⟩)).const_mul _
  have hmajorantInt : Integrable (fun omega =>
      1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
        (∑ k ∈ Finset.Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
        (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
          (max (X omega) 0) ^ q) mu := by
    have hlin : Integrable (fun omega => t * X omega) mu := hX.const_mul t
    have hquad : Integrable
        (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2) mu := by
      have hs : Integrable (fun omega => (t * X omega) ^ 2) mu := by
        convert hXsq.const_mul (t ^ 2) using 1
        ext omega
        ring
      exact hs.const_mul _
    have hsumInt : Integrable (fun omega =>
        ∑ k ∈ Finset.Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) mu := by
      exact integrable_finsetSum _ hfiniteInt
    have hshape :
        (fun omega =>
          1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
            (∑ k ∈ Finset.Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
            (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
              (max (X omega) 0) ^ q) =
          ((((fun _ : Omega => (1 : ℝ)) + (fun omega => t * X omega)) +
              (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2)) +
            (fun omega => ∑ k ∈ Finset.Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k)) +
            (fun omega =>
              (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
                (max (X omega) 0) ^ q) := by
      funext omega
      simp only [Pi.add_apply]
    rw [hshape]
    exact (((((integrable_const (1 : ℝ)).add hlin).add hquad).add
      hsumInt).add htailInt)
  have hpoint : ∀ᵐ omega ∂mu,
      Real.exp (t * X omega) ≤
        1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
          (∑ k ∈ Finset.Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
          (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
            (max (X omega) 0) ^ q := by
    filter_upwards [hupper] with omega homega
    have hTaylor := exp_le_oneSidedExpTaylorBound q hq (t * X omega)
    have hmax : max (t * X omega) 0 = t * max (X omega) 0 :=
      max_mul_eq_mul_max t (X omega) ht
    have hmaxUpper : max (X omega) 0 ≤ y := max_le homega hy
    have hexpUpper : Real.exp (t * max (X omega) 0) ≤ Real.exp (t * y) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_left hmaxUpper ht)
    unfold oneSidedExpTaylorBound at hTaylor
    rw [hmax] at hTaylor
    have hsumEq :
        (∑ k ∈ Finset.Ico 3 q,
          (t * max (X omega) 0) ^ k / (k.factorial : ℝ)) =
        ∑ k ∈ Finset.Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k := by
      apply sum_congr rfl
      intro k _hk
      rw [mul_pow]
      ring
    have htailEq :
        (t * max (X omega) 0) ^ q / (q.factorial : ℝ) *
            Real.exp (t * max (X omega) 0) =
          (t ^ q / (q.factorial : ℝ) *
              Real.exp (t * max (X omega) 0)) *
            (max (X omega) 0) ^ q := by
      rw [mul_pow]
      ring
    rw [hsumEq, htailEq] at hTaylor
    have hcoefNonneg : 0 ≤
        t ^ q / (q.factorial : ℝ) * (max (X omega) 0) ^ q := by
      positivity
    have htailBound :
        (t ^ q / (q.factorial : ℝ) *
            Real.exp (t * max (X omega) 0)) *
              (max (X omega) 0) ^ q ≤
          (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
              (max (X omega) 0) ^ q := by
      calc
        (t ^ q / (q.factorial : ℝ) *
            Real.exp (t * max (X omega) 0)) *
              (max (X omega) 0) ^ q =
            (t ^ q / (q.factorial : ℝ) *
              (max (X omega) 0) ^ q) *
                Real.exp (t * max (X omega) 0) := by ring
        _ ≤ (t ^ q / (q.factorial : ℝ) *
              (max (X omega) 0) ^ q) * Real.exp (t * y) :=
          mul_le_mul_of_nonneg_left hexpUpper hcoefNonneg
        _ = (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
              (max (X omega) 0) ^ q := by ring
    have hprefixEq :
        1 + t * X omega + (t * X omega) ^ 2 / 2 +
            (∑ k ∈ Finset.Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) =
          1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
            (∑ k ∈ Finset.Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) := by
      ring
    exact hTaylor.trans (add_le_add hprefixEq.le htailBound)
  have hint := integral_mono_ae hExp hmajorantInt hpoint
  have hlin : Integrable (fun omega => t * X omega) mu := hX.const_mul t
  have hquad : Integrable
      (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2) mu := by
    have hs : Integrable (fun omega => (t * X omega) ^ 2) mu := by
      convert hXsq.const_mul (t ^ 2) using 1
      ext omega
      ring
    exact hs.const_mul _
  have hsumInt : Integrable (fun omega =>
      ∑ k ∈ Finset.Ico 3 q,
        (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) mu :=
    by
      exact integrable_finsetSum _ hfiniteInt
  have hlinIntegral :
      (∫ omega, t * X omega ∂mu) = t * ∫ omega, X omega ∂mu := by
    rw [integral_const_mul]
  have hquadIntegral :
      (∫ omega, (1 / 2 : ℝ) * (t * X omega) ^ 2 ∂mu) =
        (1 / 2 : ℝ) * t ^ 2 * V := by
    rw [integral_const_mul]
    have hscaled :
        (∫ omega, (t * X omega) ^ 2 ∂mu) = t ^ 2 * V := by
      change (∫ omega, (t * X omega) ^ 2 ∂mu) =
        t ^ 2 * ∫ omega, X omega ^ 2 ∂mu
      have hfun : (fun omega => (t * X omega) ^ 2) =
          fun omega => t ^ 2 * X omega ^ 2 := by
        funext omega
        ring
      rw [hfun, integral_const_mul]
    rw [hscaled]
    ring
  have hsumIntegral :
      (∫ omega, (∑ k ∈ Finset.Ico 3 q,
        (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) ∂mu) =
      ∑ k ∈ Finset.Ico 3 q,
        t ^ k / (k.factorial : ℝ) * M k := by
    calc
      (∫ omega, (∑ k ∈ Finset.Ico 3 q,
          (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) ∂mu) =
          ∑ k ∈ Finset.Ico 3 q,
            ∫ omega, (t ^ k / (k.factorial : ℝ)) *
              (max (X omega) 0) ^ k ∂mu :=
        integral_finsetSum (Finset.Ico 3 q) hfiniteInt
      _ = ∑ k ∈ Finset.Ico 3 q,
          t ^ k / (k.factorial : ℝ) * M k := by
        apply sum_congr rfl
        intro k hk
        rw [integral_const_mul]
  have htailIntegral :
      (∫ omega,
        (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
          (max (X omega) 0) ^ q ∂mu) =
        t ^ q / (q.factorial : ℝ) * Real.exp (t * y) * M q := by
    rw [integral_const_mul]
  have hmajorantIntegral :
      (∫ omega,
        1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
          (∑ k ∈ Finset.Ico 3 q,
            (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
          (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
            (max (X omega) 0) ^ q ∂mu) =
        1 + t * (∫ omega, X omega ∂mu) + E := by
    have hconst : Integrable (fun _ : Omega => (1 : ℝ)) mu := integrable_const _
    have hconstLin := hconst.add hlin
    have hconstLinQuad := hconstLin.add hquad
    have hprefix := hconstLinQuad.add hsumInt
    have hshape :
        (fun omega =>
          1 + t * X omega + (1 / 2 : ℝ) * (t * X omega) ^ 2 +
            (∑ k ∈ Finset.Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k) +
            (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
              (max (X omega) 0) ^ q) =
          ((((fun _ : Omega => (1 : ℝ)) + (fun omega => t * X omega)) +
              (fun omega => (1 / 2 : ℝ) * (t * X omega) ^ 2)) +
            (fun omega => ∑ k ∈ Finset.Ico 3 q,
              (t ^ k / (k.factorial : ℝ)) * (max (X omega) 0) ^ k)) +
            (fun omega =>
              (t ^ q / (q.factorial : ℝ) * Real.exp (t * y)) *
                (max (X omega) 0) ^ q) := by
      funext omega
      simp only [Pi.add_apply]
    rw [hshape]
    rw [integral_add' hprefix htailInt,
      integral_add' hconstLinQuad hsumInt,
      integral_add' hconstLin hquad,
      integral_add' hconst hlin,
      integral_const, hlinIntegral, hquadIntegral,
      hsumIntegral, htailIntegral]
    simp only [probReal_univ, one_smul]
    unfold E strongMomentTaylorExponent
    ring
  rw [hmajorantIntegral] at hint
  calc
    (∫ omega, Real.exp (t * X omega) ∂mu) ≤
        1 + t * (∫ omega, X omega ∂mu) + E := hint
    _ ≤ 1 + E := by
      have htcenter : t * (∫ omega, X omega ∂mu) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht hcenter
      linarith
    _ ≤ Real.exp E := by
      simpa [add_comm] using Real.add_one_le_exp E

end ProbabilityTheory
