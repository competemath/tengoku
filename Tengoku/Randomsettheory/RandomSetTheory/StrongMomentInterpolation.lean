/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.MeasureTheory.Integral.MeanInequalities
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interpolation of strong moments

This file proves the interpolation step used in Rio's strong-moment
Fuk--Nagaev argument.  If `2 ≤ k ≤ q`, put

`a = (q - k) / (q - 2)` and `b = (k - 2) / (q - 2)`.

Then `a, b ≥ 0`, `a + b = 1`, and Hölder's inequality, first under the
integral and then over a finite family, gives

`sum_i ∫ X_i^k ≤ (sum_i ∫ X_i^2)^a (sum_i ∫ X_i^q)^b`.

The `ENNReal` statements are the core results.  A real-valued Bochner
integral endpoint, tailored to positive moments, is provided at the end.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

/-- Weight of the second moment in interpolation between orders `2` and
`q`.-/
def strongMomentSecondWeight (q k : ℕ) : ℝ :=
  ((q : ℝ) - (k : ℝ)) / ((q : ℝ) - 2)

/-- Weight of the `q`-th moment in interpolation between orders `2` and
`q`.-/
def strongMomentQWeight (q k : ℕ) : ℝ :=
  ((k : ℝ) - 2) / ((q : ℝ) - 2)

/--
@isnad1 id=le.2h2v.s5.7203b542e1a9 from=translated src=- shape=c65ec732 vocab=67161258
-/
theorem strongMomentSecondWeight_nonneg {q k : ℕ} (hkq : k ≤ q)
    (hq : 3 ≤ q) :
    0 ≤ strongMomentSecondWeight q k := by
  unfold strongMomentSecondWeight
  exact div_nonneg (sub_nonneg.mpr (mod_cast hkq))
    (sub_nonneg.mpr (by norm_num; omega))

/--
@isnad1 id=le.2h2v.s5.a823fa70268f from=translated src=- shape=e534e85e vocab=434200c2
-/
theorem strongMomentQWeight_nonneg {q k : ℕ} (hk : 2 ≤ k)
    (hq : 3 ≤ q) :
    0 ≤ strongMomentQWeight q k := by
  unfold strongMomentQWeight
  exact div_nonneg (sub_nonneg.mpr (by norm_num; omega))
    (sub_nonneg.mpr (by norm_num; omega))

/--
@isnad1 id=eq.1h2v.s5.23b6bdf78170 from=translated src=- shape=b6ec9cd2 vocab=896db227
-/
theorem strongMomentSecondWeight_add_QWeight {q k : ℕ} (hq : 3 ≤ q) :
    strongMomentSecondWeight q k + strongMomentQWeight q k = 1 := by
  unfold strongMomentSecondWeight strongMomentQWeight
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (q : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/--
@isnad1 id=eq.1h2v.s5.03dac3f10ac6 from=translated src=- shape=33f9aa59 vocab=2544e593
-/
theorem two_mul_strongMomentSecondWeight_add_q_mul_strongMomentQWeight
    {q k : ℕ} (hq : 3 ≤ q) :
    2 * strongMomentSecondWeight q k +
        (q : ℝ) * strongMomentQWeight q k = k := by
  unfold strongMomentSecondWeight strongMomentQWeight
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (q : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/-! ## Algebraic Hölder inequality for a finite family -/

/-- Weighted Hölder inequality in the form needed to sum interpolated
moments.  Unlike a pointwise AM--GM bound, this retains the two global sums
with their interpolation powers.
@isnad1 id=le.3h6v.s7.72fcd1392cf1 from=translated src=- shape=e4177ba0 vocab=b495c0d6
-/
theorem sum_rpow_mul_rpow_le_sum_rpow_mul_sum_rpow
    {ι : Type*} (s : Finset ι) (A B : ι → ℝ≥0∞)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∑ i ∈ s, A i ^ a * B i ^ b ≤
      (∑ i ∈ s, A i) ^ a * (∑ i ∈ s, B i) ^ b := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_add] at hab
    simp [hab]
  rcases hb.eq_or_lt with rfl | hb
  · simp only [add_zero] at hab
    simp [hab]
  have hholder : (1 / a).HolderConjugate (1 / b) :=
    Real.holderConjugate_one_div ha hb hab
  have h := ENNReal.inner_le_Lp_mul_Lq s
    (fun i => A i ^ a) (fun i => B i ^ b) hholder
  simpa only [← ENNReal.rpow_mul, one_div, inv_inv, mul_inv_cancel₀ ha.ne',
    mul_inv_cancel₀ hb.ne', ENNReal.rpow_one] using h

/-! ## Interpolation under one measure -/

/-- Log-convexity of nonnegative moments, expressed with Lebesgue
integrals.  This theorem includes the endpoints `k = 2` and `k = q` and
does not require finiteness of either endpoint moment.
@isnad1 id=le.4h5v.s7.c268311b5228 from=translated src=- shape=f8dd5907 vocab=f387bf0d
-/
theorem lintegral_rpow_nat_le_strongMomentInterpolation
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (X : Omega → ℝ≥0∞) {q k : ℕ} (hq : 3 ≤ q)
    (hk : 2 ≤ k) (hkq : k ≤ q) (hX : AEMeasurable X mu) :
    ∫⁻ omega, X omega ^ (k : ℝ) ∂mu ≤
      (∫⁻ omega, X omega ^ (2 : ℝ) ∂mu) ^
          strongMomentSecondWeight q k *
        (∫⁻ omega, X omega ^ (q : ℝ) ∂mu) ^
          strongMomentQWeight q k := by
  let a := strongMomentSecondWeight q k
  let b := strongMomentQWeight q k
  have ha : 0 ≤ a := strongMomentSecondWeight_nonneg hkq hq
  have hb : 0 ≤ b := strongMomentQWeight_nonneg hk hq
  have hab : a + b = 1 := strongMomentSecondWeight_add_QWeight hq
  have hexp : 2 * a + (q : ℝ) * b = k :=
    two_mul_strongMomentSecondWeight_add_q_mul_strongMomentQWeight hq
  have hXtwo : AEMeasurable (fun omega => X omega ^ (2 : ℝ)) mu :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hX
  have hXq : AEMeasurable (fun omega => X omega ^ (q : ℝ)) mu :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hX
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    (μ := mu) (f := fun omega => X omega ^ (2 : ℝ))
    (g := fun omega => X omega ^ (q : ℝ))
    hXtwo hXq ha hb hab
  calc
    ∫⁻ omega, X omega ^ (k : ℝ) ∂mu =
        ∫⁻ omega,
          (X omega ^ (2 : ℝ)) ^ a *
            (X omega ^ (q : ℝ)) ^ b ∂mu := by
      apply lintegral_congr
      intro omega
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg (by norm_num) ha)
          (mul_nonneg (Nat.cast_nonneg q) hb)]
      exact congrArg (X omega ^ ·) hexp.symm
    _ ≤ _ := by simpa [a, b] using hholder

/-! ## Interpolation after summing a finite family -/

/-- Rio's two-stage interpolation inequality: the intermediate moments are
first interpolated for each member of the family, and the resulting terms
are then summed by a second application of Hölder.
@isnad1 id=le.4h7v.s7.f453fdb53290 from=translated src=- shape=1031de90 vocab=80ef4c86
-/
theorem sum_lintegral_rpow_nat_le_strongMomentInterpolation
    {ι Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (s : Finset ι) (X : ι → Omega → ℝ≥0∞)
    {q k : ℕ} (hq : 3 ≤ q) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) mu) :
    ∑ i ∈ s, ∫⁻ omega, X i omega ^ (k : ℝ) ∂mu ≤
      (∑ i ∈ s, ∫⁻ omega, X i omega ^ (2 : ℝ) ∂mu) ^
          strongMomentSecondWeight q k *
        (∑ i ∈ s, ∫⁻ omega, X i omega ^ (q : ℝ) ∂mu) ^
          strongMomentQWeight q k := by
  let a := strongMomentSecondWeight q k
  let b := strongMomentQWeight q k
  calc
    ∑ i ∈ s, ∫⁻ omega, X i omega ^ (k : ℝ) ∂mu ≤
        ∑ i ∈ s,
          (∫⁻ omega, X i omega ^ (2 : ℝ) ∂mu) ^ a *
            (∫⁻ omega, X i omega ^ (q : ℝ) ∂mu) ^ b := by
      exact Finset.sum_le_sum fun i hi =>
        lintegral_rpow_nat_le_strongMomentInterpolation
          mu (X i) hq hk hkq (hX i hi)
    _ ≤ _ := sum_rpow_mul_rpow_le_sum_rpow_mul_sum_rpow
      s
      (fun i => ∫⁻ omega, X i omega ^ (2 : ℝ) ∂mu)
      (fun i => ∫⁻ omega, X i omega ^ (q : ℝ) ∂mu)
      (strongMomentSecondWeight_nonneg hkq hq)
      (strongMomentQWeight_nonneg hk hq)
      (strongMomentSecondWeight_add_QWeight hq)

/-! ## Real-valued positive moments -/

/-- Conversion between a finite nonnegative real moment and the `ENNReal`
moment used by the interpolation theorem.
@isnad1 id=eq.2h4v.s7.f38a8ceeb896 from=translated src=- shape=849e755f vocab=5b0b11a2
-/
theorem ofReal_integral_pow_eq_lintegral_rpow_of_ae_nonneg
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X : Omega → ℝ} (r : ℕ) (hX : 0 ≤ᵐ[mu] X)
    (hInt : Integrable (fun omega => X omega ^ r) mu) :
    ENNReal.ofReal (∫ omega, X omega ^ r ∂mu) =
      ∫⁻ omega, ENNReal.ofReal (X omega) ^ (r : ℝ) ∂mu := by
  have hpow : 0 ≤ᵐ[mu] fun omega => X omega ^ r :=
    hX.mono fun omega homega => pow_nonneg homega r
  calc
    ENNReal.ofReal (∫ omega, X omega ^ r ∂mu) =
        ∫⁻ omega, ENNReal.ofReal (X omega ^ r) ∂mu :=
      ofReal_integral_eq_lintegral_ofReal hInt hpow
    _ = ∫⁻ omega, ENNReal.ofReal (X omega) ^ (r : ℝ) ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hX] with omega homega
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow homega]

/-- Finite-family interpolation for real-valued nonnegative moments.

This is the form directly applicable to the positive parts of martingale
differences.  Integrability of the three displayed orders is explicit;
the surrounding strong-moment API already supplies it for every
`k ∈ Icc 2 q`.
@isnad1 id=le.8h7v.s8.9b24c2284df1 from=translated src=- shape=97ba2de3 vocab=25c932cd
-/
theorem sum_integral_pow_le_strongMomentInterpolation
    {ι Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (s : Finset ι) (X : ι → Omega → ℝ)
    {q k : ℕ} (hq : 3 ≤ q) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) mu)
    (hXnonneg : ∀ i ∈ s, 0 ≤ᵐ[mu] X i)
    (hIntTwo : ∀ i ∈ s, Integrable (fun omega => X i omega ^ 2) mu)
    (hIntK : ∀ i ∈ s, Integrable (fun omega => X i omega ^ k) mu)
    (hIntQ : ∀ i ∈ s, Integrable (fun omega => X i omega ^ q) mu) :
    ∑ i ∈ s, ∫ omega, X i omega ^ k ∂mu ≤
      (∑ i ∈ s, ∫ omega, X i omega ^ 2 ∂mu) ^
          strongMomentSecondWeight q k *
        (∑ i ∈ s, ∫ omega, X i omega ^ q ∂mu) ^
          strongMomentQWeight q k := by
  let a := strongMomentSecondWeight q k
  let b := strongMomentQWeight q k
  have ha : 0 ≤ a := strongMomentSecondWeight_nonneg hkq hq
  have hb : 0 ≤ b := strongMomentQWeight_nonneg hk hq
  have hmomentNonneg : ∀ (r : ℕ), ∀ i ∈ s,
      0 ≤ ∫ omega, X i omega ^ r ∂mu := by
    intro r i hi
    exact integral_nonneg_of_ae (hXnonneg i hi |>.mono fun omega homega =>
      pow_nonneg homega r)
  have hsumNonneg : ∀ (r : ℕ),
      0 ≤ ∑ i ∈ s, ∫ omega, X i omega ^ r ∂mu := by
    intro r
    exact Finset.sum_nonneg fun i hi => hmomentNonneg r i hi
  have hcore := sum_lintegral_rpow_nat_le_strongMomentInterpolation
    mu s (fun i omega => ENNReal.ofReal (X i omega)) hq hk hkq
    (fun i hi => ENNReal.measurable_ofReal.comp_aemeasurable (hX i hi))
  have htwo : ∀ i ∈ s,
      ENNReal.ofReal (∫ omega, X i omega ^ 2 ∂mu) =
        ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (2 : ℝ) ∂mu := by
    intro i hi
    exact ofReal_integral_pow_eq_lintegral_rpow_of_ae_nonneg
      2 (hXnonneg i hi) (hIntTwo i hi)
  have hkMoment : ∀ i ∈ s,
      ENNReal.ofReal (∫ omega, X i omega ^ k ∂mu) =
        ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (k : ℝ) ∂mu := by
    intro i hi
    exact ofReal_integral_pow_eq_lintegral_rpow_of_ae_nonneg
      k (hXnonneg i hi) (hIntK i hi)
  have hqMoment : ∀ i ∈ s,
      ENNReal.ofReal (∫ omega, X i omega ^ q ∂mu) =
        ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (q : ℝ) ∂mu := by
    intro i hi
    exact ofReal_integral_pow_eq_lintegral_rpow_of_ae_nonneg
      q (hXnonneg i hi) (hIntQ i hi)
  have hsumTwo :
      ENNReal.ofReal (∑ i ∈ s, ∫ omega, X i omega ^ 2 ∂mu) =
        ∑ i ∈ s,
          ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (2 : ℝ) ∂mu := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => hmomentNonneg 2 i hi)]
    exact Finset.sum_congr rfl htwo
  have hsumK :
      ENNReal.ofReal (∑ i ∈ s, ∫ omega, X i omega ^ k ∂mu) =
        ∑ i ∈ s,
          ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (k : ℝ) ∂mu := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => hmomentNonneg k i hi)]
    exact Finset.sum_congr rfl hkMoment
  have hsumQ :
      ENNReal.ofReal (∑ i ∈ s, ∫ omega, X i omega ^ q ∂mu) =
        ∑ i ∈ s,
          ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (q : ℝ) ∂mu := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => hmomentNonneg q i hi)]
    exact Finset.sum_congr rfl hqMoment
  have hrhs :
      ENNReal.ofReal
          ((∑ i ∈ s, ∫ omega, X i omega ^ 2 ∂mu) ^ a *
            (∑ i ∈ s, ∫ omega, X i omega ^ q ∂mu) ^ b) =
        (∑ i ∈ s,
          ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (2 : ℝ) ∂mu) ^ a *
          (∑ i ∈ s,
            ∫⁻ omega, ENNReal.ofReal (X i omega) ^ (q : ℝ) ∂mu) ^ b := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hsumNonneg 2) a),
      ← ENNReal.ofReal_rpow_of_nonneg (hsumNonneg 2) ha,
      ← ENNReal.ofReal_rpow_of_nonneg (hsumNonneg q) hb,
      hsumTwo, hsumQ]
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (Real.rpow_nonneg (hsumNonneg 2) a)
    (Real.rpow_nonneg (hsumNonneg q) b))]
  rw [hsumK, hrhs]
  simpa [a, b] using hcore

/-- Interpolation with deterministic proxies `V` and `Q` for the sums of
second and `q`-th moments.  This is the precise form of Rio's Proposition
3.5 used in the subsequent MGF optimization.
@isnad1 id=le.12h9v.s8.c5abd29bce9e from=translated src=- shape=2475656f vocab=25c932cd
-/
theorem sum_integral_pow_le_strongMomentInterpolation_of_le
    {ι Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (s : Finset ι) (X : ι → Omega → ℝ)
    {q k : ℕ} (hq : 3 ≤ q) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) mu)
    (hXnonneg : ∀ i ∈ s, 0 ≤ᵐ[mu] X i)
    (hIntTwo : ∀ i ∈ s, Integrable (fun omega => X i omega ^ 2) mu)
    (hIntK : ∀ i ∈ s, Integrable (fun omega => X i omega ^ k) mu)
    (hIntQ : ∀ i ∈ s, Integrable (fun omega => X i omega ^ q) mu)
    {V Q : ℝ} (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hSecond : (∑ i ∈ s, ∫ omega, X i omega ^ 2 ∂mu) ≤ V)
    (hQMoment : (∑ i ∈ s, ∫ omega, X i omega ^ q ∂mu) ≤ Q) :
    ∑ i ∈ s, ∫ omega, X i omega ^ k ∂mu ≤
      V ^ strongMomentSecondWeight q k *
        Q ^ strongMomentQWeight q k := by
  have ha : 0 ≤ strongMomentSecondWeight q k :=
    strongMomentSecondWeight_nonneg hkq hq
  have hb : 0 ≤ strongMomentQWeight q k :=
    strongMomentQWeight_nonneg hk hq
  have hbase := sum_integral_pow_le_strongMomentInterpolation
    mu s X hq hk hkq hX hXnonneg hIntTwo hIntK hIntQ
  refine hbase.trans ?_
  have _hVPowerNonneg :
      0 ≤ V ^ strongMomentSecondWeight q k :=
    Real.rpow_nonneg hV _
  have hmul := mul_le_mul
    (Real.rpow_le_rpow
      (Finset.sum_nonneg fun i hi => integral_nonneg_of_ae
        ((hXnonneg i hi).mono fun omega homega => pow_nonneg homega q))
      hQMoment hb)
    (Real.rpow_le_rpow
      (Finset.sum_nonneg fun i hi => integral_nonneg_of_ae
        ((hXnonneg i hi).mono fun omega homega => pow_nonneg homega 2))
      hSecond ha)
    (Real.rpow_nonneg
      (Finset.sum_nonneg fun i hi => integral_nonneg_of_ae
        ((hXnonneg i hi).mono fun omega homega => pow_nonneg homega 2))
      (strongMomentSecondWeight q k))
    (Real.rpow_nonneg hQ (strongMomentQWeight q k))
  simpa only [mul_comm] using hmul

/-- Specialization of the proxy interpolation theorem to positive parts.
This matches the one-sided moments appearing in the strong-moment Taylor
exponent.
@isnad1 id=le.11h9v.s8.76d4735ea75b from=translated src=- shape=f62ebd73 vocab=ce38c032
-/
theorem sum_integral_pow_max_zero_le_strongMomentInterpolation_of_le
    {ι Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (s : Finset ι) (D : ι → Omega → ℝ)
    {q k : ℕ} (hq : 3 ≤ q) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hD : ∀ i ∈ s, AEMeasurable (D i) mu)
    (hIntTwo : ∀ i ∈ s,
      Integrable (fun omega => (max (D i omega) 0) ^ 2) mu)
    (hIntK : ∀ i ∈ s,
      Integrable (fun omega => (max (D i omega) 0) ^ k) mu)
    (hIntQ : ∀ i ∈ s,
      Integrable (fun omega => (max (D i omega) 0) ^ q) mu)
    {V Q : ℝ} (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hSecond :
      (∑ i ∈ s, ∫ omega, (max (D i omega) 0) ^ 2 ∂mu) ≤ V)
    (hQMoment :
      (∑ i ∈ s, ∫ omega, (max (D i omega) 0) ^ q ∂mu) ≤ Q) :
    ∑ i ∈ s, ∫ omega, (max (D i omega) 0) ^ k ∂mu ≤
      V ^ strongMomentSecondWeight q k *
        Q ^ strongMomentQWeight q k := by
  apply sum_integral_pow_le_strongMomentInterpolation_of_le
    mu s (fun i omega => max (D i omega) 0)
      hq hk hkq
  · intro i hi
    exact (hD i hi).max aemeasurable_const
  · intro i hi
    exact ae_of_all mu fun omega => le_max_right (D i omega) 0
  · exact hIntTwo
  · exact hIntK
  · exact hIntQ
  · exact hV
  · exact hQ
  · exact hSecond
  · exact hQMoment

end ProbabilityTheory
