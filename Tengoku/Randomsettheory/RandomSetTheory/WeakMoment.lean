/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.CenteredProcessEnvelope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive weak moments

This file introduces the positive weak moment which occurs in maximal
Fuk--Nagaev inequalities.  For a real random variable `X` and a positive
integer `q`, we use the equivalent power form

`sup_{t ≥ 0} t^q * P(t < X)`

and take its `q`-th root.  Markov's inequality immediately embeds the strong
`L^q` space into this positive weak space.  In particular, this discharges
the elementary comparison `Lambda_q^+(X) ≤ ||X||_q` used when specializing
Marchina's maximal inequality; it does not assert that maximal inequality.
-/

open Real Set MeasureTheory
open scoped ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The `q`-th power of the positive weak moment of `X`.

Using nonnegative real thresholds makes the indexing set nonempty and avoids
irrelevant negative thresholds.  For `q > 0`, the threshold zero contributes
zero.-/
def positiveWeakMomentPower (X : Omega → ℝ) (q : ℕ)
    (mu : Measure Omega) : ℝ :=
  sSup (Set.range (fun t : ℝ≥0 ↦
    (t : ℝ) ^ q * mu.real {omega | (t : ℝ) < X omega}))

/-- Positive weak moment, in the normalization
`(sup_{t ≥ 0} t^q P(t < X))^(1/q)`.-/
def positiveWeakMoment (X : Omega → ℝ) (q : ℕ)
    (mu : Measure Omega) : ℝ :=
  positiveWeakMomentPower X q mu ^ ((q : ℝ)⁻¹)

/-- Each positive-tail term is bounded by the strong absolute moment.-/
theorem positiveTailPow_mul_measureReal_le_absoluteMoment
    [IsFiniteMeasure mu] (X : Omega → ℝ) {q : ℕ} (hq : 0 < q)
    (hXq : Integrable (fun omega ↦ |X omega| ^ q) mu)
    (t : ℝ≥0) :
    (t : ℝ) ^ q * mu.real {omega | (t : ℝ) < X omega} ≤
      absoluteMoment X q mu := by
  by_cases ht : (t : ℝ) = 0
  · simp [ht, hq.ne', absoluteMoment_nonneg X q mu]
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property (Ne.symm ht)
  have hsubset : {omega | (t : ℝ) < X omega} ⊆
      {omega | (t : ℝ) ≤ |X omega|} := by
    intro omega homega
    exact homega.le.trans (le_abs_self (X omega))
  have htail : mu.real {omega | (t : ℝ) < X omega} ≤
      absoluteMoment X q mu / (t : ℝ) ^ q := by
    exact (measureReal_mono hsubset (by finiteness)).trans
      (measureReal_abs_ge_le_absoluteMoment_div X q hXq htpos)
  calc
    (t : ℝ) ^ q * mu.real {omega | (t : ℝ) < X omega} ≤
        (t : ℝ) ^ q *
          (absoluteMoment X q mu / (t : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_left htail (pow_nonneg t.property q)
    _ = absoluteMoment X q mu := by
      field_simp [pow_ne_zero q ht]

/-- The powered positive weak moment is at most the strong absolute moment.-/
theorem positiveWeakMomentPower_le_absoluteMoment
    [IsFiniteMeasure mu] (X : Omega → ℝ) {q : ℕ} (hq : 0 < q)
    (hXq : Integrable (fun omega ↦ |X omega| ^ q) mu) :
    positiveWeakMomentPower X q mu ≤ absoluteMoment X q mu := by
  unfold positiveWeakMomentPower
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨t, rfl⟩
    exact positiveTailPow_mul_measureReal_le_absoluteMoment X hq hXq t

/-- Under a finite strong moment, the powered positive weak moment is
nonnegative.-/
theorem positiveWeakMomentPower_nonneg
    [IsFiniteMeasure mu] (X : Omega → ℝ) {q : ℕ} (hq : 0 < q)
    (hXq : Integrable (fun omega ↦ |X omega| ^ q) mu) :
    0 ≤ positiveWeakMomentPower X q mu := by
  unfold positiveWeakMomentPower
  have hbdd : BddAbove (Set.range (fun t : ℝ≥0 ↦
      (t : ℝ) ^ q * mu.real {omega | (t : ℝ) < X omega})) := by
    refine ⟨absoluteMoment X q mu, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact positiveTailPow_mul_measureReal_le_absoluteMoment X hq hXq t
  have hzero : (0 : ℝ) ∈ Set.range (fun t : ℝ≥0 ↦
      (t : ℝ) ^ q * mu.real {omega | (t : ℝ) < X omega}) := by
    refine ⟨0, ?_⟩
    simp [hq.ne']
  exact le_csSup hbdd hzero

/-- Strong `L^q` controls the positive weak moment.  This is the comparison
usually written `Lambda_q^+(X) ≤ ||X||_q`.-/
theorem positiveWeakMoment_le_lpNorm
    [IsFiniteMeasure mu] (X : Omega → ℝ) {q : ℕ} (hq : 0 < q)
    (hXq : MemLp X q mu) :
    positiveWeakMoment X q mu ≤ lpNorm X q mu := by
  have hInt : Integrable (fun omega ↦ |X omega| ^ q) mu := by
    simpa only [Real.norm_eq_abs] using hXq.integrable_norm_pow hq.ne'
  have hpowNonneg := positiveWeakMomentPower_nonneg X hq hInt
  have hpowLe := positiveWeakMomentPower_le_absoluteMoment
    X hq hInt
  have hexponent : 0 ≤ ((q : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg q)
  unfold positiveWeakMoment
  calc
    positiveWeakMomentPower X q mu ^ ((q : ℝ)⁻¹) ≤
        absoluteMoment X q mu ^ ((q : ℝ)⁻¹) :=
      Real.rpow_le_rpow hpowNonneg hpowLe hexponent
    _ = lpNorm X q mu := by
      rw [absoluteMoment_eq_lpNorm_pow X hq hXq]
      exact Real.pow_rpow_inv_natCast lpNorm_nonneg hq.ne'

/-- The centred envelope used in empirical-process inequalities has positive
weak moment at most twice that of the original strong envelope.-/
theorem positiveWeakMoment_centeredProcessEnvelope_le_two_mul
    [IsProbabilityMeasure mu] (A : Omega → ℝ) {q : ℕ} (hq : 1 ≤ q)
    (hAq : MemLp A q mu) :
    positiveWeakMoment (centeredProcessEnvelope A mu) q mu ≤
      2 * lpNorm A q mu := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  exact (positiveWeakMoment_le_lpNorm
    (centeredProcessEnvelope A mu) hqpos
      (memLp_centeredProcessEnvelope A hAq)).trans
    (lpNorm_centeredProcessEnvelope_le_two_mul A hq hAq)

/-- Numerical specialization of the centred-envelope weak-moment bound.-/
theorem positiveWeakMoment_centeredProcessEnvelope_le
    [IsProbabilityMeasure mu] (A : Omega → ℝ) {q : ℕ} (hq : 1 ≤ q)
    (hAq : MemLp A q mu) {K : ℝ}
    (hAnorm : lpNorm A q mu ≤ K) :
    positiveWeakMoment (centeredProcessEnvelope A mu) q mu ≤ 2 * K := by
  exact (positiveWeakMoment_centeredProcessEnvelope_le_two_mul A hq hAq).trans
    (mul_le_mul_of_nonneg_left hAnorm (by norm_num))

end ProbabilityTheory
