/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftRoot
import Tengoku.Seed.Data.Nat.ModEq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residue corrections for rational shifts

This file develops the quotient-and-residue decomposition of

`⌈(m - a / b)^q⌉`

and prepares the periodic correction terms used in the
Bernoulli-periodic formula.
-/

namespace RoundedRootSums

/--
The integer numerator occurring in the rational power

`(m - a / b)^q = (b * m - a)^q / b^q`.-/
def shiftedPowerNumerator
    (q a b m : Nat) : Nat :=
  (b * m - a) ^ q

/--
The common denominator `b^q` of the shifted q-th powers.-/
def shiftedPowerDenominator
    (q b : Nat) : Nat :=
  b ^ q

/--
The residue of `(b * m - a)^q` modulo `b^q`.-/
def shiftedPowerResidue
    (q a b m : Nat) : Nat :=
  shiftedPowerNumerator q a b m %
    shiftedPowerDenominator q b

/--
The ceiling correction attached to a residue.

It is zero when the shifted power is integral and one otherwise.-/
def shiftedResidueCorrection
    (q a b m : Nat) : Nat :=
  if shiftedPowerResidue q a b m = 0 then 0 else 1

/--
The quotient-plus-correction expression expected to equal

`⌈(m - a / b)^q⌉`.-/
def shiftedThresholdQuotient
    (q a b m : Nat) : Nat :=
  shiftedPowerNumerator q a b m /
      shiftedPowerDenominator q b +
    shiftedResidueCorrection q a b m

/--
The denominator `b^q` is positive whenever `b` is positive.
@isnad1 id=lt.1h2v.s4.77d3130c0331 from=translated src=- shape=61bdc3e7 vocab=e044170f
-/
theorem shiftedPowerDenominator_pos
    (q b : Nat)
    (hb : 0 < b) :
    0 < shiftedPowerDenominator q b := by
  unfold shiftedPowerDenominator
  exact pow_pos hb q

/--
The shifted power residue is strictly smaller than the
common denominator `b^q`.
@isnad1 id=lt.1h4v.s4.e2f4f273fb78 from=translated src=- shape=6354d690 vocab=3be6e6b9
-/
theorem shiftedPowerResidue_lt_denominator
    (q a b m : Nat)
    (hb : 0 < b) :
    shiftedPowerResidue q a b m <
      shiftedPowerDenominator q b := by
  unfold shiftedPowerResidue
  exact Nat.mod_lt _
    (shiftedPowerDenominator_pos q b hb)

/--
The residue correction vanishes exactly when the residue vanishes.
@isnad1 id=iff.0h4v.s5.1a02960167fe from=translated src=- shape=01c63260 vocab=41508124
-/
theorem shiftedResidueCorrection_eq_zero_iff
    (q a b m : Nat) :
    shiftedResidueCorrection q a b m = 0 ↔
      shiftedPowerResidue q a b m = 0 := by
  unfold shiftedResidueCorrection
  by_cases h :
      shiftedPowerResidue q a b m = 0
  · simp [h]
  · simp [h]

/--
The residue correction equals one exactly when the residue is nonzero.
@isnad1 id=iff.0h4v.s5.a639a4b8d483 from=translated src=- shape=d2e3800b vocab=41508124
-/
theorem shiftedResidueCorrection_eq_one_iff
    (q a b m : Nat) :
    shiftedResidueCorrection q a b m = 1 ↔
      shiftedPowerResidue q a b m ≠ 0 := by
  unfold shiftedResidueCorrection
  by_cases h :
      shiftedPowerResidue q a b m = 0
  · simp [h]
  · simp [h]

/--
The shifted power numerator decomposes into its residue
plus the denominator times the quotient.
@isnad1 id=eq.0h4v.s5.cd3b5d5f1dc5 from=translated src=- shape=20ef38d8 vocab=3dcd37d6
-/
theorem shiftedPowerResidue_add_denominator_mul_div
    (q a b m : Nat) :
    shiftedPowerResidue q a b m +
        shiftedPowerDenominator q b *
          (shiftedPowerNumerator q a b m /
            shiftedPowerDenominator q b) =
      shiftedPowerNumerator q a b m := by
  unfold shiftedPowerResidue
  exact Nat.mod_add_div
    (shiftedPowerNumerator q a b m)
    (shiftedPowerDenominator q b)

/--
The threshold quotient equals the ordinary quotient exactly
when the shifted power residue is zero.
@isnad1 id=iff.0h4v.s5.b6a9cc3487b3 from=translated src=- shape=f0e9a1a4 vocab=ecf605b7
-/
theorem shiftedThresholdQuotient_eq_div_iff
    (q a b m : Nat) :
    shiftedThresholdQuotient q a b m =
        shiftedPowerNumerator q a b m /
          shiftedPowerDenominator q b ↔
      shiftedPowerResidue q a b m = 0 := by
  unfold shiftedThresholdQuotient shiftedResidueCorrection
  by_cases h : shiftedPowerResidue q a b m = 0
  · simp [h]
  · simp [h]

/--
For a nonzero residue, the threshold quotient is the ordinary
quotient plus one.
@isnad1 id=iff.0h4v.s5.2c0ad95d99f6 from=translated src=- shape=e270bc54 vocab=c7506b18
-/
theorem shiftedThresholdQuotient_eq_div_add_one_iff
    (q a b m : Nat) :
    shiftedThresholdQuotient q a b m =
        shiftedPowerNumerator q a b m /
            shiftedPowerDenominator q b + 1 ↔
      shiftedPowerResidue q a b m ≠ 0 := by
  unfold shiftedThresholdQuotient shiftedResidueCorrection
  by_cases h : shiftedPowerResidue q a b m = 0
  · simp [h]
  · simp [h]

/--
The shifted rational q-th power is the quotient of the
integer numerator `(b * m - a)^q` by the denominator `b^q`.
@isnad1 id=eq.2h4v.s6.aeba5fdb8225 from=translated src=- shape=a294433f vocab=31348d9c
-/
theorem shiftedRationalPower_eq_num_div_den
    (q a b m : Nat)
    (hb : 0 < b)
    (ham : a ≤ b * m) :
    (((m : Rat) - (a : Rat) / (b : Rat)) ^ q) =
      (shiftedPowerNumerator q a b m : Rat) /
        (shiftedPowerDenominator q b : Rat) := by
  have hbRat : (b : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb)
  have hbase :
      (m : Rat) - (a : Rat) / (b : Rat) =
        ((b * m - a : Nat) : Rat) / (b : Rat) := by
    rw [Nat.cast_sub ham, Nat.cast_mul]
    field_simp [hbRat]
  rw [hbase]
  simp [shiftedPowerNumerator, shiftedPowerDenominator,
    div_pow, Nat.cast_sub ham]

/--
The natural shifted threshold is the natural ceiling of the
quotient `(b * m - a)^q / b^q`.
@isnad1 id=eq.2h4v.s6.d39a8121eb6d from=translated src=- shape=0177e494 vocab=9798d712
-/
theorem shiftedThresholdNat_eq_natCeil_num_div_den
    (q a b m : Nat)
    (hb : 0 < b)
    (ham : a ≤ b * m) :
    shiftedThresholdNat q a b m =
      ⌈(shiftedPowerNumerator q a b m : Rat) /
        (shiftedPowerDenominator q b : Rat)⌉₊ := by
  apply le_antisymm
  · apply
      (shiftedThresholdNat_le_iff
        q a b m
          ⌈(shiftedPowerNumerator q a b m : Rat) /
            (shiftedPowerDenominator q b : Rat)⌉₊
          hb ham).mpr
    rw [shiftedRationalPower_eq_num_div_den
      q a b m hb ham]
    exact Nat.le_ceil _
  · rw [Nat.ceil_le]
    rw [← shiftedRationalPower_eq_num_div_den
      q a b m hb ham]
    have hInt :
        shiftedThreshold q a b m ≤
          (shiftedThresholdNat q a b m : Int) := by
      rw [shiftedThresholdNat_cast
        q a b m hb ham]
    simpa [shiftedThreshold] using
      (Int.ceil_le.mp hInt)

/--
The natural ceiling of `N / D` equals the ordinary quotient,
plus one exactly when the remainder is nonzero.
@isnad1 id=eq.1h2v.s6.12bc2cc14365 from=translated src=- shape=dd16d41f vocab=7320a7bc
-/
theorem natCeil_natCast_div_natCast_eq_div_add_correction
    (N D : Nat)
    (hD : 0 < D) :
    ⌈(N : Rat) / (D : Rat)⌉₊ =
      N / D + if N % D = 0 then 0 else 1 := by
  have hD_rat : (0 : Rat) < (D : Rat) := by
    exact_mod_cast hD
  have hdecomp :
      N % D + (N / D) * D = N := by
    simpa [Nat.mul_comm] using
      (Nat.mod_add_div N D)
  by_cases hrem : N % D = 0
  · rw [ite_eq_left hrem, Nat.add_zero]
    have hmul :
        N = (N / D) * D := by
      omega
    have hD_ne : (D : Rat) ≠ 0 :=
      ne_of_gt hD_rat
    have hfrac :
        (N : Rat) / (D : Rat) =
          ((N / D : Nat) : Rat) := by
      apply (div_eq_iff hD_ne).2
      exact_mod_cast hmul
    rw [hfrac]
    simp
  · rw [ite_eq_right hrem]
    have hrpos :
        0 < N % D :=
      Nat.pos_of_ne_zero hrem
    have hrlt :
        N % D < D :=
      Nat.mod_lt N hD
    have hlower :
        (N / D) * D < N := by
      omega
    have hupper :
        N ≤ (N / D + 1) * D := by
      rw [Nat.add_mul, one_mul]
      omega
    apply le_antisymm
    · rw [Nat.ceil_le]
      apply (div_le_iff₀ hD_rat).2
      exact_mod_cast hupper
    · rw [Nat.succ_le_iff]
      rw [Nat.lt_ceil]
      apply (lt_div_iff₀ hD_rat).2
      exact_mod_cast hlower

/--
The natural shifted threshold is the ordinary quotient of
`(b * m - a)^q` by `b^q`, plus the residue correction.
@isnad1 id=eq.2h4v.s5.ad41ce4c37fa from=translated src=- shape=4a7532d4 vocab=f95774a7
-/
theorem shiftedThresholdNat_eq_thresholdQuotient
    (q a b m : Nat)
    (hb : 0 < b)
    (ham : a ≤ b * m) :
    shiftedThresholdNat q a b m =
      shiftedThresholdQuotient q a b m := by
  rw [shiftedThresholdNat_eq_natCeil_num_div_den
    q a b m hb ham]
  unfold shiftedThresholdQuotient
  unfold shiftedResidueCorrection
  unfold shiftedPowerResidue
  exact
    natCeil_natCast_div_natCast_eq_div_add_correction
      (shiftedPowerNumerator q a b m)
      (shiftedPowerDenominator q b)
      (shiftedPowerDenominator_pos q b hb)

/--
The sum of the ordinary quotient parts for levels `1, ..., t`.-/
def shiftedPowerQuotientSum
    (q a b t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun m =>
    shiftedPowerNumerator q a b (m + 1) /
      shiftedPowerDenominator q b)

/--
The sum of the residue corrections for levels `1, ..., t`.-/
def shiftedResidueCorrectionSum
    (q a b t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun m =>
    shiftedResidueCorrection q a b (m + 1))

/--
The shifted threshold sum splits into the ordinary quotient sum
and the sum of residue corrections.
@isnad1 id=eq.2h4v.s5.2e68f3372253 from=translated src=- shape=afac07d8 vocab=17203563
-/
theorem shiftedThresholdSum_eq_quotientSum_add_correctionSum
    (q a b t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedThresholdSum q a b t =
      shiftedPowerQuotientSum q a b t +
        shiftedResidueCorrectionSum q a b t := by
  unfold shiftedThresholdSum
  unfold shiftedPowerQuotientSum
  unfold shiftedResidueCorrectionSum
  calc
    Finset.sum (Finset.range t) (fun m =>
        shiftedThresholdNat q a b (m + 1)) =
      Finset.sum (Finset.range t) (fun m =>
        shiftedThresholdQuotient q a b (m + 1)) := by
      apply Finset.sum_congr rfl
      intro m _hm
      apply shiftedThresholdNat_eq_thresholdQuotient
      · exact hb
      · calc
          a ≤ b := Nat.le_of_lt ha
          _ = b * 1 := by simp
          _ ≤ b * (m + 1) :=
            Nat.mul_le_mul_left b
              (Nat.succ_le_succ (Nat.zero_le m))
    _ =
        Finset.sum (Finset.range t) (fun m =>
          shiftedPowerNumerator q a b (m + 1) /
            shiftedPowerDenominator q b) +
        Finset.sum (Finset.range t) (fun m =>
          shiftedResidueCorrection q a b (m + 1)) := by
      simp only [shiftedThresholdQuotient]
      rw [Finset.sum_add_distrib]

/--
Exact inversion with the threshold sum separated into
the ordinary quotient part and the residue-correction part.
@isnad1 id=eq.3h4v.s6.6291b52be2f1 from=translated src=- shape=8c15d652 vocab=b99e2aa5
-/
theorem shiftedRealRoundedSum_residue_formula
    (q a b n : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRealRoundedSum q a b n =
      shiftedRealRoundedValue q a b n * (n + 1) -
        (shiftedPowerQuotientSum q a b
            (shiftedRealRoundedValue q a b n) +
          shiftedResidueCorrectionSum q a b
            (shiftedRealRoundedValue q a b n)) := by
  calc
    shiftedRealRoundedSum q a b n =
        shiftedRealRoundedValue q a b n * (n + 1) -
          shiftedThresholdSum q a b
            (shiftedRealRoundedValue q a b n) :=
      shiftedRealRoundedSum_explicit_formula
        q a b n hq hb ha
    _ =
        shiftedRealRoundedValue q a b n * (n + 1) -
          (shiftedPowerQuotientSum q a b
              (shiftedRealRoundedValue q a b n) +
            shiftedResidueCorrectionSum q a b
              (shiftedRealRoundedValue q a b n)) := by
      rw [shiftedThresholdSum_eq_quotientSum_add_correctionSum
        q a b (shiftedRealRoundedValue q a b n) hb ha]

/--
A natural period candidate for the rational-shift residue sequence.

Shifting `m` by `b^(q - 1)` changes `b * m - a`
by a multiple of `b^q`.-/
def shiftedResiduePeriod
    (q b : Nat) : Nat :=
  b ^ (q - 1)

/--
The period candidate multiplied by `b` equals the common
denominator `b^q`, provided `q` is positive.
@isnad1 id=eq.1h2v.s4.574a72fb8ccc from=translated src=- shape=ee6803e8 vocab=ea3e9526
-/
theorem shiftedResiduePeriod_mul_base
    (q b : Nat)
    (hq : 0 < q) :
    shiftedResiduePeriod q b * b =
      shiftedPowerDenominator q b := by
  have h1q : 1 ≤ q :=
    Nat.succ_le_iff.mpr hq
  have hqSplit :
      q - 1 + 1 = q :=
    Nat.sub_add_cancel h1q
  unfold shiftedResiduePeriod
  unfold shiftedPowerDenominator
  calc
    b ^ (q - 1) * b =
        b ^ ((q - 1) + 1) := by
      symm
      exact pow_succ b (q - 1)
    _ = b ^ q := by
      rw [hqSplit]

/--
The sum of the residue corrections over one candidate period.-/
def shiftedResidueCorrectionPeriodSum
    (q a b : Nat) : Nat :=
  Finset.sum
    (Finset.range (shiftedResiduePeriod q b))
    (fun r =>
      shiftedResidueCorrection q a b (r + 1))

/--
Shifting a positive level by `b^(q - 1)` preserves the residue
of `(b * m - a)^q` modulo `b^q`.
@isnad1 id=eq.2h4v.s6.ce6772e02d6d from=translated src=- shape=4a141ea7 vocab=ce20ee17
-/
theorem shiftedPowerResidue_add_period
    (q a b m : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedPowerResidue q a b
        (m + 1 + shiftedResiduePeriod q b) =
      shiftedPowerResidue q a b (m + 1) := by
  have hright :
      a ≤ b * (m + 1) := by
    calc
      a ≤ b := Nat.le_of_lt ha
      _ = b * 1 := by simp
      _ ≤ b * (m + 1) :=
        Nat.mul_le_mul_left b
          (Nat.succ_le_succ (Nat.zero_le m))
  have hleft :
      a ≤
        b * (m + 1 + shiftedResiduePeriod q b) := by
    exact le_trans hright
      (Nat.mul_le_mul_left b
        (Nat.le_add_right
          (m + 1) (shiftedResiduePeriod q b)))
  have hbaseMod :
      b * (m + 1 + shiftedResiduePeriod q b) ≡
        b * (m + 1)
          [MOD shiftedPowerDenominator q b] := by
    rw [Nat.mul_add]
    rw [Nat.mul_comm b (shiftedResiduePeriod q b)]
    rw [shiftedResiduePeriod_mul_base q b hq]
    exact Nat.add_modEq_right
  have hsubMod :
      b * (m + 1 + shiftedResiduePeriod q b) - a ≡
        b * (m + 1) - a
          [MOD shiftedPowerDenominator q b] :=
    Nat.ModEq.sub_right hleft hright hbaseMod
  have hpowMod :
      (b * (m + 1 + shiftedResiduePeriod q b) - a) ^ q ≡
        (b * (m + 1) - a) ^ q
          [MOD shiftedPowerDenominator q b] :=
    Nat.ModEq.pow q hsubMod
  unfold shiftedPowerResidue shiftedPowerNumerator
  exact hpowMod

/--
The residue correction is periodic with period `b^(q - 1)`.
@isnad1 id=eq.2h4v.s6.0d7570b1f6dc from=translated src=- shape=4a141ea7 vocab=7221e8b3
-/
theorem shiftedResidueCorrection_add_period
    (q a b m : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedResidueCorrection q a b
        (m + 1 + shiftedResiduePeriod q b) =
      shiftedResidueCorrection q a b (m + 1) := by
  unfold shiftedResidueCorrection
  rw [shiftedPowerResidue_add_period
    q a b m hq ha]

/--
The residue-correction sequence indexed from zero.

Index `r` corresponds to the positive level `r + 1`.-/
def shiftedResidueCorrectionAt
    (q a b r : Nat) : Nat :=
  shiftedResidueCorrection q a b (r + 1)

/--
The zero-indexed residue-correction sequence is periodic
with period `b^(q - 1)`.
@isnad1 id=eq.2h4v.s5.a20b23c553ce from=translated src=- shape=ac749cea vocab=5a7b713c
-/
theorem shiftedResidueCorrectionAt_add_period
    (q a b r : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedResidueCorrectionAt q a b
        (shiftedResiduePeriod q b + r) =
      shiftedResidueCorrectionAt q a b r := by
  unfold shiftedResidueCorrectionAt
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (shiftedResidueCorrection_add_period
      q a b r hq ha)

/--
Adding one complete period adds exactly the correction sum
over one period.
@isnad1 id=eq.2h4v.s5.571149ad347a from=translated src=- shape=354c3027 vocab=b2b0409d
-/
theorem shiftedResidueCorrectionSum_period_add
    (q a b t : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedResidueCorrectionSum q a b
        (shiftedResiduePeriod q b + t) =
      shiftedResidueCorrectionPeriodSum q a b +
        shiftedResidueCorrectionSum q a b t := by
  unfold shiftedResidueCorrectionSum
  unfold shiftedResidueCorrectionPeriodSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (shiftedResidueCorrection_add_period
      q a b r hq ha)

/--
The correction sum over `s` complete periods followed by
an additional initial segment of length `r`.
@isnad1 id=eq.2h5v.s6.a92501473ce7 from=translated src=- shape=88ff1eb7 vocab=68fc0fea
-/
theorem shiftedResidueCorrectionSum_mul_period_add
    (q a b s r : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedResidueCorrectionSum q a b
        (s * shiftedResiduePeriod q b + r) =
      s * shiftedResidueCorrectionPeriodSum q a b +
        shiftedResidueCorrectionSum q a b r := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      calc
        shiftedResidueCorrectionSum q a b
            (Nat.succ s * shiftedResiduePeriod q b + r) =
          shiftedResidueCorrectionSum q a b
            (shiftedResiduePeriod q b +
              (s * shiftedResiduePeriod q b + r)) := by
            congr 1
            rw [Nat.succ_mul]
            ac_rfl
        _ =
          shiftedResidueCorrectionPeriodSum q a b +
            shiftedResidueCorrectionSum q a b
              (s * shiftedResiduePeriod q b + r) :=
          shiftedResidueCorrectionSum_period_add
            q a b
              (s * shiftedResiduePeriod q b + r)
              hq ha
        _ =
          shiftedResidueCorrectionPeriodSum q a b +
            (s * shiftedResidueCorrectionPeriodSum q a b +
              shiftedResidueCorrectionSum q a b r) := by
            rw [ih]
        _ =
          Nat.succ s *
              shiftedResidueCorrectionPeriodSum q a b +
            shiftedResidueCorrectionSum q a b r := by
            rw [Nat.succ_mul]
            ac_rfl

/--
The residue-correction sum decomposes into complete periods
and the remaining initial segment.
@isnad1 id=eq.2h4v.s6.1c2696020b87 from=translated src=- shape=e72eef5c vocab=21882c20
-/
theorem shiftedResidueCorrectionSum_div_mod
    (q a b t : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedResidueCorrectionSum q a b t =
      (t / shiftedResiduePeriod q b) *
          shiftedResidueCorrectionPeriodSum q a b +
        shiftedResidueCorrectionSum q a b
          (t % shiftedResiduePeriod q b) := by
  have hdecomp :
      (t / shiftedResiduePeriod q b) *
          shiftedResiduePeriod q b +
        t % shiftedResiduePeriod q b = t := by
    calc
      (t / shiftedResiduePeriod q b) *
            shiftedResiduePeriod q b +
          t % shiftedResiduePeriod q b =
        t % shiftedResiduePeriod q b +
          shiftedResiduePeriod q b *
            (t / shiftedResiduePeriod q b) := by
          ac_rfl
      _ = t :=
        Nat.mod_add_div t (shiftedResiduePeriod q b)
  calc
    shiftedResidueCorrectionSum q a b t =
        shiftedResidueCorrectionSum q a b
          ((t / shiftedResiduePeriod q b) *
              shiftedResiduePeriod q b +
            t % shiftedResiduePeriod q b) := by
      rw [hdecomp]
    _ =
        (t / shiftedResiduePeriod q b) *
            shiftedResidueCorrectionPeriodSum q a b +
          shiftedResidueCorrectionSum q a b
            (t % shiftedResiduePeriod q b) :=
      shiftedResidueCorrectionSum_mul_period_add
        q a b
          (t / shiftedResiduePeriod q b)
          (t % shiftedResiduePeriod q b)
          hq ha

/--
The residue period `b^(q - 1)` is positive whenever `b` is positive.
@isnad1 id=lt.1h2v.s4.7ada1787f544 from=translated src=- shape=61bdc3e7 vocab=2ef8e97f
-/
theorem shiftedResiduePeriod_pos
    (q b : Nat)
    (hb : 0 < b) :
    0 < shiftedResiduePeriod q b := by
  unfold shiftedResiduePeriod
  exact pow_pos hb (q - 1)

/--
The remaining segment in the division decomposition is strictly
shorter than one complete residue period.
@isnad1 id=lt.1h3v.s5.db8a53761960 from=translated src=- shape=a29d542b vocab=d4420864
-/
theorem shiftedResidueRemainder_lt_period
    (q b t : Nat)
    (hb : 0 < b) :
    t % shiftedResiduePeriod q b <
      shiftedResiduePeriod q b := by
  exact Nat.mod_lt t
    (shiftedResiduePeriod_pos q b hb)

/--
Exact inversion with the residue correction decomposed into
complete periods and a final incomplete period.
@isnad1 id=eq.3h4v.s7.f76234ff0d4f from=translated src=- shape=5d64475a vocab=b5d48dc7
-/
theorem shiftedRealRoundedSum_periodic_residue_formula
    (q a b n : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRealRoundedSum q a b n =
      shiftedRealRoundedValue q a b n * (n + 1) -
        (shiftedPowerQuotientSum q a b
            (shiftedRealRoundedValue q a b n) +
          ((shiftedRealRoundedValue q a b n /
                shiftedResiduePeriod q b) *
              shiftedResidueCorrectionPeriodSum q a b +
            shiftedResidueCorrectionSum q a b
              (shiftedRealRoundedValue q a b n %
                shiftedResiduePeriod q b))) := by
  calc
    shiftedRealRoundedSum q a b n =
        shiftedRealRoundedValue q a b n * (n + 1) -
          (shiftedPowerQuotientSum q a b
              (shiftedRealRoundedValue q a b n) +
            shiftedResidueCorrectionSum q a b
              (shiftedRealRoundedValue q a b n)) :=
      shiftedRealRoundedSum_residue_formula
        q a b n hq hb ha
    _ =
        shiftedRealRoundedValue q a b n * (n + 1) -
          (shiftedPowerQuotientSum q a b
              (shiftedRealRoundedValue q a b n) +
            ((shiftedRealRoundedValue q a b n /
                  shiftedResiduePeriod q b) *
                shiftedResidueCorrectionPeriodSum q a b +
              shiftedResidueCorrectionSum q a b
                (shiftedRealRoundedValue q a b n %
                  shiftedResiduePeriod q b))) := by
      rw [shiftedResidueCorrectionSum_div_mod
        q a b
          (shiftedRealRoundedValue q a b n)
          hq ha]

/--
Every residue correction is at most one.
@isnad1 id=le.0h4v.s4.681771c492e9 from=translated src=- shape=e9751f0b vocab=54d8d8d5
-/
theorem shiftedResidueCorrection_le_one
    (q a b m : Nat) :
    shiftedResidueCorrection q a b m ≤ 1 := by
  unfold shiftedResidueCorrection
  split_ifs <;> simp

/--
The sum of the first `t` residue corrections is at most `t`.
@isnad1 id=le.0h4v.s4.667397cd0dce from=translated src=- shape=fc089d5d vocab=177c80b1
-/
theorem shiftedResidueCorrectionSum_le
    (q a b t : Nat) :
    shiftedResidueCorrectionSum q a b t ≤ t := by
  unfold shiftedResidueCorrectionSum
  calc
    Finset.sum (Finset.range t) (fun m =>
        shiftedResidueCorrection q a b (m + 1)) ≤
      Finset.sum (Finset.range t) (fun _m => 1) := by
        apply Finset.sum_le_sum
        intro m _hm
        exact shiftedResidueCorrection_le_one
          q a b (m + 1)
    _ = t := by
      simp

/--
The incomplete-period residue correction appearing after
division by the full period.-/
def shiftedResiduePeriodicRemainder
    (q a b t : Nat) : Nat :=
  shiftedResidueCorrectionSum q a b
    (t % shiftedResiduePeriod q b)

/--
The incomplete-period correction is strictly smaller than
one full period.
@isnad1 id=lt.1h4v.s4.1e8855d6d5ca from=translated src=- shape=6354d690 vocab=a2ac7785
-/
theorem shiftedResiduePeriodicRemainder_lt_period
    (q a b t : Nat)
    (hb : 0 < b) :
    shiftedResiduePeriodicRemainder q a b t <
      shiftedResiduePeriod q b := by
  unfold shiftedResiduePeriodicRemainder
  exact lt_of_le_of_lt
    (shiftedResidueCorrectionSum_le
      q a b (t % shiftedResiduePeriod q b))
    (shiftedResidueRemainder_lt_period
      q b t hb)

/--
Exact inversion with a linear complete-period correction and
a bounded incomplete-period remainder.
@isnad1 id=eq.3h4v.s7.1823f4d24532 from=translated src=- shape=a6b6c967 vocab=041ab9a1
-/
theorem shiftedRealRoundedSum_bounded_periodic_formula
    (q a b n : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRealRoundedSum q a b n =
      shiftedRealRoundedValue q a b n * (n + 1) -
        (shiftedPowerQuotientSum q a b
            (shiftedRealRoundedValue q a b n) +
          ((shiftedRealRoundedValue q a b n /
                shiftedResiduePeriod q b) *
              shiftedResidueCorrectionPeriodSum q a b +
            shiftedResiduePeriodicRemainder q a b
              (shiftedRealRoundedValue q a b n))) := by
  unfold shiftedResiduePeriodicRemainder
  exact shiftedRealRoundedSum_periodic_residue_formula
    q a b n hq hb ha

end RoundedRootSums
