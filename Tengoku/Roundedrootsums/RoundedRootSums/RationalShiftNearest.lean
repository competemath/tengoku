/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftBernoulli
import Tengoku.Seed.Data.Nat.ModEq
import Tengoku.Seed.NumberTheory.Multiplicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nearest integer q-th root sums

This file specializes the rational-shift theory to the half shift
`a / b = 1 / 2`, corresponding to nearest-integer rounding of
positive real q-th roots.

It also introduces the residue sequence

`ρ_q(m) = (2 * m - 1)^q mod 2^q`

and the associated rational correction sequence

`ω_q(m) = 1 - ρ_q(m) / 2^q`.

The file begins the study of their exact periods.
-/

namespace RoundedRootSums

/--
The nearest-integer rounded real q-th root of `k`,
implemented by adding `1 / 2` and taking the natural floor.-/
noncomputable def nearestQRootValue
    (q k : Nat) : Nat :=
  shiftedRealRoundedValue q 1 2 k

/--
The sum of nearest-integer rounded real q-th roots
over `k = 1, ..., n`.-/
noncomputable def nearestQRootSum
    (q n : Nat) : Nat :=
  shiftedRealRoundedSum q 1 2 n

/--
The general Bernoulli-periodic theorem specialized to
nearest-integer q-th root sums.
@isnad1 id=eq.1h2v.s5.dca3baa0d269 from=translated src=- shape=0805075f vocab=e04867e6
-/
theorem nearestQRootSum_cast_rat_eq_periodicBernoulli
    (q n : Nat)
    (hq : 0 < q) :
    (nearestQRootSum q n : Rat) =
      shiftedRealRoundedSumBernoulliPeriodic q 1 2 n := by
  unfold nearestQRootSum
  exact shiftedRealRoundedSum_cast_rat_eq_periodicBernoulli
    q 1 2 n hq (by decide) (by decide)

/--
The natural general period candidate for the half-shift
residue sequences.-/
def nearestQResiduePeriod
    (q : Nat) : Nat :=
  shiftedResiduePeriod q 2

/--
For the half shift, the general residue period candidate is
`2^(q - 1)`.
@isnad1 id=eq.0h1v.s5.d7d8001d5cdf from=translated src=- shape=c66b077f vocab=7b424e39
-/
theorem nearestQResiduePeriod_eq
    (q : Nat) :
    nearestQResiduePeriod q = 2 ^ (q - 1) := by
  rfl

/--
The general nearest-root residue period candidate is positive.
@isnad1 id=lt.0h1v.s3.cebd5224e9c3 from=translated src=- shape=8a62b088 vocab=615b1c36
-/
theorem nearestQResiduePeriod_pos
    (q : Nat) :
    0 < nearestQResiduePeriod q := by
  unfold nearestQResiduePeriod
  exact shiftedResiduePeriod_pos q 2 (by decide)

/--
The power-residue sequence

`ρ_q(m) = (2 * m - 1)^q mod 2^q`,

indexed from zero. The index `r` here corresponds to the positive
article index `m = r + 1`.-/
def nearestQPowerResidueAt
    (q r : Nat) : Nat :=
  shiftedPowerResidue q 1 2 (r + 1)

/--
The half-shift power-residue sequence is periodic with
the general candidate period `2^(q - 1)`.
@isnad1 id=eq.1h2v.s4.ca5caed5c507 from=translated src=- shape=de493d70 vocab=098e87f1
-/
theorem nearestQPowerResidueAt_add_period
    (q r : Nat)
    (hq : 0 < q) :
    nearestQPowerResidueAt q
        (r + nearestQResiduePeriod q) =
      nearestQPowerResidueAt q r := by
  unfold nearestQPowerResidueAt
  unfold nearestQResiduePeriod
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (shiftedPowerResidue_add_period
      q 1 2 r hq (by decide))

/--
The rational correction sequence

`ω_q(m) = 1 - ρ_q(m) / 2^q`.

The index `r` here corresponds to the positive article index
`m = r + 1`.-/
def nearestQOmegaAt
    (q r : Nat) : Rat :=
  1 -
    (nearestQPowerResidueAt q r : Rat) /
      ((2 : Rat) ^ q)

/--
The half-shift correction sequence `ω_q` has the guaranteed
period `2^(q - 1)`.
@isnad1 id=eq.1h2v.s4.5fe162128a72 from=translated src=- shape=ef90cc8b vocab=0b781839
-/
theorem nearestQOmegaAt_add_period
    (q r : Nat)
    (hq : 0 < q) :
    nearestQOmegaAt q
        (r + nearestQResiduePeriod q) =
      nearestQOmegaAt q r := by
  unfold nearestQOmegaAt
  rw [nearestQPowerResidueAt_add_period q r hq]

/--
`P` is the least positive natural period of the sequence `f`.-/
def IsLeastPositiveNatPeriod
    {α : Type*}
    (f : Nat → α)
    (P : Nat) : Prop :=
  0 < P ∧
    Function.Periodic f P ∧
    ∀ d : Nat,
      0 < d →
      Function.Periodic f d →
      P ≤ d

/--
The residue sequence `ρ_q` is periodic with the general
candidate period `2^(q - 1)`.
@isnad1 id=periodic.1h1v.s4.cb1467d1ef75 from=translated src=- shape=fc6cdde2 vocab=97128418
-/
theorem nearestQPowerResidueAt_periodic
    (q : Nat)
    (hq : 0 < q) :
    Function.Periodic
      (nearestQPowerResidueAt q)
      (nearestQResiduePeriod q) := by
  intro r
  exact nearestQPowerResidueAt_add_period q r hq

/--
The rational correction sequence `ω_q` is periodic with the
same general candidate period.
@isnad1 id=periodic.1h1v.s4.a32752a641c5 from=translated src=- shape=26fcee47 vocab=86c57ba7
-/
theorem nearestQOmegaAt_periodic
    (q : Nat)
    (hq : 0 < q) :
    Function.Periodic
      (nearestQOmegaAt q)
      (nearestQResiduePeriod q) := by
  intro r
  exact nearestQOmegaAt_add_period q r hq

/--
A natural number `d` is a period of the residue sequence `ρ_q`
if of the residue sequence `ρ_q`
if and only if it is a period of the correction sequence `ω_q`.
@isnad1 id=iff.0h2v.s4.93a5ddc3f1bf from=translated src=- shape=c09a0554 vocab=680e7887
-/
theorem nearestQPowerResidueAt_periodic_iff_omega
    (q d : Nat) :
    Function.Periodic
        (nearestQPowerResidueAt q) d ↔
      Function.Periodic
        (nearestQOmegaAt q) d := by
  constructor
  · intro hResidue r
    unfold nearestQOmegaAt
    rw [hResidue r]
  · intro hOmega r
    have h :=
      hOmega r
    unfold nearestQOmegaAt at h
    have hden :
        ((2 : Rat) ^ q) ≠ 0 := by
      positivity
    have hcast :
        (nearestQPowerResidueAt q (r + d) : Rat) =
          (nearestQPowerResidueAt q r : Rat) := by
      field_simp [hden] at h
      linarith
    exact_mod_cast hcast

/--
The residue sequence `ρ_q` and the correction sequence `ω_q`
have the same least positive periods.
@isnad1 id=iff.0h2v.s3.c60e600b4a7e from=translated src=- shape=27c9db62 vocab=7899911d
-/
theorem nearestQPowerResidueAt_isLeastPeriod_iff_omega
    (q P : Nat) :
    IsLeastPositiveNatPeriod
        (nearestQPowerResidueAt q) P ↔
      IsLeastPositiveNatPeriod
        (nearestQOmegaAt q) P := by
  unfold IsLeastPositiveNatPeriod
  constructor
  · rintro ⟨hPpos, hPperiod, hPmin⟩
    refine ⟨
      hPpos,
      (nearestQPowerResidueAt_periodic_iff_omega
        q P).1 hPperiod,
      ?_
    ⟩
    intro d hdpos hdperiod
    exact hPmin d hdpos
      ((nearestQPowerResidueAt_periodic_iff_omega
        q d).2 hdperiod)
  · rintro ⟨hPpos, hPperiod, hPmin⟩
    refine ⟨
      hPpos,
      (nearestQPowerResidueAt_periodic_iff_omega
        q P).2 hPperiod,
      ?_
    ⟩
    intro d hdpos hdperiod
    exact hPmin d hdpos
      ((nearestQPowerResidueAt_periodic_iff_omega
        q d).1 hdperiod)

/--
The nearest-root residue sequence has the explicit form

`ρ_q(r) = (2 * r + 1)^q mod 2^q`.
@isnad1 id=eq.0h2v.s6.75eab1cd925f from=translated src=- shape=39f72b12 vocab=08c09392
-/
theorem nearestQPowerResidueAt_eq_oddPowerMod
    (q r : Nat) :
    nearestQPowerResidueAt q r =
      (2 * r + 1) ^ q % 2 ^ q := by
  unfold nearestQPowerResidueAt
  unfold shiftedPowerResidue
  unfold shiftedPowerNumerator
  unfold shiftedPowerDenominator
  have hbase :
      2 * (r + 1) - 1 = 2 * r + 1 := by
    omega
  rw [hbase]

/--
For every positive exponent, the initial residue is one.
@isnad1 id=eq.1h1v.s4.9fa3f6a74f10 from=translated src=- shape=cb752352 vocab=6c7f30b0
-/
theorem nearestQPowerResidueAt_zero
    (q : Nat)
    (hq : 0 < q) :
    nearestQPowerResidueAt q 0 = 1 := by
  rw [nearestQPowerResidueAt_eq_oddPowerMod]
  have hlt :
      1 < 2 ^ q := by
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hq)
  simpa using
    (Nat.mod_eq_of_lt hlt)

/--
Every period `d` of `ρ_q` satisfies

`(2 * d + 1)^q ≡ 1 mod 2^q`.
@isnad1 id=modeq.2h2v.s6.0b74f3dbc392 from=translated src=- shape=0103c105 vocab=e3bf1c7f
-/
theorem nearestQPowerResidueAt_period_implies_modEq_one
    (q d : Nat)
    (hq : 0 < q)
    (hperiod :
      Function.Periodic
        (nearestQPowerResidueAt q) d) :
    Nat.ModEq
      (2 ^ q)
      ((2 * d + 1) ^ q)
      1 := by
  have hAtZero :
      nearestQPowerResidueAt q d =
        nearestQPowerResidueAt q 0 := by
    simpa using hperiod 0
  have hResidue :
      nearestQPowerResidueAt q d = 1 := by
    calc
      nearestQPowerResidueAt q d =
          nearestQPowerResidueAt q 0 :=
        hAtZero
      _ = 1 :=
        nearestQPowerResidueAt_zero q hq
  rw [nearestQPowerResidueAt_eq_oddPowerMod] at hResidue
  change
    ((2 * d + 1) ^ q) % (2 ^ q) =
      1 % (2 ^ q)
  have hlt :
      1 < 2 ^ q := by
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hq)
  rw [Nat.mod_eq_of_lt hlt]
  exact hResidue

/--
Every period `d` of `ρ_q` satisfies

`2^q ∣ (2 * d + 1)^q - 1`.
@isnad1 id=dvd.2h2v.s6.240a6477d63c from=translated src=- shape=45aa81a5 vocab=bb0a2ebd
-/
theorem nearestQPowerResidueAt_period_implies_pow_dvd_sub_one
    (q d : Nat)
    (hq : 0 < q)
    (hperiod :
      Function.Periodic
        (nearestQPowerResidueAt q) d) :
    2 ^ q ∣ (2 * d + 1) ^ q - 1 := by
  have hmod :=
    nearestQPowerResidueAt_period_implies_modEq_one
      q d hq hperiod
  have hle :
      1 ≤ (2 * d + 1) ^ q := by
    exact Nat.one_le_pow' q (2 * d)
  exact
    (Nat.modEq_iff_dvd' hle).1 hmod.symm

/--
The odd base appearing in the period condition is greater than one
whenever the candidate period is positive.
@isnad1 id=lt.1h1v.s5.386ec81c7048 from=translated src=- shape=0539bd03 vocab=304a85f3
-/
theorem nearestQOddBase_gt_one
    (d : Nat)
    (hd : 0 < d) :
    1 < 2 * d + 1 := by
  omega

/--
The odd base differs from one by exactly `2 * d`.
@isnad1 id=eq.0h1v.s5.88eb5ce79f04 from=translated src=- shape=7cc96f5c vocab=5a86663e
-/
theorem nearestQOddBase_sub_one
    (d : Nat) :
    (2 * d + 1) - 1 = 2 * d := by
  omega

/--
The base `2 * d + 1` is odd.
@isnad1 id=not.0h1v.s5.48b30c5d10f2 from=translated src=- shape=2ec9f39c vocab=e4d01d9c
-/
theorem nearestQOddBase_not_two_dvd
    (d : Nat) :
    ¬2 ∣ 2 * d + 1 := by
  exact Nat.two_not_dvd_two_mul_add_one d

/--
The geometric factor in the factorization

`(2 * d + 1)^q - 1 =
  (2 * d) * (1 + (2 * d + 1) + ... + (2 * d + 1)^(q - 1))`.-/
def nearestQGeomSum
    (q d : Nat) : Nat :=
  Finset.sum (Finset.range q) (fun i =>
    (2 * d + 1) ^ i)

/--
The geometric factorization of `(2 * d + 1)^q - 1`.
@isnad1 id=eq.0h2v.s6.cad4708b6cdc from=translated src=- shape=169d7463 vocab=1cdaf6a5
-/
theorem nearestQGeomSum_mul_two_mul
    (q d : Nat) :
    nearestQGeomSum q d * (2 * d) =
      (2 * d + 1) ^ q - 1 := by
  unfold nearestQGeomSum
  simpa [nearestQOddBase_sub_one] using
    (geom_sum_mul_of_one_le
      (R := Nat)
      (x := 2 * d + 1)
      (by omega)
      q)

/--
Modulo two, the geometric sum has the same residue as
the number `q` of its terms.
@isnad1 id=eq.0h2v.s5.119a6c3370c0 from=translated src=- shape=bf52afae vocab=27a6b185
-/
theorem nearestQGeomSum_mod_two
    (q d : Nat) :
    nearestQGeomSum q d % 2 = q % 2 := by
  unfold nearestQGeomSum
  rw [Finset.sum_nat_mod]
  have hbase :
      (2 * d + 1) % 2 = 1 := by
    omega
  simp [Nat.pow_mod, hbase]

/--
For odd `q`, the geometric factor is odd.
@isnad1 id=not.1h2v.s4.51932d98b75a from=translated src=- shape=4999ec08 vocab=d72d2de9
-/
theorem nearestQGeomSum_not_two_dvd
    (q d : Nat)
    (hqOdd : Odd q) :
    ¬2 ∣ nearestQGeomSum q d := by
  rw [Nat.two_dvd_ne_zero]
  rw [nearestQGeomSum_mod_two]
  exact Nat.odd_iff.mp hqOdd

/--
For odd `q`, every period `d` forces `2^q` to divide `2 * d`.
@isnad1 id=dvd.3h2v.s5.8bcb23f631b1 from=translated src=- shape=01ed1fa2 vocab=19b8343c
-/
theorem nearestQPowerResidueAt_odd_period_implies_pow_dvd_two_mul
    (q d : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q)
    (hperiod :
      Function.Periodic
        (nearestQPowerResidueAt q) d) :
    2 ^ q ∣ 2 * d := by
  have hpow :
      2 ^ q ∣ (2 * d + 1) ^ q - 1 :=
    nearestQPowerResidueAt_period_implies_pow_dvd_sub_one
      q d hq hperiod
  have hproduct :
      2 ^ q ∣ nearestQGeomSum q d * (2 * d) := by
    rw [nearestQGeomSum_mul_two_mul]
    exact hpow
  have hcoprimeTwo :
      Nat.Coprime 2 (nearestQGeomSum q d) := by
    exact
      (Nat.prime_two.coprime_iff_not_dvd).2
        (nearestQGeomSum_not_two_dvd q d hqOdd)
  have hcoprimePow :
      Nat.Coprime (2 ^ q) (nearestQGeomSum q d) :=
    hcoprimeTwo.pow_left q
  exact hcoprimePow.dvd_of_dvd_mul_left hproduct

/--
For odd `q`, every positive period of `ρ_q` is divisible by
the candidate period `2^(q - 1)`.
@isnad1 id=dvd.3h2v.s5.1b488bbf553c from=translated src=- shape=bb984aca vocab=fe8eb826
-/
theorem nearestQResiduePeriod_dvd_of_odd_period
    (q d : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q)
    (hperiod :
      Function.Periodic
        (nearestQPowerResidueAt q) d) :
    nearestQResiduePeriod q ∣ d := by
  rw [nearestQResiduePeriod_eq]
  have htwo :
      2 ^ q ∣ 2 * d :=
    nearestQPowerResidueAt_odd_period_implies_pow_dvd_two_mul
      q d hq hqOdd hperiod
  have hqSplit :
      (q - 1) + 1 = q := by
    omega
  have hpowEq :
      2 ^ (q - 1) * 2 = 2 ^ q := by
    calc
      2 ^ (q - 1) * 2 =
          2 ^ ((q - 1) + 1) := by
        rw [pow_succ]
      _ = 2 ^ q := by
        rw [hqSplit]
  have hcancel :
      2 ^ (q - 1) * 2 ∣ d * 2 := by
    rw [hpowEq]
    simpa only [Nat.mul_comm] using htwo
  exact Nat.dvd_of_mul_dvd_mul_right
    (k := 2)
    (by decide)
    hcancel

/--
For odd positive `q`, the least positive period of `ρ_q`
is exactly `2^(q - 1)`.
@isnad1 id=isleastp.2h1v.s4.c4ca9548f1cf from=translated src=- shape=1b3b1243 vocab=264ff6ac
-/
theorem nearestQPowerResidueAt_isLeastPeriod_of_odd
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    IsLeastPositiveNatPeriod
      (nearestQPowerResidueAt q)
      (nearestQResiduePeriod q) := by
  refine ⟨
    nearestQResiduePeriod_pos q,
    nearestQPowerResidueAt_periodic q hq,
    ?_
  ⟩
  intro d hdpos hdperiod
  exact Nat.le_of_dvd hdpos
    (nearestQResiduePeriod_dvd_of_odd_period
      q d hq hqOdd hdperiod)

/--
For odd positive `q`, the least positive period of `ω_q`
is also exactly `2^(q - 1)`.
@isnad1 id=isleastp.2h1v.s4.426fa52f37e4 from=translated src=- shape=02490f5b vocab=97429162
-/
theorem nearestQOmegaAt_isLeastPeriod_of_odd
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    IsLeastPositiveNatPeriod
      (nearestQOmegaAt q)
      (nearestQResiduePeriod q) := by
  exact
    (nearestQPowerResidueAt_isLeastPeriod_iff_omega
      q (nearestQResiduePeriod q)).1
      (nearestQPowerResidueAt_isLeastPeriod_of_odd
        q hq hqOdd)

/--
Every odd square is congruent to one modulo four.
Consequently, the nearest-root residue sequence for `q = 2`
is constantly equal to one.
@isnad1 id=eq.0h1v.s4.1cd5c59cf520 from=translated src=- shape=fe2c2146 vocab=ad4e306f
-/
theorem nearestQPowerResidueAt_two
    (r : Nat) :
    nearestQPowerResidueAt 2 r = 1 := by
  rw [nearestQPowerResidueAt_eq_oddPowerMod]
  have hpow :
      (2 * r + 1) ^ 2 =
        4 * (r ^ 2 + r) + 1 := by
    ring
  rw [hpow]
  norm_num [Nat.add_mod, Nat.mul_mod]

/--
Every odd fourth power is congruent to one modulo sixteen.
Consequently, the nearest-root residue sequence for `q = 4`
is constantly equal to one.
@isnad1 id=eq.0h1v.s4.7674f2101474 from=translated src=- shape=fe2c2146 vocab=ad4e306f
-/
theorem nearestQPowerResidueAt_four
    (r : Nat) :
    nearestQPowerResidueAt 4 r = 1 := by
  rw [nearestQPowerResidueAt_eq_oddPowerMod]
  obtain ⟨k, hk | hk⟩ :=
    Nat.even_or_odd' r
  · rw [hk]
    have hpow :
        (2 * (2 * k) + 1) ^ 4 =
          16 *
              (16 * k ^ 4 +
                16 * k ^ 3 +
                6 * k ^ 2 +
                k) +
            1 := by
      ring
    rw [hpow]
    norm_num [Nat.add_mod, Nat.mul_mod]
  · rw [hk]
    have hpow :
        (2 * (2 * k + 1) + 1) ^ 4 =
          16 *
              (16 * k ^ 4 +
                48 * k ^ 3 +
                54 * k ^ 2 +
                27 * k +
                5) +
            1 := by
      ring
    rw [hpow]
    norm_num [Nat.add_mod, Nat.mul_mod]

/--
For `q = 2`, the residue sequence has period one.
@isnad1 id=periodic.0h0v.s3.cc5a9639b1b2 from=translated src=- shape=be477f6c vocab=41fe0b01
-/
theorem nearestQPowerResidueAt_two_periodic_one :
    Function.Periodic
      (nearestQPowerResidueAt 2)
      1 := by
  intro r
  rw [
    nearestQPowerResidueAt_two,
    nearestQPowerResidueAt_two
  ]

/--
For `q = 4`, the residue sequence has period one.
@isnad1 id=periodic.0h0v.s3.05c7b387b179 from=translated src=- shape=be477f6c vocab=41fe0b01
-/
theorem nearestQPowerResidueAt_four_periodic_one :
    Function.Periodic
      (nearestQPowerResidueAt 4)
      1 := by
  intro r
  rw [
    nearestQPowerResidueAt_four,
    nearestQPowerResidueAt_four
  ]

/--
The least positive period of `ρ₂` is one.
@isnad1 id=isleastp.0h0v.s3.9651391064b1 from=translated src=- shape=3c26ae4f vocab=130dc6e0
-/
theorem nearestQPowerResidueAt_isLeastPeriod_two :
    IsLeastPositiveNatPeriod
      (nearestQPowerResidueAt 2)
      1 := by
  refine ⟨
    by decide,
    nearestQPowerResidueAt_two_periodic_one,
    ?_
  ⟩
  intro d hd _hperiod
  omega

/--
The least positive period of `ρ₄` is one.
@isnad1 id=isleastp.0h0v.s3.58a5240c656a from=translated src=- shape=3c26ae4f vocab=130dc6e0
-/
theorem nearestQPowerResidueAt_isLeastPeriod_four :
    IsLeastPositiveNatPeriod
      (nearestQPowerResidueAt 4)
      1 := by
  refine ⟨
    by decide,
    nearestQPowerResidueAt_four_periodic_one,
    ?_
  ⟩
  intro d hd _hperiod
  omega

/--
The least positive period of `ω₂` is one.
@isnad1 id=isleastp.0h0v.s3.ad586f828b01 from=translated src=- shape=424ed084 vocab=42545c74
-/
theorem nearestQOmegaAt_isLeastPeriod_two :
    IsLeastPositiveNatPeriod
      (nearestQOmegaAt 2)
      1 := by
  exact
    (nearestQPowerResidueAt_isLeastPeriod_iff_omega
      2 1).1
      nearestQPowerResidueAt_isLeastPeriod_two

/--
The least positive period of `ω₄` is one.
@isnad1 id=isleastp.0h0v.s3.024a07e91e73 from=translated src=- shape=424ed084 vocab=42545c74
-/
theorem nearestQOmegaAt_isLeastPeriod_four :
    IsLeastPositiveNatPeriod
      (nearestQOmegaAt 4)
      1 := by
  exact
    (nearestQPowerResidueAt_isLeastPeriod_iff_omega
      4 1).1
      nearestQPowerResidueAt_isLeastPeriod_four

/--
The two-adic order `ν₂(q)` of the exponent `q`.-/
def nearestQTwoAdicOrder
    (q : Nat) : Nat :=
  padicValNat 2 q

/--
The expected exact period in the nonexceptional even case:

`2^(q - 1 - ν₂(q))`.-/
def nearestQEvenResiduePeriod
    (q : Nat) : Nat :=
  2 ^ (q - 1 - nearestQTwoAdicOrder q)

/--
The even-case period candidate written directly using
the two-adic valuation.
@isnad1 id=eq.0h1v.s5.686c88f772f6 from=translated src=- shape=962c9202 vocab=fb4f515a
-/
theorem nearestQEvenResiduePeriod_eq
    (q : Nat) :
    nearestQEvenResiduePeriod q =
      2 ^ (q - 1 - padicValNat 2 q) := by
  rfl

/--
The maximal power `2^ν₂(q)` divides `q`.
@isnad1 id=dvd.0h1v.s4.e5925f305d66 from=translated src=- shape=3a6b3ed6 vocab=52784dfd
-/
theorem nearestQTwoAdicOrder_pow_dvd
    (q : Nat) :
    2 ^ nearestQTwoAdicOrder q ∣ q := by
  unfold nearestQTwoAdicOrder
  exact pow_padicValNat_dvd

/--
For positive `q`, the next power
`2^(ν₂(q) + 1)` does not divide `q`.
@isnad1 id=not.1h1v.s5.0abb2ff262a0 from=translated src=- shape=ab41d489 vocab=4ea5e32e
-/
theorem nearestQTwoAdicOrder_next_pow_not_dvd
    (q : Nat)
    (hq : 0 < q) :
    ¬2 ^ (nearestQTwoAdicOrder q + 1) ∣ q := by
  unfold nearestQTwoAdicOrder
  exact
    pow_succ_padicValNat_not_dvd
      (p := 2)
      (Nat.ne_of_gt hq)

/--
The odd part of `q`, obtained after removing the maximal
power of two dividing `q`.-/
def nearestQOddPart
    (q : Nat) : Nat :=
  q / 2 ^ nearestQTwoAdicOrder q

/--
The exponent `q` decomposes as

`q = 2^ν₂(q) * nearestQOddPart q`.
@isnad1 id=eq.0h1v.s5.9b4869312a1b from=translated src=- shape=8ff0dd88 vocab=2eeeec06
-/
theorem nearestQTwoAdicOrder_mul_oddPart
    (q : Nat) :
    2 ^ nearestQTwoAdicOrder q *
        nearestQOddPart q =
      q := by
  unfold nearestQOddPart
  exact Nat.mul_div_cancel'
    (nearestQTwoAdicOrder_pow_dvd q)

/--
For positive `q`, the odd part of `q` is not divisible by two.
@isnad1 id=not.1h1v.s4.4fabb571f83e from=translated src=- shape=ff955309 vocab=e509df9b
-/
theorem nearestQOddPart_not_two_dvd
    (q : Nat)
    (hq : 0 < q) :
    ¬2 ∣ nearestQOddPart q := by
  intro hdiv
  apply
    nearestQTwoAdicOrder_next_pow_not_dvd
      q hq
  rcases hdiv with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    q =
        2 ^ nearestQTwoAdicOrder q *
          nearestQOddPart q := by
      symm
      exact nearestQTwoAdicOrder_mul_oddPart q
    _ =
        2 ^ nearestQTwoAdicOrder q *
          (2 * k) := by
      rw [hk]
    _ =
        (2 ^ nearestQTwoAdicOrder q * 2) *
          k := by
      ac_rfl
    _ =
        2 ^ (nearestQTwoAdicOrder q + 1) *
          k := by
      rw [pow_succ]

/--
For positive `q`, its odd part is positive.
@isnad1 id=lt.1h1v.s4.e90b652a5808 from=translated src=- shape=35bd48ee vocab=94b474c1
-/
theorem nearestQOddPart_pos
    (q : Nat)
    (hq : 0 < q) :
    0 < nearestQOddPart q := by
  by_contra hpos
  have hzero :
      nearestQOddPart q = 0 := by
    exact Nat.eq_zero_of_not_pos hpos
  have hdecomp :=
    nearestQTwoAdicOrder_mul_oddPart q
  rw [hzero, Nat.mul_zero] at hdecomp
  omega

/--
For positive `q`, the remaining factor after removing
the maximal power of two is odd.
@isnad1 id=odd.1h1v.s4.8b61c7571f36 from=translated src=- shape=f10a4ec0 vocab=fdf81e06
-/
theorem nearestQOddPart_odd
    (q : Nat)
    (hq : 0 < q) :
    Odd (nearestQOddPart q) := by
  obtain ⟨k, hk | hk⟩ :=
    Nat.even_or_odd' (nearestQOddPart q)
  · exfalso
    apply nearestQOddPart_not_two_dvd q hq
    refine ⟨k, ?_⟩
    omega
  · exact ⟨k, by omega⟩

/--
For positive `q`, its two-adic order is strictly smaller than `q`.
@isnad1 id=lt.1h1v.s4.e7c055c5659b from=translated src=- shape=71fa8a4a vocab=d9aeb666
-/
theorem nearestQTwoAdicOrder_lt_self
    (q : Nat)
    (hq : 0 < q) :
    nearestQTwoAdicOrder q < q := by
  have hpowDvd :
      2 ^ nearestQTwoAdicOrder q ∣ q :=
    nearestQTwoAdicOrder_pow_dvd q
  have hpowLe :
      2 ^ nearestQTwoAdicOrder q ≤ q :=
    Nat.le_of_dvd hq hpowDvd
  have horderLtPow :
      nearestQTwoAdicOrder q <
        2 ^ nearestQTwoAdicOrder q := by
    generalize
      nearestQTwoAdicOrder q = s
    induction s with
    | zero =>
        norm_num
    | succ s ih =>
        rw [pow_succ]
        omega
  exact lt_of_lt_of_le horderLtPow hpowLe

/--
For positive even `q`, at least one factor of two divides `q`.
Therefore its two-adic order is positive.
@isnad1 id=lt.2h1v.s4.ff71f5b5fa42 from=translated src=- shape=1ab87d3a vocab=4c32895e
-/
theorem nearestQTwoAdicOrder_pos_of_even
    (q : Nat)
    (hq : 0 < q)
    (hqEven : Even q) :
    0 < nearestQTwoAdicOrder q := by
  by_contra hpos
  have hzero :
      nearestQTwoAdicOrder q = 0 := by
    exact Nat.eq_zero_of_not_pos hpos
  have hnot :=
    nearestQTwoAdicOrder_next_pow_not_dvd
      q hq
  rw [hzero] at hnot
  norm_num at hnot
  rcases hqEven with ⟨k, hk⟩
  rw [hk] at hnot
  omega

/--
For even `q ≥ 6`, the two-adic order is at least
two below `q`.
@isnad1 id=le.2h1v.s5.b54cba5d3606 from=translated src=- shape=339911a3 vocab=2bc2fbc5
-/
theorem nearestQTwoAdicOrder_add_two_le_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQTwoAdicOrder q + 2 ≤ q := by
  have hqPos : 0 < q := by
    omega
  have hsPos :
      0 < nearestQTwoAdicOrder q :=
    nearestQTwoAdicOrder_pos_of_even
      q hqPos hqEven
  by_cases hsOne :
      nearestQTwoAdicOrder q = 1
  · omega
  · have hsTwo :
        2 ≤ nearestQTwoAdicOrder q := by
      omega
    have hpowDvd :
        2 ^ nearestQTwoAdicOrder q ∣ q :=
      nearestQTwoAdicOrder_pow_dvd q
    have hpowLe :
        2 ^ nearestQTwoAdicOrder q ≤ q :=
      Nat.le_of_dvd hqPos hpowDvd
    have haux :
        ∀ s : Nat,
          2 ≤ s →
          s + 2 ≤ 2 ^ s := by
      intro s hs
      induction s with
      | zero =>
          omega
      | succ s ih =>
          by_cases hsOne' : s = 1
          · subst s
            norm_num
          · have hsTwo' : 2 ≤ s := by
              omega
            have hih := ih hsTwo'
            rw [pow_succ]
            omega
    exact le_trans
      (haux
        (nearestQTwoAdicOrder q)
        hsTwo)
      hpowLe

/--
For even `q ≥ 6`, the exponent in the expected
period `2^(q - 1 - ν₂(q))` is positive.
@isnad1 id=lt.2h1v.s5.72ca934d267f from=translated src=- shape=6cce5c26 vocab=1920a35d
-/
theorem nearestQEvenResidueExponent_pos
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    0 <
      q - 1 - nearestQTwoAdicOrder q := by
  have hbound :=
    nearestQTwoAdicOrder_add_two_le_of_even_ge_six
      q hq hqEven
  omega

/--
For even `q ≥ 6`, the expected residue period is at least two.
@isnad1 id=le.2h1v.s4.3521d485b205 from=translated src=- shape=1ab87d3a vocab=453e498a
-/
theorem nearestQEvenResiduePeriod_two_le
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 ≤ nearestQEvenResiduePeriod q := by
  unfold nearestQEvenResiduePeriod
  have hexponent :
      0 <
        q - 1 - nearestQTwoAdicOrder q :=
    nearestQEvenResidueExponent_pos
      q hq hqEven
  generalize
    q - 1 - nearestQTwoAdicOrder q = e
      at hexponent ⊢
  cases e with
  | zero =>
      omega
  | succ e =>
      rw [pow_succ]
      have hpowPos :
          0 < 2 ^ e := by
        positivity
      omega

/--
For even `q ≥ 6`, twice the expected period is

`2^(q - ν₂(q))`.
@isnad1 id=eq.2h1v.s5.d876b0db6645 from=translated src=- shape=9708dee1 vocab=d2a17a81
-/
theorem two_mul_nearestQEvenResiduePeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 * nearestQEvenResiduePeriod q =
      2 ^ (q - nearestQTwoAdicOrder q) := by
  have hbound :
      nearestQTwoAdicOrder q + 2 ≤ q :=
    nearestQTwoAdicOrder_add_two_le_of_even_ge_six
      q hq hqEven
  have hexponent :
      (q - 1 - nearestQTwoAdicOrder q) + 1 =
        q - nearestQTwoAdicOrder q := by
    omega
  unfold nearestQEvenResiduePeriod
  calc
    2 * 2 ^ (q - 1 - nearestQTwoAdicOrder q) =
        2 ^ (q - 1 - nearestQTwoAdicOrder q) * 2 := by
      ac_rfl
    _ =
        2 ^
          ((q - 1 - nearestQTwoAdicOrder q) + 1) := by
      rw [pow_succ]
    _ =
        2 ^ (q - nearestQTwoAdicOrder q) := by
      rw [hexponent]

/--
Shifting the index by the expected period adds twice
that period to the corresponding odd base.
@isnad1 id=eq.0h2v.s6.64116cb989ff from=translated src=- shape=d2dbfc23 vocab=7cf19911
-/
theorem nearestQOddBase_add_evenPeriod
    (q r : Nat) :
    2 * (r + nearestQEvenResiduePeriod q) + 1 =
      (2 * r + 1) +
        2 * nearestQEvenResiduePeriod q := by
  omega

/--
For even `q ≥ 6`, shifting the index by the expected
period adds exactly `2^(q - ν₂(q))` to the odd base.
@isnad1 id=eq.2h2v.s6.bc75b071f88d from=translated src=- shape=3af59c1e vocab=bcdc5f9a
-/
theorem nearestQOddBase_add_evenPeriod_eq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 * (r + nearestQEvenResiduePeriod q) + 1 =
      (2 * r + 1) +
        2 ^ (q - nearestQTwoAdicOrder q) := by
  calc
    2 * (r + nearestQEvenResiduePeriod q) + 1 =
        (2 * r + 1) +
          2 * nearestQEvenResiduePeriod q := by
      exact nearestQOddBase_add_evenPeriod q r
    _ =
        (2 * r + 1) +
          2 ^ (q - nearestQTwoAdicOrder q) := by
      rw [
        two_mul_nearestQEvenResiduePeriod
          q hq hqEven
      ]

/--
The additive shift of the odd base associated with
the expected period in the even case.-/
def nearestQEvenShift
    (q : Nat) : Nat :=
  2 ^ (q - nearestQTwoAdicOrder q)

/--
For even `q ≥ 6`, the additive base shift is twice
the expected residue period.
@isnad1 id=eq.2h1v.s5.e34ab179e02a from=translated src=- shape=313f7a45 vocab=81ecab1a
-/
theorem nearestQEvenShift_eq_two_mul_period
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQEvenShift q =
      2 * nearestQEvenResiduePeriod q := by
  unfold nearestQEvenShift
  symm
  exact
    two_mul_nearestQEvenResiduePeriod
      q hq hqEven

/--
The first nonconstant term in the binomial expansion

`(x + 2^(q - ν₂(q)))^q`

is divisible by `2^q`.
@isnad1 id=dvd.1h2v.s6.9065223771cd from=translated src=- shape=de41c0af vocab=0ce255c6
-/
theorem nearestQFirstBinomialTerm_dvd
    (q r : Nat)
    (hq : 0 < q) :
    2 ^ q ∣
      q * (2 * r + 1) ^ (q - 1) *
        nearestQEvenShift q := by
  let s :=
    nearestQTwoAdicOrder q
  let u :=
    nearestQOddPart q
  change
    2 ^ q ∣
      q * (2 * r + 1) ^ (q - 1) *
        2 ^ (q - s)
  have hsLe :
      s ≤ q := by
    exact Nat.le_of_lt
      (nearestQTwoAdicOrder_lt_self q hq)
  have hdecomp :
      2 ^ s * u = q := by
    simpa [s, u] using
      nearestQTwoAdicOrder_mul_oddPart q
  have hpow :
      2 ^ s * 2 ^ (q - s) = 2 ^ q := by
    calc
      2 ^ s * 2 ^ (q - s) =
          2 ^ (s + (q - s)) := by
        rw [pow_add]
      _ = 2 ^ q := by
        rw [show s + (q - s) = q by omega]
  refine
    ⟨u * (2 * r + 1) ^ (q - 1), ?_⟩
  calc
    q * (2 * r + 1) ^ (q - 1) *
          2 ^ (q - s) =
        (2 ^ s * u) *
          (2 * r + 1) ^ (q - 1) *
          2 ^ (q - s) := by
      rw [hdecomp]
    _ =
        (2 ^ s * 2 ^ (q - s)) *
          (u * (2 * r + 1) ^ (q - 1)) := by
      ac_rfl
    _ =
        2 ^ q *
          (u * (2 * r + 1) ^ (q - 1)) := by
      rw [hpow]

/--
For even `q ≥ 6`, twice the two-adic order of `q`
does not exceed `q`.
@isnad1 id=le.2h1v.s5.00a90e92c931 from=translated src=- shape=97ee2391 vocab=ab9b9317
-/
theorem nearestQTwoAdicOrder_double_le_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 * nearestQTwoAdicOrder q ≤ q := by
  have hqPos : 0 < q := by
    omega
  have hsPos :
      0 < nearestQTwoAdicOrder q :=
    nearestQTwoAdicOrder_pos_of_even
      q hqPos hqEven
  by_cases hsOne :
      nearestQTwoAdicOrder q = 1
  · omega
  · have hsTwo :
        2 ≤ nearestQTwoAdicOrder q := by
      omega
    have hpowDvd :
        2 ^ nearestQTwoAdicOrder q ∣ q :=
      nearestQTwoAdicOrder_pow_dvd q
    have hpowLe :
        2 ^ nearestQTwoAdicOrder q ≤ q :=
      Nat.le_of_dvd hqPos hpowDvd
    have haux :
        ∀ s : Nat,
          2 ≤ s →
          2 * s ≤ 2 ^ s := by
      intro s hs
      induction s with
      | zero =>
          omega
      | succ s ih =>
          by_cases hsOne' : s = 1
          · subst s
            norm_num
          · have hsTwo' : 2 ≤ s := by
              omega
            have hih := ih hsTwo'
            rw [pow_succ]
            omega
    exact le_trans
      (haux
        (nearestQTwoAdicOrder q)
        hsTwo)
      hpowLe

/--
For even `q ≥ 6`, the square of the additive base shift
is divisible by `2^q`.
@isnad1 id=dvd.2h1v.s5.1d70bea37d83 from=translated src=- shape=b8642955 vocab=3f9029fa
-/
theorem nearestQEvenShift_sq_dvd
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 ^ q ∣ nearestQEvenShift q ^ 2 := by
  have hdouble :
      2 * nearestQTwoAdicOrder q ≤ q :=
    nearestQTwoAdicOrder_double_le_of_even_ge_six
      q hq hqEven
  have hexponent :
      q ≤
        (q - nearestQTwoAdicOrder q) * 2 := by
    omega
  have hpow :
      2 ^ q ∣
        2 ^
          ((q - nearestQTwoAdicOrder q) * 2) :=
    Nat.pow_dvd_pow 2 hexponent
  simpa [nearestQEvenShift, pow_mul] using hpow

/--
For even `q ≥ 6`, every power of the additive shift
with exponent at least two is divisible by `2^q`.
@isnad1 id=dvd.3h2v.s6.2a16ce931a3d from=translated src=- shape=52133765 vocab=3f9029fa
-/
theorem nearestQEvenShift_pow_dvd
    (q j : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hj : 2 ≤ j) :
    2 ^ q ∣ nearestQEvenShift q ^ j := by
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_add_of_le hj
  obtain ⟨c, hc⟩ :=
    nearestQEvenShift_sq_dvd
      q hq hqEven
  refine
    ⟨c * nearestQEvenShift q ^ k, ?_⟩
  rw [pow_add, hc]
  ac_rfl

/--
Every binomial term containing at least the square
of the additive shift is divisible by `2^q`.
@isnad1 id=dvd.3h3v.s7.ffd74d6d95f8 from=translated src=- shape=37d2125a vocab=ddf60c8d
-/
theorem nearestQHigherBinomialTerm_dvd
    (q r j : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hj : 2 ≤ j) :
    2 ^ q ∣
      Nat.choose q j *
        (2 * r + 1) ^ (q - j) *
        nearestQEvenShift q ^ j := by
  obtain ⟨c, hc⟩ :=
    nearestQEvenShift_pow_dvd
      q j hq hqEven hj
  refine
    ⟨Nat.choose q j *
        (2 * r + 1) ^ (q - j) *
        c,
      ?_⟩
  rw [hc]
  ac_rfl

/--
Every positive-index term in the binomial expansion
is divisible by `2^q`.
@isnad1 id=dvd.3h3v.s7.01a7de03ec83 from=translated src=- shape=3e28cb1f vocab=a81b1619
-/
theorem nearestQPositiveBinomialTerm_dvd
    (q r j : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hj : 0 < j) :
    2 ^ q ∣
      Nat.choose q j *
        (2 * r + 1) ^ (q - j) *
        nearestQEvenShift q ^ j := by
  by_cases hjOne : j = 1
  · subst j
    simpa using
      nearestQFirstBinomialTerm_dvd
        q r (by omega)
  · have hjTwo :
        2 ≤ j := by
      omega
    exact
      nearestQHigherBinomialTerm_dvd
        q r j hq hqEven hjTwo

/--
The positive-index part of the binomial expansion of

`((2 * r + 1) + nearestQEvenShift q)^q`.-/
def nearestQBinomialTail
    (q r : Nat) : Nat :=
  Finset.sum
    ((Finset.range (q + 1)).erase 0)
    (fun j =>
      Nat.choose q j *
        (2 * r + 1) ^ (q - j) *
        nearestQEvenShift q ^ j)

/--
For even `q ≥ 6`, the complete positive-index
binomial tail is divisible by `2^q`.
@isnad1 id=dvd.2h2v.s5.db99fdf729e1 from=translated src=- shape=a6b2f86d vocab=008b72ce
-/
theorem nearestQBinomialTail_dvd
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 ^ q ∣ nearestQBinomialTail q r := by
  unfold nearestQBinomialTail
  apply Finset.dvd_sum
  intro j hj
  have hjNe :
      j ≠ 0 :=
    (Finset.mem_erase.mp hj).1
  have hjPos :
      0 < j :=
    Nat.pos_of_ne_zero hjNe
  exact
    nearestQPositiveBinomialTerm_dvd
      q r j hq hqEven hjPos

/--
The binomial expansion splits into its zero-index term
and the positive-index tail.
@isnad1 id=eq.0h2v.s6.1336afba9081 from=translated src=- shape=ae13ce27 vocab=89e49af8
-/
theorem nearestQAddPow_eq_base_add_tail
    (q r : Nat) :
    ((2 * r + 1) + nearestQEvenShift q) ^ q =
      (2 * r + 1) ^ q +
        nearestQBinomialTail q r := by
  classical
  let f : Nat → Nat := fun j =>
    Nat.choose q j *
      (2 * r + 1) ^ (q - j) *
      nearestQEvenShift q ^ j
  have hfull :
      ((2 * r + 1) + nearestQEvenShift q) ^ q =
        Finset.sum
          (Finset.range (q + 1))
          f := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [f]
    ac_rfl
  have hzero :
      0 ∈ Finset.range (q + 1) := by
    simp
  calc
    ((2 * r + 1) + nearestQEvenShift q) ^ q =
        Finset.sum
          (Finset.range (q + 1))
          f :=
      hfull
    _ =
        f 0 +
          Finset.sum
            ((Finset.range (q + 1)).erase 0)
            f := by
      calc
        Finset.sum
            (Finset.range (q + 1))
            f =
          Finset.sum
              ((Finset.range (q + 1)).erase 0)
              f +
            f 0 := by
          symm
          exact
            Finset.sum_erase_add
              (Finset.range (q + 1))
              f
              hzero
        _ =
            f 0 +
              Finset.sum
                ((Finset.range (q + 1)).erase 0)
                f := by
          ac_rfl
    _ =
        (2 * r + 1) ^ q +
          nearestQBinomialTail q r := by
      simp [f, nearestQBinomialTail]

/--
For even `q ≥ 6`, adding the even-case base shift
does not change the q-th power modulo `2^q`.
@isnad1 id=modeq.2h2v.s6.9be5196b537a from=translated src=- shape=b0150b2c vocab=e5c74b0b
-/
theorem nearestQAddShift_pow_modEq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Nat.ModEq
      (2 ^ q)
      (((2 * r + 1) + nearestQEvenShift q) ^ q)
      ((2 * r + 1) ^ q) := by
  rw [nearestQAddPow_eq_base_add_tail]
  symm
  have hle :
      (2 * r + 1) ^ q ≤
        (2 * r + 1) ^ q +
          nearestQBinomialTail q r := by
    omega
  apply
    (Nat.modEq_iff_dvd' hle).2
  simpa using
    nearestQBinomialTail_dvd
      q r hq hqEven

/--
For even `q ≥ 6`, shifting the index by the expected
period does not change the corresponding odd q-th power
modulo `2^q`.
@isnad1 id=modeq.2h2v.s6.699621161aea from=translated src=- shape=344c8c5a vocab=18ccb0aa
-/
theorem nearestQOddPower_add_evenPeriod_modEq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Nat.ModEq
      (2 ^ q)
      ((2 * (r + nearestQEvenResiduePeriod q) + 1) ^ q)
      ((2 * r + 1) ^ q) := by
  rw [
    nearestQOddBase_add_evenPeriod_eq
      q r hq hqEven
  ]
  simpa [nearestQEvenShift] using
    nearestQAddShift_pow_modEq
      q r hq hqEven

/--
For even `q ≥ 6`, the expected period

`2^(q - 1 - ν₂(q))`

is a period of the nearest-root power-residue sequence.
@isnad1 id=periodic.2h1v.s4.6781dd128726 from=translated src=- shape=94db5565 vocab=4ef714f4
-/
theorem nearestQPowerResidueAt_even_periodic
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Function.Periodic
      (nearestQPowerResidueAt q)
      (nearestQEvenResiduePeriod q) := by
  intro r
  rw [
    nearestQPowerResidueAt_eq_oddPowerMod,
    nearestQPowerResidueAt_eq_oddPowerMod
  ]
  exact
    nearestQOddPower_add_evenPeriod_modEq
      q r hq hqEven

/--
Half of the expected period in the nonexceptional even case.
This is the only maximal proper power-of-two divisor
that must be excluded to prove minimality.-/
def nearestQEvenResidueHalfPeriod
    (q : Nat) : Nat :=
  2 ^ (q - 2 - nearestQTwoAdicOrder q)

/--
For even `q ≥ 6`, twice the half-period is exactly
the expected period.
@isnad1 id=eq.2h1v.s5.b526a3b7d475 from=translated src=- shape=d6adb4b5 vocab=48263cae
-/
theorem two_mul_nearestQEvenResidueHalfPeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 * nearestQEvenResidueHalfPeriod q =
      nearestQEvenResiduePeriod q := by
  have hbound :
      nearestQTwoAdicOrder q + 2 ≤ q :=
    nearestQTwoAdicOrder_add_two_le_of_even_ge_six
      q hq hqEven
  have hexponent :
      (q - 2 - nearestQTwoAdicOrder q) + 1 =
        q - 1 - nearestQTwoAdicOrder q := by
    omega
  unfold nearestQEvenResidueHalfPeriod
  unfold nearestQEvenResiduePeriod
  calc
    2 * 2 ^ (q - 2 - nearestQTwoAdicOrder q) =
        2 ^ (q - 2 - nearestQTwoAdicOrder q) * 2 := by
      ac_rfl
    _ =
        2 ^
          ((q - 2 - nearestQTwoAdicOrder q) + 1) := by
      rw [pow_succ]
    _ =
        2 ^ (q - 1 - nearestQTwoAdicOrder q) := by
      rw [hexponent]

/--
At the half-period index, the corresponding odd base
is one plus the expected full period.
@isnad1 id=eq.2h1v.s5.5ca236c4e652 from=translated src=- shape=e271c73d vocab=c0533a65
-/
theorem nearestQOddBase_at_evenHalfPeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 * nearestQEvenResidueHalfPeriod q + 1 =
      1 + nearestQEvenResiduePeriod q := by
  rw [
    two_mul_nearestQEvenResidueHalfPeriod
      q hq hqEven
  ]
  omega

/--
For even `q ≥ 6`, the linear binomial term `q * P_q`
contains exactly the factor `2^(q - 1)`, multiplied by
the odd part of `q`.
@isnad1 id=eq.2h1v.s6.03525e3801ee from=translated src=- shape=5899def4 vocab=72c63c9f
-/
theorem nearestQEvenLinearTerm_eq
    (q : Nat)
    (hq : 6 ≤ q)
    (_hqEven : Even q) :
    q * nearestQEvenResiduePeriod q =
      2 ^ (q - 1) * nearestQOddPart q := by
  let s :=
    nearestQTwoAdicOrder q
  let u :=
    nearestQOddPart q
  have hqPos :
      0 < q := by
    omega
  have hsLt :
      s < q := by
    simpa [s] using
      nearestQTwoAdicOrder_lt_self q hqPos
  have hdecomp :
      2 ^ s * u = q := by
    simpa [s, u] using
      nearestQTwoAdicOrder_mul_oddPart q
  have hexponent :
      s + (q - 1 - s) = q - 1 := by
    omega
  unfold nearestQEvenResiduePeriod
  calc
    q * 2 ^ (q - 1 - nearestQTwoAdicOrder q) =
        (2 ^ s * u) *
          2 ^ (q - 1 - s) := by
      rw [hdecomp]
    _ =
        (2 ^ s * 2 ^ (q - 1 - s)) * u := by
      ac_rfl
    _ =
        2 ^ (s + (q - 1 - s)) * u := by
      rw [pow_add]
    _ =
        2 ^ (q - 1) * u := by
      rw [hexponent]
    _ =
        2 ^ (q - 1) * nearestQOddPart q := by
      rfl

/--
For even `q ≥ 6`, the linear term `q * P_q`
is not divisible by `2^q`.
@isnad1 id=not.2h1v.s5.02b5f28449d6 from=translated src=- shape=699d29e8 vocab=ffa5e0b0
-/
theorem nearestQEvenLinearTerm_not_dvd
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    ¬2 ^ q ∣
      q * nearestQEvenResiduePeriod q := by
  have hqPos :
      0 < q := by
    omega
  intro hdiv
  obtain ⟨k, hk⟩ := hdiv
  rw [
    nearestQEvenLinearTerm_eq
      q hq hqEven
  ] at hk
  have hpow :
      2 ^ q =
        2 ^ (q - 1) * 2 := by
    calc
      2 ^ q =
          2 ^ ((q - 1) + 1) := by
        congr 1
        omega
      _ =
          2 ^ (q - 1) * 2 := by
        rw [pow_succ]
  rw [hpow] at hk
  have hk' :
      2 ^ (q - 1) * nearestQOddPart q =
        2 ^ (q - 1) * (2 * k) := by
    calc
      2 ^ (q - 1) * nearestQOddPart q =
          (2 ^ (q - 1) * 2) * k :=
        hk
      _ =
          2 ^ (q - 1) * (2 * k) := by
        ac_rfl
  have hoddPart :
      nearestQOddPart q = 2 * k := by
    exact
      Nat.mul_left_cancel
        (show 0 < 2 ^ (q - 1) by
          positivity)
        hk'
  apply nearestQOddPart_not_two_dvd q hqPos
  exact ⟨k, hoddPart⟩

/--
For `q ≥ 6`, twice the two-adic order of `q`,
plus two, does not exceed `q`.
@isnad1 id=le.2h1v.s5.a7608c40ee3d from=translated src=- shape=4f7d6111 vocab=76447268
-/
theorem nearestQTwoAdicOrder_double_add_two_le_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (_hqEven : Even q) :
    2 * nearestQTwoAdicOrder q + 2 ≤ q := by
  have hqPos :
      0 < q := by
    omega
  by_cases hsSmall :
      nearestQTwoAdicOrder q ≤ 2
  · omega
  · have hsThree :
        3 ≤ nearestQTwoAdicOrder q := by
      omega
    have hpowDvd :
        2 ^ nearestQTwoAdicOrder q ∣ q :=
      nearestQTwoAdicOrder_pow_dvd q
    have hpowLe :
        2 ^ nearestQTwoAdicOrder q ≤ q :=
      Nat.le_of_dvd hqPos hpowDvd
    have haux :
        ∀ s : Nat,
          3 ≤ s →
          2 * s + 2 ≤ 2 ^ s := by
      intro s hs
      induction s with
      | zero =>
          omega
      | succ s ih =>
          by_cases hsTwo : s = 2
          · subst s
            norm_num
          · have hsThree' :
                3 ≤ s := by
              omega
            have hih :=
              ih hsThree'
            rw [pow_succ]
            omega
    exact le_trans
      (haux
        (nearestQTwoAdicOrder q)
        hsThree)
      hpowLe

/--
For even `q ≥ 6`, the square of the expected period
is divisible by `2^q`.
@isnad1 id=dvd.2h1v.s5.679da8a77ea1 from=translated src=- shape=b8642955 vocab=0789e225
-/
theorem nearestQEvenResiduePeriod_sq_dvd
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 ^ q ∣ nearestQEvenResiduePeriod q ^ 2 := by
  have hbound :
      2 * nearestQTwoAdicOrder q + 2 ≤ q :=
    nearestQTwoAdicOrder_double_add_two_le_of_even_ge_six
      q hq hqEven
  have hexponent :
      q ≤
        (q - 1 - nearestQTwoAdicOrder q) * 2 := by
    omega
  have hpow :
      2 ^ q ∣
        2 ^
          ((q - 1 - nearestQTwoAdicOrder q) * 2) :=
    Nat.pow_dvd_pow 2 hexponent
  simpa [nearestQEvenResiduePeriod, pow_mul] using hpow

/--
For even `q ≥ 6`, every power of the expected period
with exponent at least two is divisible by `2^q`.
@isnad1 id=dvd.3h2v.s6.050d589703b0 from=translated src=- shape=52133765 vocab=0789e225
-/
theorem nearestQEvenResiduePeriod_pow_dvd
    (q j : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hj : 2 ≤ j) :
    2 ^ q ∣ nearestQEvenResiduePeriod q ^ j := by
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_add_of_le hj
  obtain ⟨c, hc⟩ :=
    nearestQEvenResiduePeriod_sq_dvd
      q hq hqEven
  refine
    ⟨c * nearestQEvenResiduePeriod q ^ k, ?_⟩
  rw [pow_add, hc]
  ac_rfl

/--
Every binomial term of degree at least two in
the expected period is divisible by `2^q`.
@isnad1 id=dvd.3h2v.s6.5f2732d09a06 from=translated src=- shape=f7cb9da9 vocab=6df8e2fa
-/
theorem nearestQEvenHigherBinomialTerm_dvd
    (q j : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hj : 2 ≤ j) :
    2 ^ q ∣
      Nat.choose q j *
        nearestQEvenResiduePeriod q ^ j := by
  obtain ⟨c, hc⟩ :=
    nearestQEvenResiduePeriod_pow_dvd
      q j hq hqEven hj
  refine
    ⟨Nat.choose q j * c, ?_⟩
  rw [hc]
  ac_rfl

/--
The nonlinear part of the binomial expansion of

`(1 + nearestQEvenResiduePeriod q)^q`.

It contains precisely the terms with indices
`j = 2, ..., q`.-/
def nearestQEvenNonlinearTail
    (q : Nat) : Nat :=
  Finset.sum
    (((Finset.range (q + 1)).erase 0).erase 1)
    (fun j =>
      Nat.choose q j *
        nearestQEvenResiduePeriod q ^ j)

/--
For even `q ≥ 6`, the complete nonlinear part of the
binomial expansion of `(1 + P_q)^q` is divisible by `2^q`.
@isnad1 id=dvd.2h1v.s5.bd3da7bf22c5 from=translated src=- shape=3187fb21 vocab=f1013fe6
-/
theorem nearestQEvenNonlinearTail_dvd
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    2 ^ q ∣ nearestQEvenNonlinearTail q := by
  unfold nearestQEvenNonlinearTail
  apply Finset.dvd_sum
  intro j hj
  have hjNeOne :
      j ≠ 1 :=
    (Finset.mem_erase.mp hj).1
  have hjEraseZero :
      j ∈
        (Finset.range (q + 1)).erase 0 :=
    (Finset.mem_erase.mp hj).2
  have hjNeZero :
      j ≠ 0 :=
    (Finset.mem_erase.mp hjEraseZero).1
  have hjTwo :
      2 ≤ j := by
    omega
  exact
    nearestQEvenHigherBinomialTerm_dvd
      q j hq hqEven hjTwo

/--
The binomial expansion of `(1 + P_q)^q` consists of
the constant term, the linear term, and the nonlinear tail.
@isnad1 id=eq.1h1v.s6.6ed73ab98657 from=translated src=- shape=42c7be46 vocab=22c9f36f
-/
theorem nearestQOneAddEvenPeriod_pow_eq
    (q : Nat)
    (hq : 1 ≤ q) :
    (1 + nearestQEvenResiduePeriod q) ^ q =
      1 +
        q * nearestQEvenResiduePeriod q +
        nearestQEvenNonlinearTail q := by
  classical
  let f : Nat → Nat := fun j =>
    Nat.choose q j *
      nearestQEvenResiduePeriod q ^ j
  have hfull :
      (1 + nearestQEvenResiduePeriod q) ^ q =
        Finset.sum
          (Finset.range (q + 1))
          f := by
    rw [
      add_comm
        (1 : Nat)
        (nearestQEvenResiduePeriod q),
      add_pow
    ]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [f, mul_comm]
  have hzero :
      0 ∈ Finset.range (q + 1) := by
    simp
  have hone :
      1 ∈
        (Finset.range (q + 1)).erase 0 := by
    rw [Finset.mem_erase]
    constructor
    · norm_num
    · rw [Finset.mem_range]
      omega
  have hsplitZero :
      Finset.sum
          (Finset.range (q + 1))
          f =
        f 0 +
          Finset.sum
            ((Finset.range (q + 1)).erase 0)
            f := by
    calc
      Finset.sum
          (Finset.range (q + 1))
          f =
        Finset.sum
            ((Finset.range (q + 1)).erase 0)
            f +
          f 0 := by
        symm
        exact
          Finset.sum_erase_add
            (Finset.range (q + 1))
            f
            hzero
      _ =
          f 0 +
            Finset.sum
              ((Finset.range (q + 1)).erase 0)
              f := by
        ac_rfl
  have hsplitOne :
      Finset.sum
          ((Finset.range (q + 1)).erase 0)
          f =
        f 1 +
          Finset.sum
            (((Finset.range (q + 1)).erase 0).erase 1)
            f := by
    calc
      Finset.sum
          ((Finset.range (q + 1)).erase 0)
          f =
        Finset.sum
            (((Finset.range (q + 1)).erase 0).erase 1)
            f +
          f 1 := by
        symm
        exact
          Finset.sum_erase_add
            ((Finset.range (q + 1)).erase 0)
            f
            hone
      _ =
          f 1 +
            Finset.sum
              (((Finset.range (q + 1)).erase 0).erase 1)
              f := by
        ac_rfl
  calc
    (1 + nearestQEvenResiduePeriod q) ^ q =
        Finset.sum
          (Finset.range (q + 1))
          f :=
      hfull
    _ =
        f 0 +
          Finset.sum
            ((Finset.range (q + 1)).erase 0)
            f :=
      hsplitZero
    _ =
        f 0 +
          (f 1 +
            Finset.sum
              (((Finset.range (q + 1)).erase 0).erase 1)
              f) := by
      rw [hsplitOne]
    _ =
        1 +
          q * nearestQEvenResiduePeriod q +
          nearestQEvenNonlinearTail q := by
      simp [
        f,
        nearestQEvenNonlinearTail,
        add_assoc
      ]

/--
For even `q ≥ 6`, the value `(1 + P_q)^q - 1`
is not divisible by `2^q`.
@isnad1 id=not.2h1v.s6.9884b023c421 from=translated src=- shape=c84c51e6 vocab=7b5e5835
-/
theorem nearestQOneAddEvenPeriod_pow_sub_one_not_dvd
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    ¬2 ^ q ∣
      (1 + nearestQEvenResiduePeriod q) ^ q - 1 := by
  intro hdiv
  rw [
    nearestQOneAddEvenPeriod_pow_eq
      q
      (by omega)
  ] at hdiv
  have hsub :
      (1 +
          q * nearestQEvenResiduePeriod q +
          nearestQEvenNonlinearTail q) -
          1 =
        q * nearestQEvenResiduePeriod q +
          nearestQEvenNonlinearTail q := by
    omega
  rw [hsub] at hdiv
  have htail :
      2 ^ q ∣ nearestQEvenNonlinearTail q :=
    nearestQEvenNonlinearTail_dvd
      q hq hqEven
  have hsumMod :
      (q * nearestQEvenResiduePeriod q +
          nearestQEvenNonlinearTail q) %
          2 ^ q =
        0 := by
    exact
      Nat.dvd_iff_mod_eq_zero.mp
        hdiv
  have htailMod :
      nearestQEvenNonlinearTail q %
          2 ^ q =
        0 := by
    exact
      Nat.dvd_iff_mod_eq_zero.mp
        htail
  have hlinearMod :
      (q * nearestQEvenResiduePeriod q) %
          2 ^ q =
        0 := by
    simpa [Nat.add_mod, htailMod] using
      hsumMod
  have hlinear :
      2 ^ q ∣
        q * nearestQEvenResiduePeriod q := by
    exact
      Nat.dvd_iff_mod_eq_zero.mpr
        hlinearMod
  exact
    (nearestQEvenLinearTerm_not_dvd
      q hq hqEven)
      hlinear

/--
For even `q ≥ 6`, the residue at the half-period index
differs from the initial residue.
@isnad1 id=ne.2h1v.s4.9758a24c7475 from=translated src=- shape=0214c189 vocab=5f625534
-/
theorem nearestQPowerResidueAt_evenHalfPeriod_ne_initial
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQPowerResidueAt q
        (nearestQEvenResidueHalfPeriod q) ≠
      nearestQPowerResidueAt q 0 := by
  intro heq
  have hqPos :
      0 < q := by
    omega
  have hzero :
      nearestQPowerResidueAt q 0 = 1 :=
    nearestQPowerResidueAt_zero q hqPos
  have hresidue :
      nearestQPowerResidueAt q
          (nearestQEvenResidueHalfPeriod q) =
        1 := by
    exact heq.trans hzero
  rw [
    nearestQPowerResidueAt_eq_oddPowerMod
  ] at hresidue
  rw [
    nearestQOddBase_at_evenHalfPeriod
      q hq hqEven
  ] at hresidue
  have honeLt :
      1 < 2 ^ q := by
    exact
      Nat.one_lt_two_pow
        (Nat.ne_of_gt hqPos)
  have hmod :
      Nat.ModEq
        (2 ^ q)
        ((1 + nearestQEvenResiduePeriod q) ^ q)
        1 := by
    change
      ((1 + nearestQEvenResiduePeriod q) ^ q) %
          2 ^ q =
        1 % 2 ^ q
    rw [Nat.mod_eq_of_lt honeLt]
    exact hresidue
  have honeLe :
      1 ≤
        (1 + nearestQEvenResiduePeriod q) ^ q := by
    simpa [Nat.add_comm] using
      (Nat.one_le_pow'
        q
        (nearestQEvenResiduePeriod q))
  have hdvd :
      2 ^ q ∣
        (1 + nearestQEvenResiduePeriod q) ^ q -
          1 := by
    exact
      (Nat.modEq_iff_dvd' honeLe).1
        hmod.symm
  exact
    (nearestQOneAddEvenPeriod_pow_sub_one_not_dvd
      q hq hqEven)
      hdvd

/--
For even `q ≥ 6`, half of the expected period
is not itself a period of the residue sequence.
@isnad1 id=not.2h1v.s4.c8910605e19c from=translated src=- shape=53f92811 vocab=07ed7da5
-/
theorem nearestQPowerResidueAt_evenHalfPeriod_not_periodic
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    ¬Function.Periodic
      (nearestQPowerResidueAt q)
      (nearestQEvenResidueHalfPeriod q) := by
  intro hperiod
  apply
    nearestQPowerResidueAt_evenHalfPeriod_ne_initial
      q hq hqEven
  simpa using
    hperiod 0

/--
Every natural multiple of a period is again a period.
@isnad1 id=periodic.1h4v.s4.2350ddfbb899 from=translated src=- shape=f0b3f40c vocab=a63bfc85
-/
theorem natPeriodic_mul
    {α : Type*}
    (f : Nat → α)
    (d n : Nat)
    (hperiod : Function.Periodic f d) :
    Function.Periodic f (n * d) := by
  exact hperiod.nat_mul n

/--
If `P` and `d` are periods of a sequence on the naturals,
then `P % d` is also a period.
@isnad1 id=periodic.2h4v.s5.8d2c23aeca6c from=translated src=- shape=d2abe59f vocab=a23a0970
-/
theorem natPeriodic_mod
    {α : Type*}
    (f : Nat → α)
    (P d : Nat)
    (hP : Function.Periodic f P)
    (hd : Function.Periodic f d) :
    Function.Periodic f (P % d) := by
  intro x
  have hmultiple :
      Function.Periodic f ((P / d) * d) := by
    exact hd.nat_mul (P / d)
  have hdecomp :
      P % d + (P / d) * d = P := by
    simpa [Nat.mul_comm] using
      Nat.mod_add_div P d
  calc
    f (x + P % d) =
        f ((x + P % d) + (P / d) * d) := by
      symm
      exact hmultiple (x + P % d)
    _ =
        f (x + P) := by
      rw [add_assoc, hdecomp]
    _ =
        f x := by
      exact hP x

/--
The greatest common divisor of two natural periods
is again a period.
@isnad1 id=periodic.2h4v.s5.cf874ca9d42e from=translated src=- shape=89b11ab1 vocab=4c051c1c
-/
theorem natPeriodic_gcd
    {α : Type*}
    (f : Nat → α)
    (m n : Nat)
    (hm : Function.Periodic f m)
    (hn : Function.Periodic f n) :
    Function.Periodic f (Nat.gcd m n) := by
  revert hm hn
  refine
    Nat.gcd.induction
      m n
      (fun n _ hn => ?_)
      (fun m n _ ih hm hn => ?_)
  · rwa [Nat.gcd_zero_left]
  · rw [Nat.gcd_rec]
    exact
      ih
        (natPeriodic_mod f n m hn hm)
        hm

/--
For even `q ≥ 6`, the gcd of the expected period
and any other period is itself a period of the
nearest-root residue sequence.
@isnad1 id=periodic.3h2v.s5.d5201fe23ff2 from=translated src=- shape=31a8ade4 vocab=1e62ae1d
-/
theorem nearestQPowerResidueAt_even_gcd_periodic
    (q d : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hd :
      Function.Periodic
        (nearestQPowerResidueAt q)
        d) :
    Function.Periodic
      (nearestQPowerResidueAt q)
      (Nat.gcd
        (nearestQEvenResiduePeriod q)
        d) := by
  exact
    natPeriodic_gcd
      (nearestQPowerResidueAt q)
      (nearestQEvenResiduePeriod q)
      d
      (nearestQPowerResidueAt_even_periodic
        q hq hqEven)
      hd

/--
Every proper natural divisor of `2^e`
already divides `2^(e - 1)`.
@isnad1 id=dvd.2h2v.s6.530dd3e00185 from=translated src=- shape=47f1cac4 vocab=2adff775
-/
theorem natProperDivisor_twoPow_dvd_predPow
    (a e : Nat)
    (ha : a ∣ 2 ^ e)
    (hlt : a < 2 ^ e) :
    a ∣ 2 ^ (e - 1) := by
  obtain ⟨k, hkLe, hak⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 ha
  subst a
  have hkLt :
      k < e := by
    exact
      (Nat.pow_lt_pow_iff_right
        (by norm_num : 1 < (2 : Nat))).1
        hlt
  have hkPred :
      k ≤ e - 1 := by
    omega
  exact
    Nat.pow_dvd_pow
      2
      hkPred

/--
If `d` is positive and strictly smaller than the expected
even-case period, then its gcd with that period divides
the expected half-period.
@isnad1 id=dvd.4h2v.s5.f66577459465 from=translated src=- shape=7c7630a4 vocab=48edb3f6
-/
theorem nearestQEvenGcd_dvd_halfPeriod
    (q d : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hdPos : 0 < d)
    (hdLt :
      d < nearestQEvenResiduePeriod q) :
    Nat.gcd
        (nearestQEvenResiduePeriod q)
        d ∣
      nearestQEvenResidueHalfPeriod q := by
  have hgDvdD :
      Nat.gcd
          (nearestQEvenResiduePeriod q)
          d ∣ d :=
    Nat.gcd_dvd_right
      (nearestQEvenResiduePeriod q)
      d
  have hgLeD :
      Nat.gcd
          (nearestQEvenResiduePeriod q)
          d ≤ d :=
    Nat.le_of_dvd
      hdPos
      hgDvdD
  have hgLtPeriod :
      Nat.gcd
          (nearestQEvenResiduePeriod q)
          d <
        nearestQEvenResiduePeriod q :=
    lt_of_le_of_lt
      hgLeD
      hdLt
  have hgDvdPeriod :
      Nat.gcd
          (nearestQEvenResiduePeriod q)
          d ∣
        nearestQEvenResiduePeriod q :=
    Nat.gcd_dvd_left
      (nearestQEvenResiduePeriod q)
      d
  have hgDvdPredPow :
      Nat.gcd
          (nearestQEvenResiduePeriod q)
          d ∣
        2 ^
          ((q - 1 - nearestQTwoAdicOrder q) - 1) := by
    apply
      natProperDivisor_twoPow_dvd_predPow
        (Nat.gcd
          (nearestQEvenResiduePeriod q)
          d)
        (q - 1 - nearestQTwoAdicOrder q)
    · simpa [nearestQEvenResiduePeriod] using
        hgDvdPeriod
    · simpa [nearestQEvenResiduePeriod] using
        hgLtPeriod
  have hexponent :
      (q - 1 - nearestQTwoAdicOrder q) - 1 =
        q - 2 - nearestQTwoAdicOrder q := by
    have hbound :
        nearestQTwoAdicOrder q + 2 ≤ q :=
      nearestQTwoAdicOrder_add_two_le_of_even_ge_six
        q hq hqEven
    omega
  rw [hexponent] at hgDvdPredPow
  simpa [nearestQEvenResidueHalfPeriod] using
    hgDvdPredPow

/--
For even `q ≥ 6`, every positive period of the
nearest-root residue sequence is at least the expected period.
@isnad1 id=le.4h2v.s5.60a02d43b63c from=translated src=- shape=b30670f1 vocab=64895257
-/
theorem nearestQPowerResidueAt_even_period_le
    (q d : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hdPos : 0 < d)
    (hd :
      Function.Periodic
        (nearestQPowerResidueAt q)
        d) :
    nearestQEvenResiduePeriod q ≤ d := by
  by_contra hnot
  have hdLt :
      d < nearestQEvenResiduePeriod q := by
    exact Nat.lt_of_not_ge hnot
  have hgPeriod :
      Function.Periodic
        (nearestQPowerResidueAt q)
        (Nat.gcd
          (nearestQEvenResiduePeriod q)
          d) :=
    nearestQPowerResidueAt_even_gcd_periodic
      q d hq hqEven hd
  have hgDvdHalf :
      Nat.gcd
          (nearestQEvenResiduePeriod q)
          d ∣
        nearestQEvenResidueHalfPeriod q :=
    nearestQEvenGcd_dvd_halfPeriod
      q d hq hqEven hdPos hdLt
  obtain ⟨k, hk⟩ := hgDvdHalf
  have hhalf :
      Function.Periodic
        (nearestQPowerResidueAt q)
        (nearestQEvenResidueHalfPeriod q) := by
    rw [hk]
    simpa [Nat.mul_comm] using
      hgPeriod.nat_mul k
  exact
    (nearestQPowerResidueAt_evenHalfPeriod_not_periodic
      q hq hqEven)
      hhalf

/--
For even `q ≥ 6`, the exact least positive period of the
nearest-root residue sequence is

`2^(q - 1 - ν₂(q))`.
@isnad1 id=isleastp.2h1v.s4.4c3765d566cf from=translated src=- shape=1b3b1243 vocab=7d7aad8f
-/
theorem nearestQPowerResidueAt_even_isLeastPositivePeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    IsLeastPositiveNatPeriod
      (nearestQPowerResidueAt q)
      (nearestQEvenResiduePeriod q) := by
  refine ⟨?_, ?_, ?_⟩
  · have htwo :
        2 ≤ nearestQEvenResiduePeriod q :=
      nearestQEvenResiduePeriod_two_le
        q hq hqEven
    omega
  · exact
      nearestQPowerResidueAt_even_periodic
        q hq hqEven
  · intro d hdPos hdPeriod
    exact
      nearestQPowerResidueAt_even_period_le
        q d hq hqEven hdPos hdPeriod

/--
For even `q ≥ 6`, the exact least positive period of
the nearest-root correction sequence is the same as
that of the residue sequence.
@isnad1 id=isleastp.2h1v.s4.72b34f7ec6cb from=translated src=- shape=02490f5b vocab=e52d03df
-/
theorem nearestQOmegaAt_even_isLeastPositivePeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    IsLeastPositiveNatPeriod
      (nearestQOmegaAt q)
      (nearestQEvenResiduePeriod q) := by
  exact
    (nearestQPowerResidueAt_isLeastPeriod_iff_omega
      q
      (nearestQEvenResiduePeriod q)).1
      (nearestQPowerResidueAt_even_isLeastPositivePeriod
        q hq hqEven)

/--
For even `q ≥ 6`, the exact least positive period of
the correction sequence is explicitly

`2^(q - 1 - ν₂(q))`.
@isnad1 id=isleastp.2h1v.s5.3931cd4301f6 from=translated src=- shape=dad7ae83 vocab=9a8a2fc1
-/
theorem nearestQOmegaAt_even_exactPeriod_formula
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    IsLeastPositiveNatPeriod
      (nearestQOmegaAt q)
      (2 ^ (q - 1 - nearestQTwoAdicOrder q)) := by
  simpa [nearestQEvenResiduePeriod] using
    nearestQOmegaAt_even_isLeastPositivePeriod
      q hq hqEven

/--
The exact least positive period of the nearest-root
residue and correction sequences.

It equals:

* `1` for `q = 2` and `q = 4`;
* `2^(q - 1)` for odd `q`;
* `2^(q - 1 - ν₂(q))` for even `q ≥ 6`.-/
def nearestQExactPeriod
    (q : Nat) : Nat :=
  if q = 2 ∨ q = 4 then
    1
  else if Odd q then
    nearestQResiduePeriod q
  else
    nearestQEvenResiduePeriod q

/--
For every positive exponent, `nearestQExactPeriod q`
is the exact least positive period of the residue sequence.
@isnad1 id=isleastp.1h1v.s4.c48027727789 from=translated src=- shape=9c8b14d8 vocab=90452f01
-/
theorem nearestQPowerResidueAt_isLeastPeriod
    (q : Nat)
    (hq : 0 < q) :
    IsLeastPositiveNatPeriod
      (nearestQPowerResidueAt q)
      (nearestQExactPeriod q) := by
  unfold nearestQExactPeriod
  by_cases hExceptional :
      q = 2 ∨ q = 4
  · rw [ite_eq_left hExceptional]
    rcases hExceptional with hqTwo | hqFour
    · subst q
      exact
        nearestQPowerResidueAt_isLeastPeriod_two
    · subst q
      exact
        nearestQPowerResidueAt_isLeastPeriod_four
  · rw [ite_eq_right hExceptional]
    by_cases hqOdd :
        Odd q
    · rw [ite_eq_left hqOdd]
      exact
        nearestQPowerResidueAt_isLeastPeriod_of_odd
          q hq hqOdd
    · rw [ite_eq_right hqOdd]
      have hqEven :
          Even q := by
        obtain ⟨k, hkEven | hkOdd⟩ :=
          Nat.even_or_odd' q
        · exact
            ⟨k, by
              omega⟩
        · exfalso
          apply hqOdd
          exact
            ⟨k, by
              omega⟩
      have hqNeTwo :
          q ≠ 2 := by
        intro h
        apply hExceptional
        exact Or.inl h
      have hqNeFour :
          q ≠ 4 := by
        intro h
        apply hExceptional
        exact Or.inr h
      have hqSix :
          6 ≤ q := by
        obtain ⟨k, hk⟩ := hqEven
        omega
      exact
        nearestQPowerResidueAt_even_isLeastPositivePeriod
          q hqSix hqEven

/--
For every positive exponent, `nearestQExactPeriod q`
is also the exact least positive period of the
nearest-root correction sequence.
@isnad1 id=isleastp.1h1v.s4.a307d4a71bd0 from=translated src=- shape=e8ad9c19 vocab=cdf37c50
-/
theorem nearestQOmegaAt_isLeastPeriod
    (q : Nat)
    (hq : 0 < q) :
    IsLeastPositiveNatPeriod
      (nearestQOmegaAt q)
      (nearestQExactPeriod q) := by
  exact
    (nearestQPowerResidueAt_isLeastPeriod_iff_omega
      q
      (nearestQExactPeriod q)).1
      (nearestQPowerResidueAt_isLeastPeriod
        q hq)

end RoundedRootSums
