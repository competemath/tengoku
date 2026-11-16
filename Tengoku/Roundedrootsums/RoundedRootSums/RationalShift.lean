/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku
import Tengoku.Seed.Data.Rat.Floor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rational shifts

Auxiliary definitions and lemmas for thresholds involving rational shifts.
-/

namespace RoundedRootSums

/--
The integer threshold obtained by taking the ceiling of

`(m - a / b) ^ q`

in the rational numbers.-/
def shiftedThreshold
    (q a b m : Nat) : Int :=
  Int.ceil (((m : Rat) - (a : Rat) / (b : Rat)) ^ q)

/--
The shifted threshold is nonnegative whenever `b > 0` and `a ≤ b * m`.
@isnad1 id=le.2h4v.s5.7ebec79426c4 from=translated src=- shape=0cb730e5 vocab=9fd51361
-/
theorem shiftedThreshold_nonneg
    (q a b m : Nat)
    (hb : 0 < b)
    (ham : a ≤ b * m) :
    0 ≤ shiftedThreshold q a b m := by
  unfold shiftedThreshold
  have hbRat : (0 : Rat) < (b : Rat) := by
    exact_mod_cast hb
  have hamRat :
      (a : Rat) ≤ (b : Rat) * (m : Rat) := by
    exact_mod_cast ham
  have hbase :
      0 ≤ (m : Rat) - (a : Rat) / (b : Rat) := by
    rw [sub_nonneg]
    apply (div_le_iff₀ hbRat).2
    simpa [mul_comm] using hamRat
  apply Int.ceil_nonneg
  exact pow_nonneg hbase q

/--
The natural-number version of the shifted threshold

`⌈(m - a / b)^q⌉`.

The integer ceiling is converted to a natural number using `Int.toNat`.
Under the usual assumptions `b > 0` and `a ≤ b * m`, this conversion
does not lose information because the threshold is nonnegative.-/
def shiftedThresholdNat
    (q a b m : Nat) : Nat :=
  (shiftedThreshold q a b m).toNat

/--
When the shifted threshold is nonnegative, converting it to `Nat`
and then back to `Int` recovers the original threshold.
@isnad1 id=eq.2h4v.s5.dfbd089a9198 from=translated src=- shape=d109b8e4 vocab=be1bfd9e
-/
theorem shiftedThresholdNat_cast
    (q a b m : Nat)
    (hb : 0 < b)
    (ham : a ≤ b * m) :
    (shiftedThresholdNat q a b m : Int) =
      shiftedThreshold q a b m := by
  unfold shiftedThresholdNat
  rw [Int.toNat_of_nonneg (shiftedThreshold_nonneg q a b m hb ham)]

/--
The natural shifted threshold is at most `k` exactly when the
underlying rational power is at most `k`.
@isnad1 id=iff.2h5v.s6.1916af32e913 from=translated src=- shape=a8890e4e vocab=ed554103
-/
theorem shiftedThresholdNat_le_iff
    (q a b m k : Nat)
    (hb : 0 < b)
    (ham : a ≤ b * m) :
    shiftedThresholdNat q a b m ≤ k ↔
      (((m : Rat) - (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat) := by
  constructor
  · intro h
    have hInt :
        shiftedThreshold q a b m ≤ (k : Int) := by
      rw [← shiftedThresholdNat_cast q a b m hb ham]
      exact_mod_cast h
    simpa [shiftedThreshold] using (Int.ceil_le.mp hInt)
  · intro h
    have hInt :
        shiftedThreshold q a b m ≤ (k : Int) := by
      unfold shiftedThreshold
      exact Int.ceil_le.mpr h
    rw [← shiftedThresholdNat_cast q a b m hb ham] at hInt
    exact_mod_cast hInt

/--
The finite counting expression appearing in the exact inversion formula
for rationally shifted reciprocal-root sums.

The index `m` runs through `1, ..., t`.-/
def shiftedInversionSum
    (q a b n t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun m =>
    n + 1 - shiftedThresholdNat q a b (m + 1))

/--
Adding one more threshold appends one more counting term
to the shifted inversion sum.
@isnad1 id=eq.0h5v.s6.e5b2c03ba7a0 from=translated src=- shape=ea18a83a vocab=9d0f59ef
-/
theorem shiftedInversionSum_succ
    (q a b n t : Nat) :
    shiftedInversionSum q a b n (t + 1) =
      shiftedInversionSum q a b n t +
        (n + 1 - shiftedThresholdNat q a b (t + 1)) := by
  simp [shiftedInversionSum, Finset.sum_range_succ]

/--
Under the standard shift assumptions `a < b` and `m > 0`,
the natural shifted threshold is strictly positive.
@isnad1 id=lt.3h4v.s5.62670472587e from=translated src=- shape=a6881cae vocab=b7b400cb
-/
theorem shiftedThresholdNat_pos
    (q a b m : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hm : 0 < m) :
    0 < shiftedThresholdNat q a b m := by
  have hm1 : 1 ≤ m := Nat.succ_le_iff.mp hm
  have ham : a ≤ b * m := by
    calc
      a ≤ b := Nat.le_of_lt ha
      _ = b * 1 := by simp
      _ ≤ b * m := Nat.mul_le_mul_left b hm1
  have hbRat : (0 : Rat) < (b : Rat) := by
    exact_mod_cast hb
  have haRat : (a : Rat) < (b : Rat) := by
    exact_mod_cast ha
  have hmRat : (1 : Rat) ≤ (m : Rat) := by
    exact_mod_cast hm1
  have hbase :
      (0 : Rat) <
        (m : Rat) - (a : Rat) / (b : Rat) := by
    rw [sub_pos]
    have hdiv_lt_one :
        (a : Rat) / (b : Rat) < 1 := by
      exact (div_lt_one hbRat).2 haRat
    exact lt_of_lt_of_le hdiv_lt_one hmRat
  have hpow :
      (0 : Rat) <
        (((m : Rat) - (a : Rat) / (b : Rat)) ^ q) := by
    exact pow_pos hbase q
  have hInt :
      (0 : Int) < shiftedThreshold q a b m := by
    unfold shiftedThreshold
    exact Int.ceil_pos.mpr hpow
  rw [← shiftedThresholdNat_cast q a b m hb ham] at hInt
  exact_mod_cast hInt

/--
The number of positive integers `k ≤ n` that lie at or above
the rationally shifted threshold.-/
def shiftedThresholdCount
    (q a b n m : Nat) : Nat :=
  ((Finset.Icc 1 n).filter
    (fun k => shiftedThresholdNat q a b m ≤ k)).card

/--
The number of positive integers `k ≤ n` lying at or above the
shifted threshold is `n + 1 - shiftedThresholdNat q a b m`.
@isnad1 id=eq.3h5v.s6.771e8c8c5caf from=translated src=- shape=342991d3 vocab=991d816d
-/
theorem shiftedThresholdCount_eq
    (q a b n m : Nat)
    (hb : 0 < b)
    (ha : a < b)
    (hm : 0 < m) :
    shiftedThresholdCount q a b n m =
      n + 1 - shiftedThresholdNat q a b m := by
  have hpos :
      1 ≤ shiftedThresholdNat q a b m :=
    shiftedThresholdNat_pos q a b m hb ha hm
  have hfilter :
      (Finset.Icc 1 n).filter
          (fun k => shiftedThresholdNat q a b m ≤ k) =
        Finset.Icc (shiftedThresholdNat q a b m) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hk
      exact ⟨hk.2, hk.1.2⟩
    · intro hk
      exact ⟨⟨le_trans hpos hk.1, hk.2⟩, hk.1⟩
  unfold shiftedThresholdCount
  rw [hfilter]
  exact Nat.card_Icc (shiftedThresholdNat q a b m) n

/--
The total number of threshold incidences for levels `1, ..., t`.-/
def shiftedCountSum
    (q a b n t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun m =>
    shiftedThresholdCount q a b n (m + 1))

/--
Summing the explicit threshold counts gives the shifted inversion sum.
@isnad1 id=eq.2h5v.s5.7c83b013ad50 from=translated src=- shape=a88f716c vocab=962d5733
-/
theorem shiftedCountSum_eq_inversionSum
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedCountSum q a b n t =
      shiftedInversionSum q a b n t := by
  unfold shiftedCountSum shiftedInversionSum
  apply Finset.sum_congr rfl
  intro m _hm
  exact shiftedThresholdCount_eq
    q a b n (m + 1) hb ha (Nat.succ_pos m)

/--
The number of levels among `1, ..., t` whose shifted threshold
does not exceed `k`.-/
def shiftedLevelCount
    (q a b k t : Nat) : Nat :=
  ((Finset.range t).filter
    (fun m => shiftedThresholdNat q a b (m + 1) ≤ k)).card

/--
The total number of threshold incidences, counted first by `k`.-/
def shiftedLevelCountSum
    (q a b n t : Nat) : Nat :=
  Finset.sum (Finset.Icc 1 n) (fun k =>
    shiftedLevelCount q a b k t)

/--
The finite set of incidence pairs `(m, k)` such that

- `m` represents one of the levels `1, ..., t`,
- `k` lies in `1, ..., n`,
- the shifted threshold for level `m + 1` does not exceed `k`.-/
def shiftedIncidencePairs
    (q a b n t : Nat) : Finset (Nat × Nat) :=
  ((Finset.range t).product (Finset.Icc 1 n)).filter
    (fun p =>
      shiftedThresholdNat q a b (p.1 + 1) ≤ p.2)

/--
A pair `(m, k)` belongs to `shiftedIncidencePairs` exactly when
all four defining inequalities hold.
@isnad1 id=iff.0h7v.s6.77969f40bb57 from=translated src=- shape=79ef2725 vocab=c7eeb08b
-/
theorem mem_shiftedIncidencePairs_iff
    (q a b n t m k : Nat) :
    (m, k) ∈ shiftedIncidencePairs q a b n t ↔
      m < t ∧
      1 ≤ k ∧
      k ≤ n ∧
      shiftedThresholdNat q a b (m + 1) ≤ k := by
  simp [shiftedIncidencePairs, and_assoc]

/--
The indicator of a threshold incidence.

It is `1` when the shifted threshold for level `m + 1`
does not exceed `k`, and `0` otherwise.-/
def shiftedIncidenceIndicator
    (q a b m k : Nat) : Nat :=
  if shiftedThresholdNat q a b (m + 1) ≤ k then 1 else 0

/--
The threshold count is the sum of its incidence indicators over `k`.
@isnad1 id=eq.0h5v.s5.f741cab5e359 from=translated src=- shape=d48e4286 vocab=507c1e55
-/
theorem shiftedThresholdCount_eq_sum_indicator
    (q a b n m : Nat) :
    shiftedThresholdCount q a b n (m + 1) =
      Finset.sum (Finset.Icc 1 n) (fun k =>
        shiftedIncidenceIndicator q a b m k) := by
  classical
  unfold shiftedThresholdCount shiftedIncidenceIndicator
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]

/--
The level count is the sum of the same incidence indicators over `m`.
@isnad1 id=eq.0h5v.s5.51564ed54a06 from=translated src=- shape=bd8c52f5 vocab=22781cdc
-/
theorem shiftedLevelCount_eq_sum_indicator
    (q a b k t : Nat) :
    shiftedLevelCount q a b k t =
      Finset.sum (Finset.range t) (fun m =>
        shiftedIncidenceIndicator q a b m k) := by
  classical
  unfold shiftedLevelCount shiftedIncidenceIndicator
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]

/--
The total number of threshold incidences is the same whether
the pairs are counted first by levels or first by values of `k`.
@isnad1 id=eq.0h5v.s4.83067c779035 from=translated src=- shape=37b02ddb vocab=8edd08e3
-/
theorem shiftedCountSum_eq_levelCountSum
    (q a b n t : Nat) :
    shiftedCountSum q a b n t =
      shiftedLevelCountSum q a b n t := by
  unfold shiftedCountSum shiftedLevelCountSum
  simp_rw [shiftedThresholdCount_eq_sum_indicator]
  simp_rw [shiftedLevelCount_eq_sum_indicator]
  exact Finset.sum_comm

/--
Counting threshold incidences first by `k` gives the explicit
shifted inversion sum.
@isnad1 id=eq.2h5v.s5.5d01fb22dbe7 from=translated src=- shape=a88f716c vocab=c250c207
-/
theorem shiftedLevelCountSum_eq_inversionSum
    (q a b n t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedLevelCountSum q a b n t =
      shiftedInversionSum q a b n t := by
  calc
    shiftedLevelCountSum q a b n t =
        shiftedCountSum q a b n t :=
      (shiftedCountSum_eq_levelCountSum q a b n t).symm
    _ = shiftedInversionSum q a b n t :=
      shiftedCountSum_eq_inversionSum q a b n t hb ha

end RoundedRootSums
