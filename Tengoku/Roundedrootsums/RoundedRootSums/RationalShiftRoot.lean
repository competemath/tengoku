/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftInversion
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Algebra.Order.Floor.Semiring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real roots for rational shifts

This file connects the finite rational-power counting model with
the usual expression involving a real q-th root and natural floor.
-/

namespace RoundedRootSums

/--
The nonnegative real q-th root of `k`, represented as

`k ^ (1 / q)`.

The case `q = 0` is allowed by the definition, but the main
root equivalence theorems will assume `0 < q`.-/
noncomputable def shiftedRealRoot
    (q k : Nat) : Real :=
  (k : Real) ^ ((q : Real)⁻¹)

/--
The real number whose natural floor occurs in the
rationally shifted reciprocal-root sum.-/
noncomputable def shiftedRealRoundedArgument
    (q a b k : Nat) : Real :=
  shiftedRealRoot q k + (a : Real) / (b : Real)

/--
The natural floor of the rationally shifted real q-th root.-/
noncomputable def shiftedRealRoundedValue
    (q a b k : Nat) : Nat :=
  ⌊shiftedRealRoundedArgument q a b k⌋₊

/--
The rationally shifted reciprocal-root sum written using
real q-th roots and natural floors.-/
noncomputable def shiftedRealRoundedSum
    (q a b n : Nat) : Nat :=
  Finset.sum (Finset.Icc 1 n) (fun k =>
    shiftedRealRoundedValue q a b k)

/--
The real q-th root of a natural number is nonnegative.-/
theorem shiftedRealRoot_nonneg
    (q k : Nat) :
    0 ≤ shiftedRealRoot q k := by
  unfold shiftedRealRoot
  exact Real.rpow_nonneg (by positivity) _

/--
The shifted real-root argument is nonnegative when `b > 0`.-/
theorem shiftedRealRoundedArgument_nonneg
    (q a b k : Nat)
    (hb : 0 < b) :
    0 ≤ shiftedRealRoundedArgument q a b k := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have hshift :
      0 ≤ (a : Real) / (b : Real) := by
    exact div_nonneg (by positivity) (le_of_lt hbReal)
  unfold shiftedRealRoundedArgument
  exact add_nonneg
    (shiftedRealRoot_nonneg q k)
    hshift

/--
The shifted real base corresponding to level `m + 1`
is nonnegative under the standard assumptions `a < b`.-/
theorem shiftedRealBase_nonneg
    (a b m : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    0 ≤
      (((m + 1 : Nat) : Real) -
        (a : Real) / (b : Real)) := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have haReal : (a : Real) < (b : Real) := by
    exact_mod_cast ha
  have hdiv :
      (a : Real) / (b : Real) < 1 := by
    exact (div_lt_one hbReal).2 haReal
  have hm :
      (1 : Real) ≤ ((m + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  linarith

/--
For a positive exponent `q`, lying below the real q-th root
is equivalent to the corresponding q-th power inequality.-/
theorem shiftedRealBase_le_root_iff
    (q a b k m : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    (((m + 1 : Nat) : Real) -
          (a : Real) / (b : Real) ≤
        shiftedRealRoot q k) ↔
      ((((m + 1 : Nat) : Real) -
          (a : Real) / (b : Real)) ^ q ≤
        (k : Real)) := by
  have hqReal : (0 : Real) < (q : Real) := by
    exact_mod_cast hq
  have hbase :
      0 ≤
        (((m + 1 : Nat) : Real) -
          (a : Real) / (b : Real)) :=
    shiftedRealBase_nonneg a b m hb ha
  have hkReal : (0 : Real) ≤ (k : Real) := by
    positivity
  unfold shiftedRealRoot
  simpa using
    (Real.le_rpow_inv_iff_of_pos
      hbase hkReal hqReal)

/--
A positive integer level `m + 1` lies below the natural floor
of the shifted real q-th root exactly when its shifted q-th
power does not exceed `k`.-/
theorem shiftedLevel_le_realRoundedValue_iff
    (q a b k m : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    m + 1 ≤ shiftedRealRoundedValue q a b k ↔
      ((((m + 1 : Nat) : Real) -
          (a : Real) / (b : Real)) ^ q ≤
        (k : Real)) := by
  unfold shiftedRealRoundedValue
  rw [Nat.le_floor_iff
    (shiftedRealRoundedArgument_nonneg
      q a b k hb)]
  unfold shiftedRealRoundedArgument
  constructor
  · intro h
    have hbase :
        (((m + 1 : Nat) : Real) -
            (a : Real) / (b : Real)) ≤
          shiftedRealRoot q k := by
      linarith
    exact
      (shiftedRealBase_le_root_iff
        q a b k m hq hb ha).mp hbase
  · intro hpow
    have hbase :
        (((m + 1 : Nat) : Real) -
            (a : Real) / (b : Real)) ≤
          shiftedRealRoot q k :=
      (shiftedRealBase_le_root_iff
        q a b k m hq hb ha).mpr hpow
    linarith

/--
The shifted power inequality over the reals is equivalent to
the corresponding inequality over the rationals.-/
theorem shiftedRealPower_le_iff_ratPower
    (q a b k m : Nat) :
    ((((m + 1 : Nat) : Real) -
          (a : Real) / (b : Real)) ^ q ≤
        (k : Real)) ↔
      ((((m + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat)) ^ q ≤
        (k : Rat)) := by
  simpa only [
    Rat.cast_pow,
    Rat.cast_sub,
    Rat.cast_div,
    Rat.cast_natCast
  ] using
    (Rat.cast_le
      (K := Real)
      (p :=
        ((((m + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat)) ^ q))
      (q := (k : Rat)))

/--
A positive integer level lies below the natural floor of the
shifted real q-th root exactly when the corresponding rational
shifted power does not exceed `k`.-/
theorem shiftedLevel_le_realRoundedValue_iff_ratPower
    (q a b k m : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    m + 1 ≤ shiftedRealRoundedValue q a b k ↔
      ((((m + 1 : Nat) : Rat) -
          (a : Rat) / (b : Rat)) ^ q ≤
        (k : Rat)) := by
  calc
    m + 1 ≤ shiftedRealRoundedValue q a b k ↔
        ((((m + 1 : Nat) : Real) -
            (a : Real) / (b : Real)) ^ q ≤
          (k : Real)) :=
      shiftedLevel_le_realRoundedValue_iff
        q a b k m hq hb ha
    _ ↔
        ((((m + 1 : Nat) : Rat) -
            (a : Rat) / (b : Rat)) ^ q ≤
          (k : Rat)) :=
      shiftedRealPower_le_iff_ratPower
        q a b k m

/--
Once the level bound `t` is at least the shifted real rounded value,
the direct rational-power count equals that rounded value.-/
theorem shiftedPowerCount_eq_realRoundedValue_of_le
    (q a b k t : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b)
    (ht :
      shiftedRealRoundedValue q a b k ≤ t) :
    shiftedPowerCount q a b k t =
      shiftedRealRoundedValue q a b k := by
  unfold shiftedPowerCount
  have hfilter :
      (Finset.range t).filter (fun m =>
          ((((m + 1 : Nat) : Rat) -
              (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat)) =
        Finset.range
          (shiftedRealRoundedValue q a b k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hm
      have hmle :
          m + 1 ≤ shiftedRealRoundedValue q a b k :=
        (shiftedLevel_le_realRoundedValue_iff_ratPower
          q a b k m hq hb ha).mpr hm.2
      exact Nat.lt_of_succ_le hmle
    · intro hm
      have hmt : m < t :=
        lt_of_lt_of_le hm ht
      have hmle :
          m + 1 ≤ shiftedRealRoundedValue q a b k :=
        Nat.succ_le_iff.mpr hm
      have hpow :
          ((((m + 1 : Nat) : Rat) -
              (a : Rat) / (b : Rat)) ^ q) ≤ (k : Rat) :=
        (shiftedLevel_le_realRoundedValue_iff_ratPower
          q a b k m hq hb ha).mp hmle
      exact ⟨hmt, hpow⟩
  rw [hfilter]
  simp

/--
Using the shifted real rounded value itself as the level bound,
the rational-power count returns exactly that value.-/
theorem shiftedPowerCount_at_realRoundedValue
    (q a b k : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedPowerCount q a b k
        (shiftedRealRoundedValue q a b k) =
      shiftedRealRoundedValue q a b k := by
  exact shiftedPowerCount_eq_realRoundedValue_of_le
    q a b k
      (shiftedRealRoundedValue q a b k)
      hq hb ha
      (Nat.le_refl _)

/--
For a positive exponent `q`, the real q-th root of `k`
is at most `k`.-/
theorem shiftedRealRoot_le_nat
    (q k : Nat)
    (hq : 0 < q) :
    shiftedRealRoot q k ≤ (k : Real) := by
  have hqReal : (0 : Real) < (q : Real) := by
    exact_mod_cast hq
  have hkReal : (0 : Real) ≤ (k : Real) := by
    positivity
  have hkpowNat : k ≤ k ^ q := by
    exact Nat.le_self_pow (Nat.ne_of_gt hq) k
  have hkpowReal :
      (k : Real) ≤ (k : Real) ^ q := by
    exact_mod_cast hkpowNat
  unfold shiftedRealRoot
  apply
    (Real.rpow_inv_le_iff_of_pos
      hkReal hkReal hqReal).2
  simpa only [Real.rpow_natCast] using hkpowReal

/--
Under the standard assumptions, the shifted rounded value at `k`
is at most `k + 1`.-/
theorem shiftedRealRoundedValue_le_succ
    (q a b k : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRealRoundedValue q a b k ≤ k + 1 := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have haReal : (a : Real) < (b : Real) := by
    exact_mod_cast ha
  have hshift :
      (a : Real) / (b : Real) < 1 := by
    exact (div_lt_one hbReal).2 haReal
  have hroot :
      shiftedRealRoot q k ≤ (k : Real) :=
    shiftedRealRoot_le_nat q k hq
  unfold shiftedRealRoundedValue
  apply Nat.floor_le_of_le
  unfold shiftedRealRoundedArgument
  have hlt :
      shiftedRealRoot q k +
          (a : Real) / (b : Real) <
        (k : Real) + 1 := by
    linarith
  simpa using le_of_lt hlt

/--
For `k ≤ n`, the common level bound `n + 1` is large enough
to recover the full shifted real rounded value.-/
theorem shiftedPowerCount_eq_realRoundedValue_commonBound
    (q a b n k : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b)
    (hk : k ≤ n) :
    shiftedPowerCount q a b k (n + 1) =
      shiftedRealRoundedValue q a b k := by
  exact shiftedPowerCount_eq_realRoundedValue_of_le
    q a b k (n + 1) hq hb ha
    (le_trans
      (shiftedRealRoundedValue_le_succ
        q a b k hq hb ha)
      (Nat.succ_le_succ hk))

/--
The sum written with real q-th roots and natural floors agrees
with the rational-power counting model.-/
theorem shiftedRealRoundedSum_eq_powerRoundedSum
    (q a b n : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRealRoundedSum q a b n =
      shiftedPowerRoundedSum q a b n := by
  unfold shiftedRealRoundedSum
  unfold shiftedPowerRoundedSum shiftedPowerCountSum
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n :=
    (Finset.mem_Icc.mp hk).2
  exact
    (shiftedPowerCount_eq_realRoundedValue_commonBound
      q a b n k hq hb ha hkn).symm

/--
The natural maximal level is exactly the shifted real rounded
value evaluated at `n`.-/
theorem shiftedMaxLevel_eq_realRoundedValue
    (q a b n : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedMaxLevel q a b n =
      shiftedRealRoundedValue q a b n := by
  unfold shiftedMaxLevel
  exact shiftedPowerCount_eq_realRoundedValue_commonBound
    q a b n n hq hb ha (Nat.le_refl n)

/--
Exact inversion for rationally shifted real q-th root sums.

This is the explicit formula

`R(n) = t * (n + 1) - ∑_{m=1}^{t} ⌈(m - a / b)^q⌉`,

where

`t = ⌊n^(1/q) + a / b⌋`.-/
theorem shiftedRealRoundedSum_explicit_formula
    (q a b n : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    shiftedRealRoundedSum q a b n =
      shiftedRealRoundedValue q a b n * (n + 1) -
        shiftedThresholdSum q a b
          (shiftedRealRoundedValue q a b n) := by
  calc
    shiftedRealRoundedSum q a b n =
        shiftedPowerRoundedSum q a b n :=
      shiftedRealRoundedSum_eq_powerRoundedSum
        q a b n hq hb ha
    _ =
        shiftedMaxLevel q a b n * (n + 1) -
          shiftedThresholdSum q a b
            (shiftedMaxLevel q a b n) :=
      shiftedPowerRoundedSum_explicit_formula
        q a b n hb ha
    _ =
        shiftedRealRoundedValue q a b n * (n + 1) -
          shiftedThresholdSum q a b
            (shiftedRealRoundedValue q a b n) := by
      rw [shiftedMaxLevel_eq_realRoundedValue
        q a b n hq hb ha]

end RoundedRootSums
