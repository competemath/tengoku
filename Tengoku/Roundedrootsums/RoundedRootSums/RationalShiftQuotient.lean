/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftResidue
import Tengoku.Seed.Data.Nat.Choose.Sum
import Tengoku.Seed.NumberTheory.Bernoulli

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quotient sums for rational shifts

This file develops the decomposition of the quotient sum

`∑ₘ (b * m - a)^q / b^q`

into a polynomial numerator sum and a periodic residue sum.
-/

namespace RoundedRootSums

/--
The sum of the shifted power numerators over levels `1, ..., t`.-/
def shiftedPowerNumeratorSum
    (q a b t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun m =>
    shiftedPowerNumerator q a b (m + 1))

/--
The sum of the shifted power residues over levels `1, ..., t`.-/
def shiftedPowerResidueSum
    (q a b t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun m =>
    shiftedPowerResidue q a b (m + 1))

/--
For one level, denominator times quotient plus residue
recovers the original numerator.
@isnad1 id=eq.0h4v.s5.8addfd87f96f from=translated src=- shape=60c2a80f vocab=3dcd37d6
-/
theorem shiftedPowerDenominator_mul_quotient_add_residue
    (q a b m : Nat) :
    shiftedPowerDenominator q b *
        (shiftedPowerNumerator q a b m /
          shiftedPowerDenominator q b) +
      shiftedPowerResidue q a b m =
    shiftedPowerNumerator q a b m := by
  simpa [Nat.add_comm] using
    (shiftedPowerResidue_add_denominator_mul_div
      q a b m)

/--
For the complete finite sum, denominator times the quotient sum
plus the residue sum recovers the numerator sum.
@isnad1 id=eq.0h4v.s5.dd1b49cf52b7 from=translated src=- shape=04cc4d05 vocab=bc7d663f
-/
theorem shiftedPowerDenominator_mul_quotientSum_add_residueSum
    (q a b t : Nat) :
    shiftedPowerDenominator q b *
        shiftedPowerQuotientSum q a b t +
      shiftedPowerResidueSum q a b t =
    shiftedPowerNumeratorSum q a b t := by
  unfold shiftedPowerQuotientSum
  unfold shiftedPowerResidueSum
  unfold shiftedPowerNumeratorSum
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  exact shiftedPowerDenominator_mul_quotient_add_residue
    q a b (m + 1)

/--
Subtracting the residue sum from the numerator sum leaves
the denominator times the quotient sum.
@isnad1 id=eq.0h4v.s5.e2808a0c360c from=translated src=- shape=ce0bf253 vocab=6120ceea
-/
theorem shiftedPowerNumeratorSum_sub_residueSum
    (q a b t : Nat) :
    shiftedPowerNumeratorSum q a b t -
        shiftedPowerResidueSum q a b t =
      shiftedPowerDenominator q b *
        shiftedPowerQuotientSum q a b t := by
  have h :=
    shiftedPowerDenominator_mul_quotientSum_add_residueSum
      q a b t
  omega

/--
The quotient sum is obtained by subtracting the residue sum
from the numerator sum and dividing by the common denominator.
@isnad1 id=eq.1h4v.s5.1e0db6f83289 from=translated src=- shape=221fd2b0 vocab=d20dac39
-/
theorem shiftedPowerQuotientSum_eq_sub_residue_div
    (q a b t : Nat)
    (hb : 0 < b) :
    shiftedPowerQuotientSum q a b t =
      (shiftedPowerNumeratorSum q a b t -
          shiftedPowerResidueSum q a b t) /
        shiftedPowerDenominator q b := by
  have hD :
      shiftedPowerDenominator q b ≠ 0 :=
    Nat.ne_of_gt
      (shiftedPowerDenominator_pos q b hb)
  rw [shiftedPowerNumeratorSum_sub_residueSum]
  simp [hD]

/--
The integer form of the shifted power numerator.

Using integers allows us to apply the binomial theorem
directly to the subtraction `b * m - a`.-/
def shiftedPowerNumeratorInt
    (q a b m : Nat) : Int :=
  ((b : Int) * (m : Int) - (a : Int)) ^ q

/--
When the natural subtraction is nontruncated, the natural
and integer versions of the shifted numerator agree.
@isnad1 id=eq.1h4v.s5.b4d94b58f8ed from=translated src=- shape=e95986fe vocab=73b945f4
-/
theorem shiftedPowerNumerator_cast_int
    (q a b m : Nat)
    (ham : a ≤ b * m) :
    (shiftedPowerNumerator q a b m : Int) =
      shiftedPowerNumeratorInt q a b m := by
  simp [shiftedPowerNumerator, shiftedPowerNumeratorInt,
    Nat.cast_sub ham]

/--
One term in the binomial expansion of `(b * m - a)^q`.-/
def shiftedPowerBinomialTerm
    (q a b m j : Nat) : Int :=
  (-1 : Int) ^ (j + q) *
    ((b : Int) * (m : Int)) ^ j *
    (a : Int) ^ (q - j) *
    (q.choose j : Int)

/--
The integer shifted power numerator has its full
binomial expansion.
@isnad1 id=eq.0h4v.s5.b91ac45a5123 from=translated src=- shape=1715881f vocab=c8fad4cc
-/
theorem shiftedPowerNumeratorInt_eq_binomialSum
    (q a b m : Nat) :
    shiftedPowerNumeratorInt q a b m =
      Finset.sum (Finset.range (q + 1)) (fun j =>
        shiftedPowerBinomialTerm q a b m j) := by
  simpa [shiftedPowerNumeratorInt, shiftedPowerBinomialTerm] using
    (sub_pow
      ((b : Int) * (m : Int))
      (a : Int)
      q)

/--
The sum of the integer shifted power numerators
over levels `1, ..., t`.-/
def shiftedPowerNumeratorIntSum
    (q a b t : Nat) : Int :=
  Finset.sum (Finset.range t) (fun m =>
    shiftedPowerNumeratorInt q a b (m + 1))

/--
Under the standard shift assumption `a < b`, casting the natural
numerator sum to integers gives the integer numerator sum.
@isnad1 id=eq.1h4v.s4.e08bd86d60c3 from=translated src=- shape=1952d6df vocab=35efe406
-/
theorem shiftedPowerNumeratorSum_cast_int
    (q a b t : Nat)
    (ha : a < b) :
    (shiftedPowerNumeratorSum q a b t : Int) =
      shiftedPowerNumeratorIntSum q a b t := by
  unfold shiftedPowerNumeratorSum
  unfold shiftedPowerNumeratorIntSum
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  apply shiftedPowerNumerator_cast_int
  calc
    a ≤ b := Nat.le_of_lt ha
    _ = b * 1 := by simp
    _ ≤ b * (m + 1) :=
      Nat.mul_le_mul_left b
        (Nat.succ_le_succ (Nat.zero_le m))

/--
Summing the binomial expansion over all levels gives
a finite double sum.
@isnad1 id=eq.0h4v.s5.37e439ba65f5 from=translated src=- shape=e76aa28d vocab=58aa6ab2
-/
theorem shiftedPowerNumeratorIntSum_eq_binomialDoubleSum
    (q a b t : Nat) :
    shiftedPowerNumeratorIntSum q a b t =
      Finset.sum (Finset.range t) (fun m =>
        Finset.sum (Finset.range (q + 1)) (fun j =>
          shiftedPowerBinomialTerm q a b (m + 1) j)) := by
  unfold shiftedPowerNumeratorIntSum
  apply Finset.sum_congr rfl
  intro m _hm
  exact shiftedPowerNumeratorInt_eq_binomialSum
    q a b (m + 1)

/--
The two finite sums may be interchanged, grouping together
all terms having the same power index `j`.
@isnad1 id=eq.0h4v.s5.684e0276e199 from=translated src=- shape=a3171421 vocab=58aa6ab2
-/
theorem shiftedPowerNumeratorIntSum_eq_binomialSum_swapped
    (q a b t : Nat) :
    shiftedPowerNumeratorIntSum q a b t =
      Finset.sum (Finset.range (q + 1)) (fun j =>
        Finset.sum (Finset.range t) (fun m =>
          shiftedPowerBinomialTerm q a b (m + 1) j)) := by
  calc
    shiftedPowerNumeratorIntSum q a b t =
        Finset.sum (Finset.range t) (fun m =>
          Finset.sum (Finset.range (q + 1)) (fun j =>
            shiftedPowerBinomialTerm q a b (m + 1) j)) :=
      shiftedPowerNumeratorIntSum_eq_binomialDoubleSum
        q a b t
    _ =
        Finset.sum (Finset.range (q + 1)) (fun j =>
          Finset.sum (Finset.range t) (fun m =>
            shiftedPowerBinomialTerm q a b (m + 1) j)) := by
      exact Finset.sum_comm

/--
The integer power sum over the positive integers `1, ..., t`.-/
def positivePowerSumInt
    (j t : Nat) : Int :=
  Finset.sum (Finset.range t) (fun m =>
    (((m + 1 : Nat) : Int) ^ j))

/--
The coefficient of the power sum with exponent `j`
in the binomial expansion of `(b * m - a)^q`.-/
def shiftedPowerBinomialCoefficient
    (q a b j : Nat) : Int :=
  (-1 : Int) ^ (j + q) *
    (b : Int) ^ j *
    (a : Int) ^ (q - j) *
    (q.choose j : Int)

/--
Each binomial term is its coefficient times `m^j`.
@isnad1 id=eq.0h5v.s5.050c547470f8 from=translated src=- shape=a77be3e3 vocab=55e3a0a3
-/
theorem shiftedPowerBinomialTerm_eq_coefficient_mul_power
    (q a b m j : Nat) :
    shiftedPowerBinomialTerm q a b m j =
      shiftedPowerBinomialCoefficient q a b j *
        (m : Int) ^ j := by
  unfold shiftedPowerBinomialTerm
  unfold shiftedPowerBinomialCoefficient
  rw [mul_pow]
  ring

/--
For a fixed exponent `j`, summing the corresponding binomial
terms gives the coefficient times the standard power sum.
@isnad1 id=eq.0h5v.s5.84093c033dbc from=translated src=- shape=f107d404 vocab=91d56979
-/
theorem shiftedPowerBinomialInnerSum_eq_coefficient_mul_powerSum
    (q a b t j : Nat) :
    Finset.sum (Finset.range t) (fun m =>
        shiftedPowerBinomialTerm q a b (m + 1) j) =
      shiftedPowerBinomialCoefficient q a b j *
        positivePowerSumInt j t := by
  unfold positivePowerSumInt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  exact shiftedPowerBinomialTerm_eq_coefficient_mul_power
    q a b (m + 1) j

/--
The complete numerator sum is a linear combination of
the standard positive-integer power sums.
@isnad1 id=eq.0h4v.s5.9179710e5f20 from=translated src=- shape=af035f7b vocab=8d9a2382
-/
theorem shiftedPowerNumeratorIntSum_eq_coefficientPowerSums
    (q a b t : Nat) :
    shiftedPowerNumeratorIntSum q a b t =
      Finset.sum (Finset.range (q + 1)) (fun j =>
        shiftedPowerBinomialCoefficient q a b j *
          positivePowerSumInt j t) := by
  rw [shiftedPowerNumeratorIntSum_eq_binomialSum_swapped]
  apply Finset.sum_congr rfl
  intro j _hj
  exact
    shiftedPowerBinomialInnerSum_eq_coefficient_mul_powerSum
      q a b t j

/--
The rational-valued power sum over the positive integers
`1, ..., t`.-/
def positivePowerSumRat
    (j t : Nat) : Rat :=
  Finset.sum (Finset.range t) (fun m =>
    (((m + 1 : Nat) : Rat) ^ j))

/--
Casting the integer power sum to the rationals gives the
rational-valued power sum.
@isnad1 id=eq.0h2v.s3.f7120c6ba1b6 from=translated src=- shape=ef554e1c vocab=5d572d55
-/
theorem positivePowerSumInt_cast_rat
    (j t : Nat) :
    (positivePowerSumInt j t : Rat) =
      positivePowerSumRat j t := by
  simp [positivePowerSumInt, positivePowerSumRat]

/--
The Bernoulli-number expression for the positive power sum.-/
noncomputable def positivePowerSumBernoulli
    (j t : Nat) : Rat :=
  Finset.sum (Finset.range (j + 1)) (fun i =>
    bernoulli' i *
      ((j + 1).choose i : Rat) *
      (t : Rat) ^ (j + 1 - i) /
      ((j : Rat) + 1))

/--
Faulhaber's formula for the sum of the positive j-th powers
`1^j + ... + t^j`.
@isnad1 id=eq.0h2v.s3.764a776b236d from=translated src=- shape=e4af5fdd vocab=34afeee3
-/
theorem positivePowerSumRat_eq_bernoulli
    (j t : Nat) :
    positivePowerSumRat j t =
      positivePowerSumBernoulli j t := by
  unfold positivePowerSumRat
  unfold positivePowerSumBernoulli
  simpa [Finset.sum_Ico_eq_sum_range, Nat.add_comm] using
    (sum_Ico_pow t j)

/--
The Bernoulli-expanded rational expression for the complete
shifted power numerator sum.-/
noncomputable def shiftedPowerNumeratorBernoulli
    (q a b t : Nat) : Rat :=
  Finset.sum (Finset.range (q + 1)) (fun j =>
    (shiftedPowerBinomialCoefficient q a b j : Rat) *
      positivePowerSumBernoulli j t)

/--
Casting the integer numerator sum to the rationals gives
its Bernoulli-expanded expression.
@isnad1 id=eq.0h4v.s4.818a8b31bb96 from=translated src=- shape=ac8fadc5 vocab=d0877b19
-/
theorem shiftedPowerNumeratorIntSum_cast_rat_eq_bernoulli
    (q a b t : Nat) :
    (shiftedPowerNumeratorIntSum q a b t : Rat) =
      shiftedPowerNumeratorBernoulli q a b t := by
  rw [shiftedPowerNumeratorIntSum_eq_coefficientPowerSums]
  unfold shiftedPowerNumeratorBernoulli
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Int.cast_mul]
  rw [positivePowerSumInt_cast_rat]
  rw [positivePowerSumRat_eq_bernoulli]

/--
Under the standard shift assumption, the natural numerator sum,
cast to the rationals, equals its Bernoulli-expanded expression.
@isnad1 id=eq.1h4v.s4.f453d7b4f8fc from=translated src=- shape=1952d6df vocab=bb623465
-/
theorem shiftedPowerNumeratorSum_cast_rat_eq_bernoulli
    (q a b t : Nat)
    (ha : a < b) :
    (shiftedPowerNumeratorSum q a b t : Rat) =
      shiftedPowerNumeratorBernoulli q a b t := by
  have hInt :
      (shiftedPowerNumeratorSum q a b t : Int) =
        shiftedPowerNumeratorIntSum q a b t :=
    shiftedPowerNumeratorSum_cast_int q a b t ha
  calc
    (shiftedPowerNumeratorSum q a b t : Rat) =
        (shiftedPowerNumeratorIntSum q a b t : Rat) := by
      exact_mod_cast hInt
    _ = shiftedPowerNumeratorBernoulli q a b t :=
      shiftedPowerNumeratorIntSum_cast_rat_eq_bernoulli
        q a b t

/--
The Bernoulli-expanded expression for the quotient sum.-/
noncomputable def shiftedPowerQuotientBernoulli
    (q a b t : Nat) : Rat :=
  (shiftedPowerNumeratorBernoulli q a b t -
      (shiftedPowerResidueSum q a b t : Rat)) /
    (shiftedPowerDenominator q b : Rat)

/--
The quotient sum, cast to the rationals, equals its
Bernoulli expression minus the residue contribution.
@isnad1 id=eq.2h4v.s5.0a1c6653ce23 from=translated src=- shape=8465ba16 vocab=5c6652fa
-/
theorem shiftedPowerQuotientSum_cast_rat_eq_bernoulli
    (q a b t : Nat)
    (hb : 0 < b)
    (ha : a < b) :
    (shiftedPowerQuotientSum q a b t : Rat) =
      shiftedPowerQuotientBernoulli q a b t := by
  have hNat :=
    shiftedPowerDenominator_mul_quotientSum_add_residueSum
      q a b t
  have hRat :
      (shiftedPowerDenominator q b : Rat) *
          (shiftedPowerQuotientSum q a b t : Rat) +
        (shiftedPowerResidueSum q a b t : Rat) =
      (shiftedPowerNumeratorSum q a b t : Rat) := by
    exact_mod_cast hNat
  have hDnat :
      shiftedPowerDenominator q b ≠ 0 :=
    Nat.ne_of_gt
      (shiftedPowerDenominator_pos q b hb)
  have hD :
      (shiftedPowerDenominator q b : Rat) ≠ 0 := by
    exact_mod_cast hDnat
  have hBern :
      (shiftedPowerNumeratorSum q a b t : Rat) =
        shiftedPowerNumeratorBernoulli q a b t :=
    shiftedPowerNumeratorSum_cast_rat_eq_bernoulli
      q a b t ha
  unfold shiftedPowerQuotientBernoulli
  apply (eq_div_iff hD).2
  calc
    (shiftedPowerQuotientSum q a b t : Rat) *
          (shiftedPowerDenominator q b : Rat) =
        (shiftedPowerDenominator q b : Rat) *
          (shiftedPowerQuotientSum q a b t : Rat) := by
      ring
    _ =
        (shiftedPowerNumeratorSum q a b t : Rat) -
          (shiftedPowerResidueSum q a b t : Rat) := by
      linarith
    _ =
        shiftedPowerNumeratorBernoulli q a b t -
          (shiftedPowerResidueSum q a b t : Rat) := by
      rw [hBern]

/--
The sum of the actual power residues over one complete period.-/
def shiftedPowerResiduePeriodSum
    (q a b : Nat) : Nat :=
  Finset.sum
    (Finset.range (shiftedResiduePeriod q b))
    (fun r =>
      shiftedPowerResidue q a b (r + 1))

/--
Adding one complete period adds exactly one full-period
sum of the shifted power residues.
@isnad1 id=eq.2h4v.s5.02eb95e3ebf7 from=translated src=- shape=354c3027 vocab=c0ccdbfd
-/
theorem shiftedPowerResidueSum_period_add
    (q a b t : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedPowerResidueSum q a b
        (shiftedResiduePeriod q b + t) =
      shiftedPowerResiduePeriodSum q a b +
        shiftedPowerResidueSum q a b t := by
  unfold shiftedPowerResidueSum
  unfold shiftedPowerResiduePeriodSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (shiftedPowerResidue_add_period
      q a b r hq ha)

/--
The shifted power residue sum over `s` complete periods,
followed by an initial segment of length `r`.
@isnad1 id=eq.2h5v.s6.0960925e11cd from=translated src=- shape=88ff1eb7 vocab=96b22a73
-/
theorem shiftedPowerResidueSum_mul_period_add
    (q a b s r : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedPowerResidueSum q a b
        (s * shiftedResiduePeriod q b + r) =
      s * shiftedPowerResiduePeriodSum q a b +
        shiftedPowerResidueSum q a b r := by
  induction s with
  | zero =>
      simp
  | succ s ih =>
      calc
        shiftedPowerResidueSum q a b
            (Nat.succ s * shiftedResiduePeriod q b + r) =
          shiftedPowerResidueSum q a b
            (shiftedResiduePeriod q b +
              (s * shiftedResiduePeriod q b + r)) := by
            congr 1
            rw [Nat.succ_mul]
            ac_rfl
        _ =
          shiftedPowerResiduePeriodSum q a b +
            shiftedPowerResidueSum q a b
              (s * shiftedResiduePeriod q b + r) :=
          shiftedPowerResidueSum_period_add
            q a b
              (s * shiftedResiduePeriod q b + r)
              hq ha
        _ =
          shiftedPowerResiduePeriodSum q a b +
            (s * shiftedPowerResiduePeriodSum q a b +
              shiftedPowerResidueSum q a b r) := by
            rw [ih]
        _ =
          Nat.succ s *
              shiftedPowerResiduePeriodSum q a b +
            shiftedPowerResidueSum q a b r := by
            rw [Nat.succ_mul]
            ac_rfl

/--
The shifted power residue sum decomposes into complete periods
and a final incomplete period.
@isnad1 id=eq.2h4v.s6.e7f038b431c2 from=translated src=- shape=e72eef5c vocab=5fce0f51
-/
theorem shiftedPowerResidueSum_div_mod
    (q a b t : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedPowerResidueSum q a b t =
      (t / shiftedResiduePeriod q b) *
          shiftedPowerResiduePeriodSum q a b +
        shiftedPowerResidueSum q a b
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
    shiftedPowerResidueSum q a b t =
        shiftedPowerResidueSum q a b
          ((t / shiftedResiduePeriod q b) *
              shiftedResiduePeriod q b +
            t % shiftedResiduePeriod q b) := by
      rw [hdecomp]
    _ =
        (t / shiftedResiduePeriod q b) *
            shiftedPowerResiduePeriodSum q a b +
          shiftedPowerResidueSum q a b
            (t % shiftedResiduePeriod q b) :=
      shiftedPowerResidueSum_mul_period_add
        q a b
          (t / shiftedResiduePeriod q b)
          (t % shiftedResiduePeriod q b)
          hq ha

/--
The incomplete-period part of the shifted power residue sum.-/
def shiftedPowerResiduePeriodicRemainder
    (q a b t : Nat) : Nat :=
  shiftedPowerResidueSum q a b
    (t % shiftedResiduePeriod q b)

/--
The canonical complete-period-plus-remainder expression
-period-plus-remainder expression
for the shifted power residue sum.-/
def shiftedPowerResiduePeriodicForm
    (q a b t : Nat) : Nat :=
  (t / shiftedResiduePeriod q b) *
      shiftedPowerResiduePeriodSum q a b +
    shiftedPowerResiduePeriodicRemainder q a b t

/--
The actual residue sum equals its canonical periodic form.
@isnad1 id=eq.2h4v.s5.ea1da7bef89f from=translated src=- shape=f85cd440 vocab=4e10b754
-/
theorem shiftedPowerResidueSum_eq_periodicForm
    (q a b t : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedPowerResidueSum q a b t =
      shiftedPowerResiduePeriodicForm q a b t := by
  unfold shiftedPowerResiduePeriodicForm
  unfold shiftedPowerResiduePeriodicRemainder
  exact shiftedPowerResidueSum_div_mod
    q a b t hq ha

/--
The Bernoulli expression for the quotient sum with the residue
contribution written as complete periods plus a remainder.-/
noncomputable def shiftedPowerQuotientBernoulliPeriodic
    (q a b t : Nat) : Rat :=
  (shiftedPowerNumeratorBernoulli q a b t -
      (shiftedPowerResiduePeriodicForm q a b t : Rat)) /
    (shiftedPowerDenominator q b : Rat)

/--
The quotient sum equals its Bernoulli-periodic expression.
@isnad1 id=eq.3h4v.s5.81f28653a9cb from=translated src=- shape=11946fbf vocab=feaead9f
-/
theorem shiftedPowerQuotientSum_cast_rat_eq_periodicBernoulli
    (q a b t : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    (shiftedPowerQuotientSum q a b t : Rat) =
      shiftedPowerQuotientBernoulliPeriodic q a b t := by
  calc
    (shiftedPowerQuotientSum q a b t : Rat) =
        shiftedPowerQuotientBernoulli q a b t :=
      shiftedPowerQuotientSum_cast_rat_eq_bernoulli
        q a b t hb ha
    _ =
        shiftedPowerQuotientBernoulliPeriodic q a b t := by
      unfold shiftedPowerQuotientBernoulli
      unfold shiftedPowerQuotientBernoulliPeriodic
      rw [shiftedPowerResidueSum_eq_periodicForm
        q a b t hq ha]

end RoundedRootSums
