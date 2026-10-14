/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import Tengoku.Formalslt.FormalSLT.AnytimeValid.ComputablePredictableBettingMixture
import Tengoku.Formalslt.FormalSLT.AnytimeValid.CountableEProcess

/-!
# Exact countable sleeping-expert betting mixtures

This module extends the computable finite betting master to a countable
catalog without evaluating an infinite sum. Expert `j` sleeps through times
`k < j`, and the prior weight of expert `j` is `2⁻⁽ʲ⁺¹⁾`. At time `n`, all
experts `j ≥ n` still have wealth one, so their entire infinite tail has the
closed form `2⁻ⁿ`. The countable mixture wealth and its current master bet are
therefore finite computations.

The resulting master automatically competes with every expert once that
expert has entered the active prefix. This is a countable, growing, exact
strategy mixture. It is not a parameter-free continuum coin-betting theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

section Algebra

variable {R Omega : Type*}

/-- Expert `j` bets only from time `j` onward. -/
def sleepingStrategy [Zero R]
    (strategy : Nat -> Nat -> Omega -> R) (j k : Nat) (omega : Omega) : R :=
  if j <= k then strategy j k omega else 0

/--
@isnad1 id=eq.1h6v.s5.45b5b557ddb3 from=translated src=- shape=a2788fb5 vocab=711f6d4d
-/
@[simp]
theorem sleepingStrategy_of_le [Zero R]
    (strategy : Nat -> Nat -> Omega -> R) {j k : Nat} (hjk : j <= k)
    (omega : Omega) :
    sleepingStrategy strategy j k omega = strategy j k omega := by
  simp [sleepingStrategy, hjk]

/--
@isnad1 id=eq.1h6v.s5.1e5cde8ca4f7 from=translated src=- shape=2e45de92 vocab=69df05d4
-/
@[simp]
theorem sleepingStrategy_of_lt [Zero R]
    (strategy : Nat -> Nat -> Omega -> R) {j k : Nat} (hkj : k < j)
    (omega : Omega) :
    sleepingStrategy strategy j k omega = 0 := by
  simp [sleepingStrategy, not_le.mpr hkj]

/-- An expert that has not awakened has unit wealth.
@isnad1 id=eq.1h7v.s6.d9d3c0f8f853 from=translated src=- shape=cecc409d vocab=fbe8744a
-/
theorem algebraicBettingWealth_sleeping_of_time_le [CommSemiring R]
    (residual : Nat -> Omega -> R) (strategy : Nat -> Nat -> Omega -> R)
    {n j : Nat} (hnj : n <= j) (omega : Omega) :
    algebraicBettingWealth residual (sleepingStrategy strategy j) n omega = 1 := by
  unfold algebraicBettingWealth
  apply Finset.prod_eq_one
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hkj : k < j := lt_of_lt_of_le hkn hnj
  simp [sleepingStrategy, not_le.mpr hkj]

/-- Dyadic prior mass assigned to expert `j`. -/
def dyadicExpertWeight [Field R] (j : Nat) : R :=
  1 / (2 : R) ^ (j + 1)

/-- Closed-form mass of the sleeping tail `j ≥ n`. -/
def dyadicSleepingTail [Field R] (n : Nat) : R :=
  1 / (2 : R) ^ n

/-- Exact finite representation of the countable sleeping-expert mixture.
The first term is the closed-form wealth-one tail. -/
def countableSleepingMixtureWealth [Field R]
    (residual : Nat -> Omega -> R)
    (strategy : Nat -> Nat -> Omega -> R) (n : Nat) (omega : Omega) : R :=
  dyadicSleepingTail n +
    ∑ j ∈ Finset.range n,
      dyadicExpertWeight j *
        algebraicBettingWealth residual (sleepingStrategy strategy j) n omega

/-- Current wealth-weighted numerator. Only experts `j ≤ n` can bet at time
`n`, so the sum is finite. -/
def countableSleepingBetNumerator [Field R]
    (residual : Nat -> Omega -> R)
    (strategy : Nat -> Nat -> Omega -> R) (n : Nat) (omega : Omega) : R :=
  ∑ j ∈ Finset.range (n + 1),
    dyadicExpertWeight j *
      algebraicBettingWealth residual (sleepingStrategy strategy j) n omega *
        strategy j n omega

/-- Executable master bet for the countable sleeping-expert catalog. -/
def countableSleepingMasterBet [Field R]
    (residual : Nat -> Omega -> R)
    (strategy : Nat -> Nat -> Omega -> R) (n : Nat) (omega : Omega) : R :=
  countableSleepingBetNumerator residual strategy n omega /
    countableSleepingMixtureWealth residual strategy n omega

/--
@isnad1 id=eq.0h5v.s5.99810dc21f08 from=translated src=- shape=254e6538 vocab=eea08a71
-/
@[simp]
theorem countableSleepingMixtureWealth_zero [Field R]
    (residual : Nat -> Omega -> R)
    (strategy : Nat -> Nat -> Omega -> R) (omega : Omega) :
    countableSleepingMixtureWealth residual strategy 0 omega = 1 := by
  simp [countableSleepingMixtureWealth, dyadicSleepingTail]

/-- One dyadic atom plus the remaining tail equals the previous tail.
@isnad1 id=eq.0h2v.s5.c9074c53d509 from=translated src=- shape=ef95a24d vocab=1bcd5eb3
-/
theorem dyadicSleepingTail_succ_add_weight [Field R] [CharZero R]
    (n : Nat) :
    dyadicSleepingTail (R := R) (n + 1) +
        dyadicExpertWeight (R := R) n =
      dyadicSleepingTail (R := R) n := by
  simp only [dyadicSleepingTail, dyadicExpertWeight]
  rw [pow_succ]
  field_simp
  ring

/--
@isnad1 id=lt.0h2v.s6.add4b9efc040 from=translated src=- shape=70182548 vocab=f976ef82
-/
theorem dyadicExpertWeight_pos [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (j : Nat) :
    0 < dyadicExpertWeight (R := R) j := by
  unfold dyadicExpertWeight
  positivity

/--
@isnad1 id=lt.0h2v.s6.84c45e3b7b67 from=translated src=- shape=70182548 vocab=15ea9564
-/
theorem dyadicSleepingTail_pos [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (n : Nat) :
    0 < dyadicSleepingTail (R := R) n := by
  unfold dyadicSleepingTail
  positivity

/-- The exact countable mixture obeys the usual wealth recursion, with a
finite current numerator.
@isnad1 id=eq.0h6v.s6.949aae4db199 from=translated src=- shape=79a0db82 vocab=62a1ac3f
-/
theorem countableSleepingMixtureWealth_succ [Field R] [CharZero R]
    (residual : Nat -> Omega -> R)
    (strategy : Nat -> Nat -> Omega -> R) (n : Nat) (omega : Omega) :
    countableSleepingMixtureWealth residual strategy (n + 1) omega =
      countableSleepingMixtureWealth residual strategy n omega +
        residual n omega *
          countableSleepingBetNumerator residual strategy n omega := by
  unfold countableSleepingMixtureWealth countableSleepingBetNumerator
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hactive (j : Nat) (hj : j ∈ Finset.range n) :
      algebraicBettingWealth residual (sleepingStrategy strategy j)
          (n + 1) omega =
        algebraicBettingWealth residual (sleepingStrategy strategy j)
            n omega *
          (1 + strategy j n omega * residual n omega) := by
    rw [algebraicBettingWealth_succ]
    simp [sleepingStrategy, Nat.le_of_lt (Finset.mem_range.mp hj)]
  have hsum_succ :
      (∑ j ∈ Finset.range n,
          dyadicExpertWeight j *
            algebraicBettingWealth residual (sleepingStrategy strategy j)
              (n + 1) omega) =
        ∑ j ∈ Finset.range n,
          dyadicExpertWeight j *
            (algebraicBettingWealth residual (sleepingStrategy strategy j)
                n omega *
              (1 + strategy j n omega * residual n omega)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hactive j hj]
  have hsum_expand :
      (∑ j ∈ Finset.range n,
          dyadicExpertWeight j *
            (algebraicBettingWealth residual (sleepingStrategy strategy j)
                n omega *
              (1 + strategy j n omega * residual n omega))) =
        (∑ j ∈ Finset.range n,
          dyadicExpertWeight j *
            algebraicBettingWealth residual (sleepingStrategy strategy j)
              n omega) +
          residual n omega *
            ∑ j ∈ Finset.range n,
              dyadicExpertWeight j *
                algebraicBettingWealth residual
                  (sleepingStrategy strategy j) n omega *
                    strategy j n omega := by
    calc
      _ = ∑ j ∈ Finset.range n,
          (dyadicExpertWeight j *
              algebraicBettingWealth residual
                (sleepingStrategy strategy j) n omega +
            residual n omega *
              (dyadicExpertWeight j *
                algebraicBettingWealth residual
                  (sleepingStrategy strategy j) n omega *
                    strategy j n omega)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hnew_before :
      algebraicBettingWealth residual (sleepingStrategy strategy n)
          n omega = 1 :=
    algebraicBettingWealth_sleeping_of_time_le residual strategy le_rfl omega
  have hnew_after :
      algebraicBettingWealth residual (sleepingStrategy strategy n)
          (n + 1) omega =
        1 + strategy n n omega * residual n omega := by
    rw [algebraicBettingWealth_succ, hnew_before]
    simp [sleepingStrategy]
  rw [hsum_succ, hsum_expand, hnew_after, hnew_before]
  rw [← dyadicSleepingTail_succ_add_weight (R := R) n]
  ring

/-- The closed-form sleeping tail keeps the countable mixture strictly
positive whenever active expert wealth is nonnegative.
@isnad1 id=lt.1h6v.s7.32eca785a954 from=translated src=- shape=405edab0 vocab=950e281a
-/
theorem countableSleepingMixtureWealth_pos [Field R] [LinearOrder R]
    [IsStrictOrderedRing R]
    {residual : Nat -> Omega -> R}
    {strategy : Nat -> Nat -> Omega -> R}
    (hwealth_nonneg : forall j n omega,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega)
    (n : Nat) (omega : Omega) :
    0 < countableSleepingMixtureWealth residual strategy n omega := by
  unfold countableSleepingMixtureWealth
  exact add_pos_of_pos_of_nonneg (dyadicSleepingTail_pos n)
    (Finset.sum_nonneg fun j _hj =>
      mul_nonneg (dyadicExpertWeight_pos j).le
        (hwealth_nonneg j n omega))

/-- Once expert `j` is in the active prefix, the exact finite-tail mixture
dominates its prior-weighted wealth.
@isnad1 id=le.2h7v.s7.3646ed62897b from=translated src=- shape=dd4e1410 vocab=bfdfc208
-/
theorem countableSleepingMixtureWealth_competes_of_lt
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {residual : Nat -> Omega -> R}
    {strategy : Nat -> Nat -> Omega -> R}
    (hwealth_nonneg : forall j n omega,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega)
    {j n : Nat} (hjn : j < n) (omega : Omega) :
    dyadicExpertWeight j *
        algebraicBettingWealth residual
          (sleepingStrategy strategy j) n omega <=
      countableSleepingMixtureWealth residual strategy n omega := by
  have hsingle :
      dyadicExpertWeight j *
          algebraicBettingWealth residual
            (sleepingStrategy strategy j) n omega <=
        ∑ i ∈ Finset.range n,
          dyadicExpertWeight i *
            algebraicBettingWealth residual
              (sleepingStrategy strategy i) n omega := by
    exact Finset.single_le_sum
      (fun i _hi => mul_nonneg (dyadicExpertWeight_pos i).le
        (hwealth_nonneg i n omega))
      (Finset.mem_range.mpr hjn)
  unfold countableSleepingMixtureWealth
  exact hsingle.trans (le_add_of_nonneg_left (dyadicSleepingTail_pos n).le)

/-- The total prior-weighted wealth of experts that can bet at time `n` is
bounded by the exact mixture denominator. The unused mass is precisely the
still-sleeping dyadic tail.
@isnad1 id=le.0h6v.s7.edce0b7ef813 from=translated src=- shape=01093b62 vocab=0caadfbc
-/
theorem countableSleepingActiveMass_le_mixture
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (residual : Nat -> Omega -> R)
    (strategy : Nat -> Nat -> Omega -> R) (n : Nat) (omega : Omega) :
    (∑ j ∈ Finset.range (n + 1),
        dyadicExpertWeight j *
          algebraicBettingWealth residual
            (sleepingStrategy strategy j) n omega) <=
      countableSleepingMixtureWealth residual strategy n omega := by
  rw [Finset.sum_range_succ,
    algebraicBettingWealth_sleeping_of_time_le residual strategy le_rfl omega,
    mul_one]
  unfold countableSleepingMixtureWealth
  rw [← dyadicSleepingTail_succ_add_weight (R := R) n]
  have htail : 0 <= dyadicSleepingTail (R := R) (n + 1) :=
    (dyadicSleepingTail_pos (n + 1)).le
  linarith

/-- Nonnegative legal expert bets yield a legal countable-master bet in the
same interval.
@isnad1 id=mem.3h7v.s7.10c65df5d84a from=translated src=- shape=61c201b0 vocab=3e56a0c9
-/
theorem countableSleepingMasterBet_mem_Icc
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {residual : Nat -> Omega -> R}
    {strategy : Nat -> Nat -> Omega -> R} {limit : R}
    (hlimit_nonneg : 0 <= limit)
    (hwealth_nonneg : forall j n omega,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega)
    (hstrategy : forall j n omega,
      strategy j n omega ∈ Set.Icc (0 : R) limit)
    (n : Nat) (omega : Omega) :
    countableSleepingMasterBet residual strategy n omega ∈
      Set.Icc (0 : R) limit := by
  let coefficient : Nat -> R := fun j =>
    dyadicExpertWeight j *
      algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega
  have hcoefficient : forall j, 0 <= coefficient j := fun j =>
    mul_nonneg (dyadicExpertWeight_pos j).le
      (hwealth_nonneg j n omega)
  have hnum_nonneg : 0 <=
      ∑ j ∈ Finset.range (n + 1),
        coefficient j * strategy j n omega :=
    Finset.sum_nonneg fun j _hj =>
      mul_nonneg (hcoefficient j) (hstrategy j n omega).1
  have hnum_le_active :
      (∑ j ∈ Finset.range (n + 1),
          coefficient j * strategy j n omega) <=
        limit *
          ∑ j ∈ Finset.range (n + 1), coefficient j := by
    calc
      _ <= ∑ j ∈ Finset.range (n + 1), coefficient j * limit := by
        exact Finset.sum_le_sum fun j _hj =>
          mul_le_mul_of_nonneg_left
            (hstrategy j n omega).2 (hcoefficient j)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have hactive_le :
      (∑ j ∈ Finset.range (n + 1), coefficient j) <=
        countableSleepingMixtureWealth residual strategy n omega := by
    exact countableSleepingActiveMass_le_mixture
      residual strategy n omega
  have hnum_le :
      (∑ j ∈ Finset.range (n + 1),
          coefficient j * strategy j n omega) <=
        limit * countableSleepingMixtureWealth
          residual strategy n omega :=
    hnum_le_active.trans
      (mul_le_mul_of_nonneg_left hactive_le hlimit_nonneg)
  have hmix_pos := countableSleepingMixtureWealth_pos
    hwealth_nonneg n omega
  unfold countableSleepingMasterBet countableSleepingBetNumerator
  change
    (∑ j ∈ Finset.range (n + 1),
        coefficient j * strategy j n omega) /
        countableSleepingMixtureWealth residual strategy n omega ∈
      Set.Icc (0 : R) limit
  exact ⟨div_nonneg hnum_nonneg hmix_pos.le,
    (div_le_iff₀ hmix_pos).2 hnum_le⟩

/-- The recursively generated master wealth is exactly the finite-tail
representation of the countable sleeping-expert mixture.
@isnad1 id=eq.1h6v.s6.5be30cb1cf47 from=translated src=- shape=00e4c578 vocab=c3824f8b
-/
theorem countableSleepingMasterWealth_eq_mixture [Field R] [CharZero R]
    (residual : Nat -> Omega -> R)
    (strategy : Nat -> Nat -> Omega -> R)
    (hmix_ne : forall n omega,
      countableSleepingMixtureWealth residual strategy n omega ≠ 0) :
    forall n omega,
      algebraicBettingWealth residual
          (countableSleepingMasterBet residual strategy) n omega =
        countableSleepingMixtureWealth residual strategy n omega := by
  intro n
  induction n with
  | zero =>
      intro omega
      simp
  | succ n ih =>
      intro omega
      rw [algebraicBettingWealth_succ, ih omega,
        countableSleepingMixtureWealth_succ]
      unfold countableSleepingMasterBet
      field_simp [hmix_ne n omega]

/-- The executable countable master competes with every expert after that
expert enters the growing active prefix.
@isnad1 id=le.2h7v.s7.c9a5a24fda07 from=translated src=- shape=1e053c47 vocab=66761332
-/
theorem countableSleepingMasterWealth_competes_of_lt
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {residual : Nat -> Omega -> R}
    {strategy : Nat -> Nat -> Omega -> R}
    (hwealth_nonneg : forall j n omega,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega)
    {j n : Nat} (hjn : j < n) (omega : Omega) :
    dyadicExpertWeight j *
        algebraicBettingWealth residual
          (sleepingStrategy strategy j) n omega <=
      algebraicBettingWealth residual
        (countableSleepingMasterBet residual strategy) n omega := by
  rw [countableSleepingMasterWealth_eq_mixture residual strategy
    (fun n omega =>
      (countableSleepingMixtureWealth_pos hwealth_nonneg n omega).ne')
    n omega]
  exact countableSleepingMixtureWealth_competes_of_lt
    hwealth_nonneg hjn omega

end Algebra

section InfiniteMixtureIdentity

variable {Omega : Type*}

/--
@isnad1 id=hassum.0h0v.s4.a791d4180629 from=translated src=- shape=bef2ba81 vocab=abcd2207
-/
theorem hasSum_dyadicExpertWeight :
    HasSum (fun j : Nat => dyadicExpertWeight (R := Real) j) 1 := by
  have heq :
      (fun j : Nat => dyadicExpertWeight (R := Real) j) =
        fun j : Nat => (1 : Real) / 2 / 2 ^ j := by
    funext j
    unfold dyadicExpertWeight
    rw [pow_succ]
    ring
  rw [heq]
  exact hasSum_geometric_two' 1

/-- The executable finite-prefix-plus-tail formula is exactly the mathematical
infinite dyadic mixture of all sleeping-expert wealths. The infinite sum
appears only in this specification theorem, not in the executable definition.
@isnad1 id=eq.0h5v.s6.46edf0cc22e4 from=translated src=- shape=d4ab20b3 vocab=abfe4fb2
-/
theorem countableSleepingMixtureWealth_eq_tsum
    (residual : Nat -> Omega -> Real)
    (strategy : Nat -> Nat -> Omega -> Real) (n : Nat) (omega : Omega) :
    countableSleepingMixtureWealth residual strategy n omega =
      ∑' j : Nat,
        dyadicExpertWeight j *
          algebraicBettingWealth residual
            (sleepingStrategy strategy j) n omega := by
  let f : Nat -> Real := fun j =>
    dyadicExpertWeight j *
      algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega
  have hweight_summable : Summable
      (fun j : Nat => dyadicExpertWeight (R := Real) j) := by
    have hgeom := summable_geometric_two' (1 : Real)
    apply hgeom.congr
    intro j
    unfold dyadicExpertWeight
    rw [pow_succ]
    ring
  have htail_eq (i : Nat) :
      f (i + n) = dyadicExpertWeight (R := Real) (i + n) := by
    unfold f
    rw [algebraicBettingWealth_sleeping_of_time_le residual strategy
      (Nat.le_add_left n i) omega, mul_one]
  have hshift_summable : Summable (fun i => f (i + n)) := by
    exact ((summable_nat_add_iff n).2 hweight_summable).congr
      (fun i => (htail_eq i).symm)
  have hf : Summable f := (summable_nat_add_iff n).1 hshift_summable
  have hweight_shift (i : Nat) :
      dyadicExpertWeight (R := Real) (i + n) =
        dyadicSleepingTail (R := Real) n / 2 / 2 ^ i := by
    unfold dyadicExpertWeight dyadicSleepingTail
    rw [pow_add, pow_succ]
    field_simp
    ring
  have htail_tsum :
      (∑' i : Nat, f (i + n)) = dyadicSleepingTail n := by
    calc
      (∑' i : Nat, f (i + n)) =
          ∑' i : Nat, dyadicExpertWeight (R := Real) (i + n) := by
            apply tsum_congr
            exact htail_eq
      _ = ∑' i : Nat, dyadicSleepingTail (R := Real) n / 2 / 2 ^ i := by
            apply tsum_congr
            exact hweight_shift
      _ = dyadicSleepingTail n := tsum_geometric_two' _
  unfold countableSleepingMixtureWealth
  change dyadicSleepingTail n + (∑ j ∈ Finset.range n, f j) = ∑' j, f j
  rw [add_comm, ← htail_tsum]
  exact hf.sum_add_tsum_nat_add n

end InfiniteMixtureIdentity

section RationalBridge

variable {Omega : Type*}

/--
@isnad1 id=eq.0h5v.s5.0b08c2585307 from=translated src=- shape=8fbf481f vocab=a2b9a8ff
-/
@[simp]
theorem ratCast_sleepingStrategy
    (strategy : Nat -> Nat -> Omega -> Rat) (j k : Nat) (omega : Omega) :
    ((sleepingStrategy strategy j k omega : Rat) : Real) =
      sleepingStrategy
        (fun j k omega => (strategy j k omega : Real)) j k omega := by
  by_cases hjk : j <= k <;> simp [sleepingStrategy, hjk]

/--
@isnad1 id=eq.0h5v.s6.4ee51f5a8821 from=translated src=- shape=5e6afe21 vocab=dc26673e
-/
theorem ratCast_countableSleepingMixtureWealth
    (residual : Nat -> Omega -> Rat)
    (strategy : Nat -> Nat -> Omega -> Rat) (n : Nat) (omega : Omega) :
    ((countableSleepingMixtureWealth residual strategy n omega : Rat) : Real) =
      countableSleepingMixtureWealth
        (fun k omega => (residual k omega : Real))
        (fun j k omega => (strategy j k omega : Real)) n omega := by
  simp [countableSleepingMixtureWealth, dyadicSleepingTail,
    dyadicExpertWeight, ratCast_algebraicBettingWealth,
    ratCast_sleepingStrategy]

/--
@isnad1 id=eq.0h5v.s6.61be4a53b5da from=translated src=- shape=5e6afe21 vocab=6b4ba8f4
-/
theorem ratCast_countableSleepingBetNumerator
    (residual : Nat -> Omega -> Rat)
    (strategy : Nat -> Nat -> Omega -> Rat) (n : Nat) (omega : Omega) :
    ((countableSleepingBetNumerator residual strategy n omega : Rat) : Real) =
      countableSleepingBetNumerator
        (fun k omega => (residual k omega : Real))
        (fun j k omega => (strategy j k omega : Real)) n omega := by
  simp [countableSleepingBetNumerator, dyadicExpertWeight,
    ratCast_algebraicBettingWealth, ratCast_sleepingStrategy]

/--
@isnad1 id=eq.0h5v.s6.cd9468e00ca5 from=translated src=- shape=5e6afe21 vocab=b57254ad
-/
theorem ratCast_countableSleepingMasterBet
    (residual : Nat -> Omega -> Rat)
    (strategy : Nat -> Nat -> Omega -> Rat) (n : Nat) (omega : Omega) :
    ((countableSleepingMasterBet residual strategy n omega : Rat) : Real) =
      countableSleepingMasterBet
        (fun k omega => (residual k omega : Real))
        (fun j k omega => (strategy j k omega : Real)) n omega := by
  simp [countableSleepingMasterBet,
    ratCast_countableSleepingMixtureWealth,
    ratCast_countableSleepingBetNumerator]

end RationalBridge

section RealBridge

variable {Omega : Type*}

/-- The countable sleeping-expert master is predictable. Its time-`n`
calculation uses only finite sums of expert wealth through time `n` and the
experts' time-`n` predictable bets.
@isnad1 id=strongly.2h6v.s6.54b9c7e92d7a from=translated src=- shape=80fa0090 vocab=67bd9b97
-/
theorem countableSleepingMasterBet_stronglyAdapted
    {mOmega : MeasurableSpace Omega} {F : MeasureTheory.Filtration Nat mOmega}
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (hX_adapted : IncrementAdapted F X)
    (hstrategy_adapted : forall j,
      MeasureTheory.StronglyAdapted F (strategy j)) :
    StronglyAdapted F
      (countableSleepingMasterBet (fun k omega => X k omega - m) strategy) := by
  intro n
  have hsleep (j : Nat) : StronglyAdapted F
      (sleepingStrategy strategy j) := by
    intro k
    unfold sleepingStrategy
    split_ifs with hjk
    · exact hstrategy_adapted j k
    · exact stronglyMeasurable_const
  have hwealth (j : Nat) : StronglyMeasurable[F n]
      (fun omega => algebraicBettingWealth
        (fun k omega => X k omega - m)
        (sleepingStrategy strategy j) n omega) := by
    simpa only [algebraicBettingWealth_eq_bettingWealthProcess] using
      (stronglyAdapted_bettingWealthProcess_of_adapted
        hX_adapted (hsleep j) n)
  have hnumerator : StronglyMeasurable[F n]
      (fun omega => countableSleepingBetNumerator
        (fun k omega => X k omega - m) strategy n omega) := by
    unfold countableSleepingBetNumerator
    have hsum : StronglyMeasurable[F n]
        (∑ j ∈ Finset.range (n + 1), fun omega =>
          dyadicExpertWeight j *
              algebraicBettingWealth (fun k omega => X k omega - m)
                (sleepingStrategy strategy j) n omega *
            strategy j n omega) :=
      Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun j _hj =>
        (((hwealth j).const_mul (dyadicExpertWeight j)).mul
          (hstrategy_adapted j n))
    convert hsum using 1
    funext omega
    simp only [Finset.sum_apply]
  have hdenominator : StronglyMeasurable[F n]
      (fun omega => countableSleepingMixtureWealth
        (fun k omega => X k omega - m) strategy n omega) := by
    unfold countableSleepingMixtureWealth
    have hsum : StronglyMeasurable[F n]
        (∑ j ∈ Finset.range n, fun omega =>
          dyadicExpertWeight j *
            algebraicBettingWealth (fun k omega => X k omega - m)
              (sleepingStrategy strategy j) n omega) :=
      Finset.stronglyMeasurable_sum (Finset.range n) fun j _hj =>
        (hwealth j).const_mul (dyadicExpertWeight j)
    have hadd : StronglyMeasurable[F n]
        ((fun _ : Omega => dyadicSleepingTail n) +
          ∑ j ∈ Finset.range n, fun omega =>
            dyadicExpertWeight j *
              algebraicBettingWealth (fun k omega => X k omega - m)
                (sleepingStrategy strategy j) n omega) :=
      stronglyMeasurable_const.add hsum
    convert hadd using 1
    funext omega
    simp only [Pi.add_apply, Finset.sum_apply]
  change StronglyMeasurable[F n]
    (fun omega => countableSleepingBetNumerator
      (fun k omega => X k omega - m) strategy n omega /
        countableSleepingMixtureWealth
          (fun k omega => X k omega - m) strategy n omega)
  exact hnumerator.div hdenominator

/-- Fixed-time integrability of the mathematical countable mixture reduces to
a finite active prefix plus its constant dyadic sleeping tail.
@isnad1 id=integrab.1h8v.s6.0f837b4a4172 from=translated src=- shape=549112c5 vocab=9ac5db61
-/
theorem countableSleepingWeightedProcess_integrable
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsFiniteMeasure mu]
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (hcomponent : forall j,
      EProcess mu F
        (bettingWealthProcess X (sleepingStrategy strategy j) m))
    (n : Nat) :
    Integrable
      (countableWeightedProcess
        (fun j => dyadicExpertWeight j)
        (fun j => bettingWealthProcess X
          (sleepingStrategy strategy j) m) n) mu := by
  have heq :
      countableWeightedProcess
          (fun j => dyadicExpertWeight j)
          (fun j => bettingWealthProcess X
            (sleepingStrategy strategy j) m) n =
        fun omega => countableSleepingMixtureWealth
          (fun k omega => X k omega - m) strategy n omega := by
    funext omega
    unfold countableWeightedProcess
    rw [countableSleepingMixtureWealth_eq_tsum]
    apply tsum_congr
    intro j
    rw [algebraicBettingWealth_eq_bettingWealthProcess]
  rw [heq]
  unfold countableSleepingMixtureWealth
  have hsum : Integrable
      (∑ j ∈ Finset.range n, fun omega =>
        dyadicExpertWeight j *
          algebraicBettingWealth (fun k omega => X k omega - m)
            (sleepingStrategy strategy j) n omega) mu := by
    exact integrable_finsetSum' (Finset.range n) fun j _hj => by
      have hj : Integrable
          (bettingWealthProcess X (sleepingStrategy strategy j) m n) mu :=
        (hcomponent j).supermartingale.integrable n
      simpa only [algebraicBettingWealth_eq_bettingWealthProcess] using
        hj.const_mul (dyadicExpertWeight j)
  have hadd : Integrable
      ((fun _ : Omega => dyadicSleepingTail n) +
        ∑ j ∈ Finset.range n, fun omega =>
          dyadicExpertWeight j *
            algebraicBettingWealth (fun k omega => X k omega - m)
              (sleepingStrategy strategy j) n omega) mu :=
    (integrable_const _).add hsum
  convert hadd using 1
  funext omega
  simp only [Pi.add_apply, Finset.sum_apply]

/-- The set-integral norm series required for countable e-process closure is
summable automatically: after the finite active prefix, every expert still has
unit wealth and only the dyadic prior tail remains.
@isnad1 id=summable.1h8v.s6.5ff1b7126cf1 from=translated src=- shape=4833e3b8 vocab=07cf7273
-/
theorem countableSleepingWeightedProcess_integralNorm_summable
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu]
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (n : Nat) (s : Set Omega) (_hs : MeasurableSet s) :
    Summable fun j =>
      ∫ omega in s,
        ‖dyadicExpertWeight j *
          bettingWealthProcess X
            (sleepingStrategy strategy j) m n omega‖ ∂mu := by
  let g : Nat -> Real := fun j =>
    ∫ omega in s,
      ‖dyadicExpertWeight j *
        bettingWealthProcess X
          (sleepingStrategy strategy j) m n omega‖ ∂mu
  have hsleep (i : Nat) (omega : Omega) :
      bettingWealthProcess X
          (sleepingStrategy strategy (i + n)) m n omega = 1 := by
    rw [← algebraicBettingWealth_eq_bettingWealthProcess]
    exact algebraicBettingWealth_sleeping_of_time_le
      (fun k omega => X k omega - m) strategy
        (Nat.le_add_left n i) omega
  have htail_eq (i : Nat) :
      g (i + n) =
        dyadicExpertWeight (R := Real) (i + n) * mu.real s := by
    unfold g
    simp_rw [hsleep i]
    rw [mul_one, Real.norm_eq_abs,
      abs_of_pos (dyadicExpertWeight_pos (R := Real) (i + n))]
    simp [mul_comm]
  have hweight_shift : Summable
      (fun i => dyadicExpertWeight (R := Real) (i + n)) :=
    (summable_nat_add_iff n).2 hasSum_dyadicExpertWeight.summable
  have hshift : Summable (fun i => g (i + n)) := by
    exact (hweight_shift.mul_right (mu.real s)).congr
      (fun i => (htail_eq i).symm)
  exact (summable_nat_add_iff n).1 hshift

/-- Analytic e-process bridge for the executable countable master. The finite
active prefix and geometric sleeping tail automatically discharge the
integrability and sum/interchange obligations of countable-mixture closure.
@isnad1 id=eprocess.3h7v.s6.79294319aa82 from=translated src=- shape=18f21f06 vocab=f98e3a8f
-/
theorem countableSleepingMasterBet_eProcess
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {F : Filtration Nat mOmega} [IsFiniteMeasure mu]
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Nat -> Nat -> Omega -> Real)
    (hX_adapted : IncrementAdapted F X)
    (hstrategy_adapted : forall j, StronglyAdapted F (strategy j))
    (hcomponent : forall j,
      EProcess mu F
        (bettingWealthProcess X (sleepingStrategy strategy j) m)) :
    EProcess mu F
      (bettingWealthProcess X
        (countableSleepingMasterBet
          (fun k omega => X k omega - m) strategy) m) := by
  have hwealth_nonneg : forall j n omega,
      0 <= algebraicBettingWealth (fun k omega => X k omega - m)
        (sleepingStrategy strategy j) n omega := by
    intro j n omega
    simpa only [algebraicBettingWealth_eq_bettingWealthProcess,
      Pi.zero_apply] using
      (hcomponent j).nonneg n omega
  have heq :
      bettingWealthProcess X
          (countableSleepingMasterBet
            (fun k omega => X k omega - m) strategy) m =
        countableWeightedProcess
          (fun j => dyadicExpertWeight j)
          (fun j => bettingWealthProcess X
            (sleepingStrategy strategy j) m) := by
    funext n omega
    rw [← algebraicBettingWealth_eq_bettingWealthProcess]
    rw [countableSleepingMasterWealth_eq_mixture
      (fun k omega => X k omega - m) strategy
        (fun n omega =>
          (countableSleepingMixtureWealth_pos
            hwealth_nonneg n omega).ne') n omega]
    rw [countableSleepingMixtureWealth_eq_tsum]
    rfl
  have hadapted : StronglyAdapted F
      (countableWeightedProcess
        (fun j => dyadicExpertWeight j)
        (fun j => bettingWealthProcess X
          (sleepingStrategy strategy j) m)) := by
    rw [← heq]
    exact stronglyAdapted_bettingWealthProcess_of_adapted hX_adapted
      (countableSleepingMasterBet_stronglyAdapted
        X m strategy hX_adapted hstrategy_adapted)
  have hE : EProcess mu F
      (countableWeightedProcess
        (fun j => dyadicExpertWeight j)
        (fun j => bettingWealthProcess X
          (sleepingStrategy strategy j) m)) := by
    apply countableWeightedProcess_eProcess
      (fun j => (dyadicExpertWeight_pos j).le)
      hasSum_dyadicExpertWeight hcomponent hadapted
      (countableSleepingWeightedProcess_integrable
        X m strategy hcomponent)
      (countableSleepingWeightedProcess_integralNorm_summable
        X m strategy)
  rw [heq]
  exact hE

/-- Log-wealth regret against any expert already in the active prefix is at
most the negative log of that expert's dyadic prior weight.
@isnad1 id=le.3h6v.s6.ae2e5ca12a5f from=translated src=- shape=656a92db vocab=fee0deb6
-/
theorem countableSleepingMaster_logWealth_regret_le
    {residual : Nat -> Omega -> Real}
    {strategy : Nat -> Nat -> Omega -> Real}
    (hwealth_nonneg : forall j n omega,
      0 <= algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega)
    {j n : Nat} (hjn : j < n) {omega : Omega}
    (hexpert_pos :
      0 < algebraicBettingWealth residual
        (sleepingStrategy strategy j) n omega) :
    Real.log
          (algebraicBettingWealth residual
            (sleepingStrategy strategy j) n omega) -
        Real.log
          (algebraicBettingWealth residual
            (countableSleepingMasterBet residual strategy) n omega) <=
      -Real.log (dyadicExpertWeight j) := by
  have hcomp := countableSleepingMasterWealth_competes_of_lt
    hwealth_nonneg hjn omega
  have hweight_pos : 0 < dyadicExpertWeight (R := Real) j :=
    dyadicExpertWeight_pos j
  have hlog := Real.log_le_log (mul_pos hweight_pos hexpert_pos) hcomp
  rw [Real.log_mul hweight_pos.ne' hexpert_pos.ne'] at hlog
  linarith

end RealBridge

end FormalSLT.AnytimeValid
