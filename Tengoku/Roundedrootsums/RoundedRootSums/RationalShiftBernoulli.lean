/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bernoulli-periodic formula for rationally shifted root sums

This file combines the exact inversion theorem, the Bernoulli
expansion of the quotient sum, and the periodic residue corrections.
-/

namespace RoundedRootSums

/--
The complete-period-plus-remainder expression for the
ceiling residue corrections.-/
def shiftedResidueCorrectionPeriodicForm
    (q a b t : Nat) : Nat :=
  (t / shiftedResiduePeriod q b) *
      shiftedResidueCorrectionPeriodSum q a b +
    shiftedResiduePeriodicRemainder q a b t

/--
The residue-correction sum equals its canonical periodic form.-/
theorem shiftedResidueCorrectionSum_eq_periodicForm
    (q a b t : Nat)
    (hq : 0 < q)
    (ha : a < b) :
    shiftedResidueCorrectionSum q a b t =
      shiftedResidueCorrectionPeriodicForm q a b t := by
  unfold shiftedResidueCorrectionPeriodicForm
  unfold shiftedResiduePeriodicRemainder
  exact shiftedResidueCorrectionSum_div_mod
    q a b t hq ha

/--
The complete Bernoulli-periodic expression for the rationally
shifted real q-th root sum.-/
noncomputable def shiftedRealRoundedSumBernoulliPeriodic
    (q a b n : Nat) : Rat :=
  (shiftedRealRoundedValue q a b n : Rat) *
      ((n + 1 : Nat) : Rat) -
    (shiftedPowerQuotientBernoulliPeriodic q a b
        (shiftedRealRoundedValue q a b n) +
      (shiftedResidueCorrectionPeriodicForm q a b
          (shiftedRealRoundedValue q a b n) : Rat))

/--
The rationally shifted real q-th root sum equals its complete
Bernoulli-periodic expression.-/
theorem shiftedRealRoundedSum_cast_rat_eq_periodicBernoulli
    (q a b n : Nat)
    (hq : 0 < q)
    (hb : 0 < b)
    (ha : a < b) :
    (shiftedRealRoundedSum q a b n : Rat) =
      shiftedRealRoundedSumBernoulliPeriodic q a b n := by
  let t := shiftedRealRoundedValue q a b n
  have hcut :
      IsShiftedCutoff q a b n
        (shiftedMaxLevel q a b n) :=
    shiftedMaxLevel_isCutoff q a b n hb ha
  have hadd :=
    shiftedInversionSum_add_thresholdSum_of_cutoff
      q a b n (shiftedMaxLevel q a b n)
      hb ha hcut
  have hthresholdMax :
      shiftedThresholdSum q a b
          (shiftedMaxLevel q a b n) ≤
        shiftedMaxLevel q a b n * (n + 1) := by
    omega
  have hthreshold :
      shiftedThresholdSum q a b t ≤
        t * (n + 1) := by
    simpa [t,
      shiftedMaxLevel_eq_realRoundedValue
        q a b n hq hb ha] using hthresholdMax
  have hsplit :=
    shiftedThresholdSum_eq_quotientSum_add_correctionSum
      q a b t hb ha
  have hparts :
      shiftedPowerQuotientSum q a b t +
          shiftedResidueCorrectionSum q a b t ≤
        t * (n + 1) := by
    rw [← hsplit]
    exact hthreshold
  have hNat :
      shiftedRealRoundedSum q a b n =
        t * (n + 1) -
          (shiftedPowerQuotientSum q a b t +
            shiftedResidueCorrectionSum q a b t) := by
    simpa [t] using
      (shiftedRealRoundedSum_residue_formula
        q a b n hq hb ha)
  have hRat :
      (shiftedRealRoundedSum q a b n : Rat) =
        (t : Rat) * ((n + 1 : Nat) : Rat) -
          ((shiftedPowerQuotientSum q a b t : Rat) +
            (shiftedResidueCorrectionSum q a b t : Rat)) := by
    have hCast :=
      congrArg (fun x : Nat => (x : Rat)) hNat
    rw [Nat.cast_sub hparts] at hCast
    simpa only [
      Nat.cast_mul,
      Nat.cast_add,
      Nat.cast_one
    ] using hCast
  unfold shiftedRealRoundedSumBernoulliPeriodic
  calc
    (shiftedRealRoundedSum q a b n : Rat) =
        (t : Rat) * ((n + 1 : Nat) : Rat) -
          ((shiftedPowerQuotientSum q a b t : Rat) +
            (shiftedResidueCorrectionSum q a b t : Rat)) :=
      hRat
    _ =
        (t : Rat) * ((n + 1 : Nat) : Rat) -
          (shiftedPowerQuotientBernoulliPeriodic q a b t +
            (shiftedResidueCorrectionPeriodicForm
              q a b t : Rat)) := by
      rw [shiftedPowerQuotientSum_cast_rat_eq_periodicBernoulli
        q a b t hq hb ha]
      rw [shiftedResidueCorrectionSum_eq_periodicForm
        q a b t hq ha]
    _ =
        (shiftedRealRoundedValue q a b n : Rat) *
            ((n + 1 : Nat) : Rat) -
          (shiftedPowerQuotientBernoulliPeriodic q a b
              (shiftedRealRoundedValue q a b n) +
            (shiftedResidueCorrectionPeriodicForm q a b
              (shiftedRealRoundedValue q a b n) : Rat)) := by
      rfl

end RoundedRootSums
