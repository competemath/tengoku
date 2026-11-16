/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftNearestMean
import Tengoku.Seed.Data.Nat.Periodic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Periodic antiderivatives for nearest q-th root corrections

This file introduces the centered nearest-root correction sequence

`ω_q(r) - μ_q`

and begins the construction of its exact periodic antiderivative.
-/

namespace RoundedRootSums

/--
The nearest-root correction sequence centered by its mean
over the exact least positive period.-/
def nearestQCenteredOmegaAt
    (q r : Nat) : Rat :=
  nearestQOmegaAt q r -
    nearestQOmegaExactPeriodMean q

/--
For every positive `q`, the centered correction sequence has
period `nearestQExactPeriod q`.
@isnad1 id=periodic.1h1v.s4.a9e45593da58 from=translated src=- shape=26fcee47 vocab=afb61fa7
-/
theorem nearestQCenteredOmegaAt_periodic
    (q : Nat)
    (hq : 0 < q) :
    Function.Periodic
      (nearestQCenteredOmegaAt q)
      (nearestQExactPeriod q) := by
  have hperiod :
      Function.Periodic
        (nearestQOmegaAt q)
        (nearestQExactPeriod q) :=
    (nearestQOmegaAt_isLeastPeriod
      q hq).2.1
  intro r
  unfold nearestQCenteredOmegaAt
  rw [hperiod r]

/--
For every positive `q`, the sum of the centered correction
sequence over one exact period is zero.
@isnad1 id=eq.1h1v.s4.84c2a2cb8753 from=translated src=- shape=360b44f8 vocab=0c40578b
-/
theorem nearestQCenteredOmegaAt_exactPeriod_sum_zero
    (q : Nat)
    (hq : 0 < q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun r =>
          nearestQCenteredOmegaAt q r) =
      0 := by
  have hperiodNe :
      (nearestQExactPeriod q : Rat) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        (nearestQExactPeriod_pos q hq))
  unfold nearestQCenteredOmegaAt
  rw [Finset.sum_sub_distrib]
  simp only [
    Finset.sum_const,
    Finset.card_range,
    nsmul_eq_mul
  ]
  unfold nearestQOmegaExactPeriodMean
  field_simp [hperiodNe]
  ring

/--
The periodic antiderivative of the centered nearest-root
correction sequence.

Its value at `t` is the centered prefix sum up to the
remainder of `t` modulo the exact period.-/
def nearestQOmegaTildeAt
    (q t : Nat) : Rat :=
  Finset.sum
    (Finset.range
      (t % nearestQExactPeriod q))
    (fun r =>
      nearestQCenteredOmegaAt q r)

/--
The periodic antiderivative is normalized to vanish at zero.
@isnad1 id=eq.0h1v.s4.4ee963a9a8eb from=translated src=- shape=8fc7241c vocab=fc9d762b
-/
@[simp]
theorem nearestQOmegaTildeAt_zero
    (q : Nat) :
    nearestQOmegaTildeAt q 0 = 0 := by
  simp [nearestQOmegaTildeAt]

/--
The centered prefix-sum construction is periodic with
period `nearestQExactPeriod q`.
@isnad1 id=periodic.0h1v.s3.edfbcb8c74c6 from=translated src=- shape=5c4c3a1a vocab=9bd677af
-/
theorem nearestQOmegaTildeAt_periodic
    (q : Nat) :
    Function.Periodic
      (nearestQOmegaTildeAt q)
      (nearestQExactPeriod q) := by
  intro t
  unfold nearestQOmegaTildeAt
  rw [Nat.add_mod_right]

/--
The centered nearest-root correction at an arbitrary index
equals its value at the corresponding residue modulo the
exact period.
@isnad1 id=eq.1h2v.s4.4e9b86b6e692 from=translated src=- shape=ef90cc8b vocab=7b87f13e
-/
theorem nearestQCenteredOmegaAt_mod_eq
    (q t : Nat)
    (hq : 0 < q) :
    nearestQCenteredOmegaAt q
        (t % nearestQExactPeriod q) =
      nearestQCenteredOmegaAt q t := by
  exact
    (nearestQCenteredOmegaAt_periodic
      q hq).map_mod_nat t

/--
Away from the end of the exact period, increasing the index
by one adds the corresponding centered correction term to
the periodic antiderivative.
@isnad1 id=eq.2h2v.s6.42c8833ae2fe from=translated src=- shape=960156c6 vocab=e5514d29
-/
theorem nearestQOmegaTildeAt_succ_of_mod_succ_lt
    (q t : Nat)
    (hq : 0 < q)
    (hnext :
      t % nearestQExactPeriod q + 1 <
        nearestQExactPeriod q) :
    nearestQOmegaTildeAt q (t + 1) =
      nearestQOmegaTildeAt q t +
        nearestQCenteredOmegaAt q t := by
  have hone :
      1 % nearestQExactPeriod q = 1 := by
    apply Nat.mod_eq_of_lt
    omega
  have hmod :
      (t + 1) % nearestQExactPeriod q =
        t % nearestQExactPeriod q + 1 := by
    rw [Nat.add_mod, hone]
    exact Nat.mod_eq_of_lt hnext
  unfold nearestQOmegaTildeAt
  rw [
    hmod,
    Finset.sum_range_succ,
    nearestQCenteredOmegaAt_mod_eq
      q t hq
  ]

/--
At the end of the exact period, increasing the index by one
resets the periodic antiderivative to zero. The zero-sum
identity over the full period gives the same increment formula.
@isnad1 id=eq.2h2v.s6.7ce10526e1a8 from=translated src=- shape=7f797197 vocab=e5514d29
-/
theorem nearestQOmegaTildeAt_succ_of_mod_succ_eq
    (q t : Nat)
    (hq : 0 < q)
    (hwrap :
      t % nearestQExactPeriod q + 1 =
        nearestQExactPeriod q) :
    nearestQOmegaTildeAt q (t + 1) =
      nearestQOmegaTildeAt q t +
        nearestQCenteredOmegaAt q t := by
  have hdiv :
      nearestQExactPeriod q ∣ t + 1 := by
    refine
      ⟨t / nearestQExactPeriod q + 1, ?_⟩
    rw [
      Nat.mul_add,
      Nat.mul_one
    ]
    have ht :=
      Nat.mod_add_div
        t
        (nearestQExactPeriod q)
    omega
  have hmod :
      (t + 1) % nearestQExactPeriod q = 0 := by
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hprefix :
      Finset.sum
          (Finset.range
            (t % nearestQExactPeriod q))
          (fun r =>
            nearestQCenteredOmegaAt q r) +
          nearestQCenteredOmegaAt q t =
        0 := by
    calc
      Finset.sum
            (Finset.range
              (t % nearestQExactPeriod q))
            (fun r =>
              nearestQCenteredOmegaAt q r) +
          nearestQCenteredOmegaAt q t =
        Finset.sum
            (Finset.range
              (t % nearestQExactPeriod q))
            (fun r =>
              nearestQCenteredOmegaAt q r) +
          nearestQCenteredOmegaAt q
            (t % nearestQExactPeriod q) := by
              rw [
                nearestQCenteredOmegaAt_mod_eq
                  q t hq
              ]
      _ =
        Finset.sum
          (Finset.range
            (t % nearestQExactPeriod q + 1))
          (fun r =>
            nearestQCenteredOmegaAt q r) := by
              rw [Finset.sum_range_succ]
      _ =
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            nearestQCenteredOmegaAt q r) := by
              rw [hwrap]
      _ = 0 :=
        nearestQCenteredOmegaAt_exactPeriod_sum_zero
          q hq
  unfold nearestQOmegaTildeAt
  rw [hmod]
  simp only [
    Finset.range_zero,
    Finset.sum_empty
  ]
  exact hprefix.symm

/--
For every index, increasing the argument by one adds exactly
the corresponding centered correction term to the periodic
antiderivative.
@isnad1 id=eq.1h2v.s5.0a51342b08c8 from=translated src=- shape=17cf03f6 vocab=58f8031c
-/
theorem nearestQOmegaTildeAt_succ
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeAt q (t + 1) =
      nearestQOmegaTildeAt q t +
        nearestQCenteredOmegaAt q t := by
  have hmodLt :
      t % nearestQExactPeriod q <
        nearestQExactPeriod q := by
    exact
      Nat.mod_lt t
        (nearestQExactPeriod_pos q hq)
  by_cases hnext :
      t % nearestQExactPeriod q + 1 <
        nearestQExactPeriod q
  · exact
      nearestQOmegaTildeAt_succ_of_mod_succ_lt
        q t hq hnext
  · have hwrap :
        t % nearestQExactPeriod q + 1 =
          nearestQExactPeriod q := by
      omega
    exact
      nearestQOmegaTildeAt_succ_of_mod_succ_eq
        q t hq hwrap

/--
The first difference of the periodic antiderivative is the
centered nearest-root correction sequence.
@isnad1 id=eq.1h2v.s5.6391404fe78a from=translated src=- shape=9e409aca vocab=b90da21e
-/
theorem nearestQOmegaTildeAt_succ_sub
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeAt q (t + 1) -
        nearestQOmegaTildeAt q t =
      nearestQCenteredOmegaAt q t := by
  rw [
    nearestQOmegaTildeAt_succ
      q t hq
  ]
  ring

/--
Equivalently, the first difference of the periodic
antiderivative is

`ω_q(t) - μ_q`.
@isnad1 id=eq.1h2v.s5.dd893a2058bc from=translated src=- shape=f2b07145 vocab=bb3116ac
-/
theorem nearestQOmegaTildeAt_succ_sub_eq_omega_sub_mean
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeAt q (t + 1) -
        nearestQOmegaTildeAt q t =
      nearestQOmegaAt q t -
        nearestQOmegaExactPeriodMean q := by
  rw [
    nearestQOmegaTildeAt_succ_sub
      q t hq
  ]
  rfl

/--
Inside the first exact period, the periodic antiderivative
is the ordinary centered prefix sum.
@isnad1 id=eq.1h2v.s4.52ba19355831 from=translated src=- shape=6aecc6ca vocab=eafdd147
-/
theorem nearestQOmegaTildeAt_eq_prefixSum_of_lt_period
    (q r : Nat)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQOmegaTildeAt q r =
      Finset.sum
        (Finset.range r)
        (fun j =>
          nearestQCenteredOmegaAt q j) := by
  unfold nearestQOmegaTildeAt
  rw [Nat.mod_eq_of_lt hr]

/--
Every period of the periodic antiderivative is also a period
of the centered nearest-root correction sequence.
@isnad1 id=periodic.2h2v.s4.01955bfffa85 from=translated src=- shape=094c3536 vocab=80c5ea69
-/
theorem nearestQCenteredOmegaAt_periodic_of_omegaTilde_periodic
    (q d : Nat)
    (hq : 0 < q)
    (hperiod :
      Function.Periodic
        (nearestQOmegaTildeAt q)
        d) :
    Function.Periodic
      (nearestQCenteredOmegaAt q)
      d := by
  intro t
  have hadd :
      t + d + 1 =
        t + 1 + d := by
    omega
  calc
    nearestQCenteredOmegaAt q (t + d) =
        nearestQOmegaTildeAt q (t + d + 1) -
          nearestQOmegaTildeAt q (t + d) := by
      symm
      exact
        nearestQOmegaTildeAt_succ_sub
          q (t + d) hq
    _ =
        nearestQOmegaTildeAt q (t + 1 + d) -
          nearestQOmegaTildeAt q (t + d) := by
      rw [hadd]
    _ =
        nearestQOmegaTildeAt q (t + 1) -
          nearestQOmegaTildeAt q t := by
      rw [
        hperiod (t + 1),
        hperiod t
      ]
    _ =
        nearestQCenteredOmegaAt q t := by
      exact
        nearestQOmegaTildeAt_succ_sub
          q t hq

/--
Every positive period of the periodic antiderivative is at
least `nearestQExactPeriod q`.
@isnad1 id=le.3h2v.s5.b5e41f5563d6 from=translated src=- shape=c40d59d3 vocab=3c0ae579
-/
theorem nearestQExactPeriod_le_of_omegaTilde_periodic
    (q d : Nat)
    (hq : 0 < q)
    (hd : 0 < d)
    (hperiod :
      Function.Periodic
        (nearestQOmegaTildeAt q)
        d) :
    nearestQExactPeriod q ≤ d := by
  have hcentered :
      Function.Periodic
        (nearestQCenteredOmegaAt q)
        d :=
    nearestQCenteredOmegaAt_periodic_of_omegaTilde_periodic
      q d hq hperiod
  have homega :
      Function.Periodic
        (nearestQOmegaAt q)
        d := by
    intro t
    have h := hcentered t
    unfold nearestQCenteredOmegaAt at h
    linarith
  exact
    (nearestQOmegaAt_isLeastPeriod
      q hq).2.2
      d hd homega

/--
For every positive exponent `q`, the periodic antiderivative
has exact least positive period `nearestQExactPeriod q`.
@isnad1 id=isleastp.1h1v.s4.417e737f6f01 from=translated src=- shape=e8ad9c19 vocab=ef62d6fc
-/
theorem nearestQOmegaTildeAt_isLeastPeriod
    (q : Nat)
    (hq : 0 < q) :
    IsLeastPositiveNatPeriod
      (nearestQOmegaTildeAt q)
      (nearestQExactPeriod q) := by
  refine ⟨
    nearestQExactPeriod_pos q hq,
    nearestQOmegaTildeAt_periodic q,
    ?_
  ⟩
  intro d hd hperiod
  exact
    nearestQExactPeriod_le_of_omegaTilde_periodic
      q d hq hd hperiod

/--
The normalized odd q-th power residue sequence.

Since every power residue is congruent to one modulo
`2^d_q`, this quotient extracts the parameter of the
arithmetic progression

`1 + 2^d_q * j`.-/
def nearestQNormalizedResidueAt
    (q r : Nat) : Nat :=
  nearestQPowerResidueAt q r /
    2 ^ nearestQResidueStepExponent q

/--
For every positive `q`, the power residue is reconstructed
from its normalized parameter by

`ρ_q(r) = 1 + 2^d_q * σ_q(r)`.
@isnad1 id=eq.1h2v.s5.1a725da45b96 from=translated src=- shape=4bf73a65 vocab=3d206d0d
-/
theorem nearestQPowerResidueAt_eq_one_add_step_mul_normalized
    (q r : Nat)
    (hq : 0 < q) :
    nearestQPowerResidueAt q r =
      1 +
        2 ^ nearestQResidueStepExponent q *
          nearestQNormalizedResidueAt q r := by
  let s : Nat :=
    2 ^ nearestQResidueStepExponent q
  let y : Nat :=
    nearestQPowerResidueAt q r
  have hdPos :
      0 < nearestQResidueStepExponent q :=
    nearestQResidueStepExponent_pos q hq
  have hsOne :
      1 < s := by
    dsimp [s]
    exact
      Nat.one_lt_two_pow
        (Nat.ne_of_gt hdPos)
  have hmod :
      y % s = 1 := by
    have h :=
      nearestQPowerResidueAt_mod_step
        q r hq
    change
      y % s = 1 % s
      at h
    rw [Nat.mod_eq_of_lt hsOne] at h
    exact h
  have hdecomp :
      1 + s * (y / s) = y := by
    have h :=
      Nat.mod_add_div y s
    rw [hmod] at h
    exact h
  unfold nearestQNormalizedResidueAt
  simpa [s, y] using hdecomp.symm

/--
For every positive `q`, the normalized residue parameter
lies strictly below the predicted image size

`M_q = 2^(q - d_q)`.
@isnad1 id=lt.1h2v.s4.e6081672825c from=translated src=- shape=d8a819b4 vocab=bc2eb307
-/
theorem nearestQNormalizedResidueAt_lt_imageSize
    (q r : Nat)
    (hq : 0 < q) :
    nearestQNormalizedResidueAt q r <
      nearestQResidueImageSize q := by
  rcases
      nearestQPowerResidueAt_exists_predictedParam
        q r hq with
    ⟨j, hj, hjValue⟩
  have hparam :
      1 +
          2 ^ nearestQResidueStepExponent q *
            nearestQNormalizedResidueAt q r =
        1 +
          2 ^ nearestQResidueStepExponent q * j := by
    calc
      1 +
            2 ^ nearestQResidueStepExponent q *
              nearestQNormalizedResidueAt q r =
          nearestQPowerResidueAt q r := by
        symm
        exact
          nearestQPowerResidueAt_eq_one_add_step_mul_normalized
            q r hq
      _ =
          1 +
            2 ^ nearestQResidueStepExponent q * j := by
        exact hjValue.symm
  have hnormalized :
      nearestQNormalizedResidueAt q r = j :=
    nearestQPredictedResidueParam_injective
      q hparam
  rw [hnormalized]
  exact hj

/--
For every positive `q`, the normalized residue sequence has
period `nearestQExactPeriod q`.
@isnad1 id=periodic.1h1v.s4.0d6ab727b958 from=translated src=- shape=fc6cdde2 vocab=b6662025
-/
theorem nearestQNormalizedResidueAt_periodic
    (q : Nat)
    (hq : 0 < q) :
    Function.Periodic
      (nearestQNormalizedResidueAt q)
      (nearestQExactPeriod q) := by
  have hperiod :
      Function.Periodic
        (nearestQPowerResidueAt q)
        (nearestQExactPeriod q) :=
    (nearestQPowerResidueAt_isLeastPeriod
      q hq).2.1
  intro r
  unfold nearestQNormalizedResidueAt
  rw [hperiod r]

/--
For every positive exponent `q`, the normalized residue
sequence has exact least positive period
`nearestQExactPeriod q`.
@isnad1 id=isleastp.1h1v.s4.cc5b7781b521 from=translated src=- shape=9c8b14d8 vocab=b73c7adf
-/
theorem nearestQNormalizedResidueAt_isLeastPeriod
    (q : Nat)
    (hq : 0 < q) :
    IsLeastPositiveNatPeriod
      (nearestQNormalizedResidueAt q)
      (nearestQExactPeriod q) := by
  refine ⟨
    nearestQExactPeriod_pos q hq,
    nearestQNormalizedResidueAt_periodic q hq,
    ?_
  ⟩
  intro d hd hnormalized
  have hresidue :
      Function.Periodic
        (nearestQPowerResidueAt q)
        d := by
    intro r
    calc
      nearestQPowerResidueAt q (r + d) =
          1 +
            2 ^ nearestQResidueStepExponent q *
              nearestQNormalizedResidueAt q (r + d) :=
        nearestQPowerResidueAt_eq_one_add_step_mul_normalized
          q (r + d) hq
      _ =
          1 +
            2 ^ nearestQResidueStepExponent q *
              nearestQNormalizedResidueAt q r := by
        rw [hnormalized r]
      _ =
          nearestQPowerResidueAt q r := by
        symm
        exact
          nearestQPowerResidueAt_eq_one_add_step_mul_normalized
            q r hq
  exact
    (nearestQPowerResidueAt_isLeastPeriod
      q hq).2.2
      d hd hresidue

/--
The centered nearest-root correction has the normalized
residue form

`(M_q - 1 - 2 * σ_q(r)) / (2 * M_q)`.
@isnad1 id=eq.1h2v.s6.01425f1c41a2 from=translated src=- shape=1bc1ecb4 vocab=329a49dc
-/
theorem nearestQCenteredOmegaAt_eq_normalizedFormula
    (q r : Nat)
    (hq : 0 < q) :
    nearestQCenteredOmegaAt q r =
      ((nearestQResidueImageSize q : Rat) -
          1 -
          2 *
            (nearestQNormalizedResidueAt q r : Rat)) /
        (2 *
          (nearestQResidueImageSize q : Rat)) := by
  have hsizeNe :
      (nearestQResidueImageSize q : Rat) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        (nearestQResidueImageSize_pos q))
  have hstepNe :
      ((2 : Rat) ^
          nearestQResidueStepExponent q) ≠ 0 := by
    positivity
  have hproduct :
      ((2 : Rat) ^
            nearestQResidueStepExponent q) *
          (nearestQResidueImageSize q : Rat) =
        (2 : Rat) ^ q :=
    nearestQStepPow_mul_imageSize_cast q
  have hresidue :
      (nearestQPowerResidueAt q r : Rat) =
        1 +
          (2 : Rat) ^
              nearestQResidueStepExponent q *
            (nearestQNormalizedResidueAt q r : Rat) := by
    exact_mod_cast
      (nearestQPowerResidueAt_eq_one_add_step_mul_normalized
        q r hq)
  have hpowSucc :
      (2 : Rat) ^ (q + 1) =
        (2 : Rat) ^ q * 2 := by
    rw [pow_succ]
  unfold
    nearestQCenteredOmegaAt
    nearestQOmegaAt
  rw [
    nearestQOmegaExactPeriodMean_eq_closed
      q hq,
    hresidue,
    hpowSucc,
    ← hproduct
  ]
  field_simp [hsizeNe, hstepNe]
  ring

/--
The periodic antiderivative is the prefix sum of the
normalized centered-residue formula.
@isnad1 id=eq.1h2v.s6.a971b0d3c1d8 from=translated src=- shape=8b186024 vocab=bec07fc7
-/
theorem nearestQOmegaTildeAt_eq_normalizedSum
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeAt q t =
      Finset.sum
        (Finset.range
          (t % nearestQExactPeriod q))
        (fun r =>
          ((nearestQResidueImageSize q : Rat) -
                1 -
                2 *
                  (nearestQNormalizedResidueAt q r : Rat)) /
            (2 *
              (nearestQResidueImageSize q : Rat))) := by
  unfold nearestQOmegaTildeAt
  apply Finset.sum_congr rfl
  intro r _hr
  exact
    nearestQCenteredOmegaAt_eq_normalizedFormula
      q r hq

/--
A finite sum of normalized centered-residue terms can be
written using the prefix sum of the normalized residues.
@isnad1 id=eq.0h2v.s7.ee1bc7615e85 from=translated src=- shape=f838e499 vocab=d937c31c
-/
theorem nearestQNormalizedFormula_sum_eq
    (q n : Nat) :
    Finset.sum
        (Finset.range n)
        (fun r =>
          ((nearestQResidueImageSize q : Rat) -
                1 -
                2 *
                  (nearestQNormalizedResidueAt q r : Rat)) /
            (2 *
              (nearestQResidueImageSize q : Rat))) =
      (((n : Nat) : Rat) *
            ((nearestQResidueImageSize q : Rat) - 1) -
          2 *
            Finset.sum
              (Finset.range n)
              (fun r =>
                (nearestQNormalizedResidueAt q r : Rat))) /
        (2 *
          (nearestQResidueImageSize q : Rat)) := by
  have hsizeNe :
      (nearestQResidueImageSize q : Rat) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        (nearestQResidueImageSize_pos q))
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [
        Finset.sum_range_succ,
        Finset.sum_range_succ,
        ih
      ]
      push_cast
      field_simp [hsizeNe]
      ring

/--
The exact normalized-residue formula for the periodic
antiderivative.

Writing `r = t mod P_q`, it is

`(r * (M_q - 1) - 2 * ∑_{j < r} σ_q(j)) / (2 * M_q)`.
@isnad1 id=eq.1h2v.s6.3173fe7bcd65 from=translated src=- shape=5e6d050a vocab=bec07fc7
-/
theorem nearestQOmegaTildeAt_eq_normalizedPrefixFormula
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeAt q t =
      (((t % nearestQExactPeriod q : Nat) : Rat) *
            ((nearestQResidueImageSize q : Rat) - 1) -
          2 *
            Finset.sum
              (Finset.range
                (t % nearestQExactPeriod q))
              (fun r =>
                (nearestQNormalizedResidueAt q r : Rat))) /
        (2 *
          (nearestQResidueImageSize q : Rat)) := by
  rw [
    nearestQOmegaTildeAt_eq_normalizedSum
      q t hq,
    nearestQNormalizedFormula_sum_eq
      q
      (t % nearestQExactPeriod q)
  ]

/--
For `q = 2`, the correction sequence is constant, so its
centered version vanishes identically.
@isnad1 id=eq.0h1v.s4.d1bb7d14a3c2 from=translated src=- shape=d7485c18 vocab=e3f2b426
-/
@[simp]
theorem nearestQCenteredOmegaAt_two
    (r : Nat) :
    nearestQCenteredOmegaAt 2 r = 0 := by
  unfold
    nearestQCenteredOmegaAt
    nearestQOmegaAt
  rw [
    nearestQPowerResidueAt_two,
    nearestQOmegaExactPeriodMean_two
  ]
  norm_num

/--
For `q = 4`, the correction sequence is constant, so its
centered version vanishes identically.
@isnad1 id=eq.0h1v.s4.54b4fb07c688 from=translated src=- shape=d7485c18 vocab=e3f2b426
-/
@[simp]
theorem nearestQCenteredOmegaAt_four
    (r : Nat) :
    nearestQCenteredOmegaAt 4 r = 0 := by
  unfold
    nearestQCenteredOmegaAt
    nearestQOmegaAt
  rw [
    nearestQPowerResidueAt_four,
    nearestQOmegaExactPeriodMean_four
  ]
  norm_num

/--
For the exceptional exponents `q = 2` and `q = 4`, the
periodic antiderivative vanishes identically.
@isnad1 id=eq.1h2v.s5.01254dc234b4 from=translated src=- shape=0e53ca3a vocab=fc9d762b
-/
theorem nearestQOmegaTildeAt_eq_zero_of_exceptional
    (q t : Nat)
    (hExceptional :
      q = 2 ∨ q = 4) :
    nearestQOmegaTildeAt q t = 0 := by
  rcases hExceptional with hqTwo | hqFour
  · subst q
    simp [nearestQOmegaTildeAt]
  · subst q
    simp [nearestQOmegaTildeAt]

/--
If the periodic antiderivative vanishes identically, then
the centered nearest-root correction sequence also vanishes
identically.
@isnad1 id=eq.2h2v.s5.9b7b84302455 from=translated src=- shape=84af46ba vocab=88e3fd51
-/
theorem nearestQCenteredOmegaAt_eq_zero_of_omegaTilde_eq_zero
    (q : Nat)
    (hq : 0 < q)
    (hzero :
      ∀ t : Nat,
        nearestQOmegaTildeAt q t = 0) :
    ∀ t : Nat,
      nearestQCenteredOmegaAt q t = 0 := by
  intro t
  have hdiff :=
    nearestQOmegaTildeAt_succ_sub
      q t hq
  rw [
    hzero (t + 1),
    hzero t
  ] at hdiff
  simpa using hdiff.symm

/--
If the centered correction sequence vanishes identically,
then the original correction sequence is constant and hence
has period one.
@isnad1 id=periodic.1h1v.s4.6b535fc3cc88 from=translated src=- shape=79ecb749 vocab=54bdea3b
-/
theorem nearestQOmegaAt_periodic_one_of_centered_eq_zero
    (q : Nat)
    (hzero :
      ∀ t : Nat,
        nearestQCenteredOmegaAt q t = 0) :
    Function.Periodic
      (nearestQOmegaAt q)
      1 := by
  intro t
  have hnext :=
    hzero (t + 1)
  have hcurrent :=
    hzero t
  change
    nearestQOmegaAt q (t + 1) -
        nearestQOmegaExactPeriodMean q =
      0
    at hnext
  change
    nearestQOmegaAt q t -
        nearestQOmegaExactPeriodMean q =
      0
    at hcurrent
  linarith

/--
If the periodic antiderivative vanishes identically, then
the exact least positive period of the correction sequence
is one.
@isnad1 id=eq.2h1v.s5.edda823a64c5 from=translated src=- shape=99cdd659 vocab=64afb4ce
-/
theorem nearestQExactPeriod_eq_one_of_omegaTilde_eq_zero
    (q : Nat)
    (hq : 0 < q)
    (hzero :
      ∀ t : Nat,
        nearestQOmegaTildeAt q t = 0) :
    nearestQExactPeriod q = 1 := by
  have hcentered :
      ∀ t : Nat,
        nearestQCenteredOmegaAt q t = 0 :=
    nearestQCenteredOmegaAt_eq_zero_of_omegaTilde_eq_zero
      q hq hzero
  have homega :
      Function.Periodic
        (nearestQOmegaAt q)
        1 :=
    nearestQOmegaAt_periodic_one_of_centered_eq_zero
      q hcentered
  have hle :
      nearestQExactPeriod q ≤ 1 :=
    (nearestQOmegaAt_isLeastPeriod
      q hq).2.2
      1
      (by norm_num)
      homega
  have hpos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos q hq
  omega

/--
For every exponent `q ≥ 2`, the exact period is one
if and only if `q = 2` or `q = 4`.
@isnad1 id=iff.1h1v.s5.55abfb537bdc from=translated src=- shape=340557f5 vocab=eb3feae1
-/
theorem nearestQExactPeriod_eq_one_iff_exceptional
    (q : Nat)
    (hq : 2 ≤ q) :
    nearestQExactPeriod q = 1 ↔
      q = 2 ∨ q = 4 := by
  constructor
  · intro hperiod
    by_contra hExceptional
    unfold nearestQExactPeriod at hperiod
    rw [ite_eq_right hExceptional] at hperiod
    by_cases hqOdd :
        Odd q
    · rw [ite_eq_left hqOdd] at hperiod
      rw [nearestQResiduePeriod_eq] at hperiod
      have hexponent :
          0 < q - 1 := by
        omega
      have hpow :
          1 < 2 ^ (q - 1) := by
        exact
          Nat.one_lt_two_pow
            (Nat.ne_of_gt hexponent)
      omega
    · rw [ite_eq_right hqOdd] at hperiod
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
      have hperiodTwo :
          2 ≤ nearestQEvenResiduePeriod q :=
        nearestQEvenResiduePeriod_two_le
          q hqSix hqEven
      omega
  · intro hExceptional
    unfold nearestQExactPeriod
    rw [ite_eq_left hExceptional]

/--
For every `q ≥ 2`, the periodic antiderivative vanishes
identically if and only if `q = 2` or `q = 4`.
@isnad1 id=iff.1h1v.s5.1d1c89c8ef3c from=translated src=- shape=84306d76 vocab=a4fd573d
-/
theorem nearestQOmegaTildeAt_eq_zero_iff_exceptional
    (q : Nat)
    (hq : 2 ≤ q) :
    (∀ t : Nat,
      nearestQOmegaTildeAt q t = 0) ↔
      q = 2 ∨ q = 4 := by
  constructor
  · intro hzero
    apply
      (nearestQExactPeriod_eq_one_iff_exceptional
        q hq).1
    exact
      nearestQExactPeriod_eq_one_of_omegaTilde_eq_zero
        q
        (by omega)
        hzero
  · intro hExceptional t
    exact
      nearestQOmegaTildeAt_eq_zero_of_exceptional
        q t hExceptional

/--
For every `q ≥ 2`, the centered correction sequence
vanishes identically if and only if `q = 2` or `q = 4`.
@isnad1 id=iff.1h1v.s5.df424450f028 from=translated src=- shape=84306d76 vocab=71e082f9
-/
theorem nearestQCenteredOmegaAt_eq_zero_iff_exceptional
    (q : Nat)
    (hq : 2 ≤ q) :
    (∀ t : Nat,
      nearestQCenteredOmegaAt q t = 0) ↔
      q = 2 ∨ q = 4 := by
  constructor
  · intro hcentered
    apply
      (nearestQOmegaTildeAt_eq_zero_iff_exceptional
        q hq).1
    intro t
    unfold nearestQOmegaTildeAt
    apply Finset.sum_eq_zero
    intro r _hr
    exact hcentered r
  · intro hExceptional
    rcases hExceptional with hqTwo | hqFour
    · subst q
      intro t
      exact nearestQCenteredOmegaAt_two t
    · subst q
      intro t
      exact nearestQCenteredOmegaAt_four t

/--
The normalized residue sequence has the exact period
`nearestQExactPeriod q`, takes values below `M_q`, reconstructs
the original power residue, and gives the centered correction
through the normalized-residue formula.
@isnad1 id=and.1h1v.s7.c27f12513e91 from=translated src=- shape=cb22e00b vocab=58e83783
-/
theorem nearestQNormalizedResidueMainTheorem
    (q : Nat)
    (hq : 0 < q) :
    IsLeastPositiveNatPeriod
        (nearestQNormalizedResidueAt q)
        (nearestQExactPeriod q) ∧
      (∀ r : Nat,
        nearestQNormalizedResidueAt q r <
          nearestQResidueImageSize q) ∧
      (∀ r : Nat,
        nearestQPowerResidueAt q r =
          1 +
            2 ^ nearestQResidueStepExponent q *
              nearestQNormalizedResidueAt q r) ∧
      (∀ r : Nat,
        nearestQCenteredOmegaAt q r =
          ((nearestQResidueImageSize q : Rat) -
              1 -
              2 *
                (nearestQNormalizedResidueAt q r : Rat)) /
            (2 *
              (nearestQResidueImageSize q : Rat))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      nearestQNormalizedResidueAt_isLeastPeriod
        q hq
  · intro r
    exact
      nearestQNormalizedResidueAt_lt_imageSize
        q r hq
  · intro r
    exact
      nearestQPowerResidueAt_eq_one_add_step_mul_normalized
        q r hq
  · intro r
    exact
      nearestQCenteredOmegaAt_eq_normalizedFormula
        q r hq

/--
For every `q ≥ 2`, the periodic antiderivative vanishes
identically if and only if the centered correction sequence
vanishes identically.
@isnad1 id=iff.1h1v.s5.f35811ef9398 from=translated src=- shape=ccec76ad vocab=bccf2615
-/
theorem nearestQOmegaTildeAt_eq_zero_iff_centeredOmega_eq_zero
    (q : Nat)
    (hq : 2 ≤ q) :
    (∀ t : Nat,
      nearestQOmegaTildeAt q t = 0) ↔
      (∀ t : Nat,
        nearestQCenteredOmegaAt q t = 0) := by
  calc
    (∀ t : Nat,
        nearestQOmegaTildeAt q t = 0) ↔
        q = 2 ∨ q = 4 :=
      nearestQOmegaTildeAt_eq_zero_iff_exceptional
        q hq
    _ ↔
        (∀ t : Nat,
          nearestQCenteredOmegaAt q t = 0) :=
      (nearestQCenteredOmegaAt_eq_zero_iff_exceptional
        q hq).symm

/--
The complete periodic-antiderivative result for every
exponent `q ≥ 2`:

* `nearestQOmegaTildeAt q` has exact least positive period
  `nearestQExactPeriod q`;
* its first difference is `ω_q(t) - μ_q`;
* it has the explicit normalized-residue prefix formula;
* it vanishes identically precisely for `q = 2` and `q = 4`.
@isnad1 id=and.1h1v.s7.dea6b8a45870 from=translated src=- shape=2c1f425c vocab=cd0d8d12
-/
theorem nearestQPeriodicAntiderivativeMainTheorem
    (q : Nat)
    (hq : 2 ≤ q) :
    IsLeastPositiveNatPeriod
        (nearestQOmegaTildeAt q)
        (nearestQExactPeriod q) ∧
      (∀ t : Nat,
        nearestQOmegaTildeAt q (t + 1) -
            nearestQOmegaTildeAt q t =
          nearestQOmegaAt q t -
            nearestQOmegaExactPeriodMean q) ∧
      (∀ t : Nat,
        nearestQOmegaTildeAt q t =
          (((t % nearestQExactPeriod q : Nat) : Rat) *
                ((nearestQResidueImageSize q : Rat) - 1) -
              2 *
                Finset.sum
                  (Finset.range
                    (t % nearestQExactPeriod q))
                  (fun r =>
                    (nearestQNormalizedResidueAt q r : Rat))) /
            (2 *
              (nearestQResidueImageSize q : Rat))) ∧
      ((∀ t : Nat,
          nearestQOmegaTildeAt q t = 0) ↔
        q = 2 ∨ q = 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      nearestQOmegaTildeAt_isLeastPeriod
        q
        (by omega)
  · intro t
    exact
      nearestQOmegaTildeAt_succ_sub_eq_omega_sub_mean
        q t
        (by omega)
  · intro t
    exact
      nearestQOmegaTildeAt_eq_normalizedPrefixFormula
        q t
        (by omega)
  · exact
      nearestQOmegaTildeAt_eq_zero_iff_exceptional
        q hq

end RoundedRootSums
