/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftNearestAntiderivative
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftNearestFourier
import Tengoku.Seed.Analysis.Complex.Trigonometric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Symmetry of nearest-root residue sequences

This file proves the palindromic symmetry of the nearest-root
residue sequence for nonexceptional even exponents and derives
the corresponding antisymmetry of the periodic correction.
-/

namespace RoundedRootSums

/--
The zero-based mirror of an index inside one exact period.

The article's positive-index reflection

`m ↦ P + 1 - m`

becomes

`r ↦ P - 1 - r`

after writing `r = m - 1`.-/
def nearestQMirrorIndex
    (q r : Nat) : Nat :=
  nearestQExactPeriod q - 1 - r

/--
The mirror of an index lying in the exact period also lies
inside that exact period.
@isnad1 id=lt.2h2v.s4.48452764a8e3 from=translated src=- shape=7011ddb4 vocab=9ffd0ee9
-/
theorem nearestQMirrorIndex_lt_period
    (q r : Nat)
    (hq : 6 ≤ q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQMirrorIndex q r <
      nearestQExactPeriod q := by
  have hperiodPos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos
      q
      (by omega)
  unfold nearestQMirrorIndex
  omega

/--
Inside one exact period, the odd base attached to the mirror
index and the odd base attached to the original index sum to
twice the exact period.
@isnad1 id=eq.2h2v.s6.305a8d777f97 from=translated src=- shape=904779d6 vocab=803a8dc8
-/
theorem nearestQMirrorOddBase_add_eq_two_mul_period
    (q r : Nat)
    (hq : 6 ≤ q)
    (hr :
      r < nearestQExactPeriod q) :
    (2 * nearestQMirrorIndex q r + 1) +
        (2 * r + 1) =
      2 * nearestQExactPeriod q := by
  have hperiodPos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos
      q
      (by omega)
  unfold nearestQMirrorIndex
  omega

/--
For even `q ≥ 6`, the two mirrored odd bases sum exactly to
the additive base shift used in the even-period argument.
@isnad1 id=eq.3h2v.s6.92d38c2832a9 from=translated src=- shape=1b027365 vocab=5e05f6d7
-/
theorem nearestQMirrorOddBase_add_eq_evenShift
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    (2 * nearestQMirrorIndex q r + 1) +
        (2 * r + 1) =
      nearestQEvenShift q := by
  rw [
    nearestQEvenShift_eq_two_mul_period
      q hq hqEven,
    ← nearestQExactPeriod_eq_evenResiduePeriod_of_even_ge_six
      q hq hqEven
  ]
  exact
    nearestQMirrorOddBase_add_eq_two_mul_period
      q r hq hr

/--
Mirroring twice inside one exact period returns the
original zero-based index.
@isnad1 id=eq.2h2v.s4.b5ceedea65cd from=translated src=- shape=f16f0e81 vocab=9ffd0ee9
-/
theorem nearestQMirrorIndex_involutive
    (q r : Nat)
    (hq : 6 ≤ q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQMirrorIndex q
        (nearestQMirrorIndex q r) =
      r := by
  have hperiodPos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos
      q
      (by omega)
  unfold nearestQMirrorIndex
  omega

/--
For even `q ≥ 6`, the odd base belonging to the mirrored
index is the even-case additive shift minus the original
odd base.
@isnad1 id=eq.3h2v.s6.93164109a348 from=translated src=- shape=38368913 vocab=c3ac0c73
-/
theorem nearestQMirrorOddBase_eq_evenShift_sub
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    2 * nearestQMirrorIndex q r + 1 =
      nearestQEvenShift q - (2 * r + 1) := by
  have hsum :
      (2 * nearestQMirrorIndex q r + 1) +
          (2 * r + 1) =
        nearestQEvenShift q :=
    nearestQMirrorOddBase_add_eq_evenShift
      q r hq hqEven hr
  omega

/--
Inside one exact period for even `q ≥ 6`, the original odd
base is strictly smaller than the even-case additive shift.
@isnad1 id=lt.3h2v.s5.8e7916990e2a from=translated src=- shape=2578563d vocab=a06bdce3
-/
theorem nearestQOddBase_lt_evenShift
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    2 * r + 1 <
      nearestQEvenShift q := by
  have hsum :
      (2 * nearestQMirrorIndex q r + 1) +
          (2 * r + 1) =
        nearestQEvenShift q :=
    nearestQMirrorOddBase_add_eq_evenShift
      q r hq hqEven hr
  have hmirrorPos :
      0 < 2 * nearestQMirrorIndex q r + 1 := by
    omega
  omega

/--
After subtracting the even-case additive shift, the mirrored
odd base becomes the negative of the original odd base.
@isnad1 id=eq.3h2v.s6.977bae7bfa9c from=translated src=- shape=a48588b6 vocab=776117bd
-/
theorem nearestQMirrorOddBase_sub_evenShift_eq_neg
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    (((2 * nearestQMirrorIndex q r + 1 : Nat) : Int) -
        (nearestQEvenShift q : Int)) =
      -((2 * r + 1 : Nat) : Int) := by
  have hsumNat :
      (2 * nearestQMirrorIndex q r + 1) +
          (2 * r + 1) =
        nearestQEvenShift q :=
    nearestQMirrorOddBase_add_eq_evenShift
      q r hq hqEven hr
  have hsumInt :
      ((2 * nearestQMirrorIndex q r + 1 : Nat) : Int) +
          ((2 * r + 1 : Nat) : Int) =
        (nearestQEvenShift q : Int) := by
    exact_mod_cast hsumNat
  linarith

/--
For even `q`, shifting the mirrored odd base by the
even-case additive shift and then taking the `q`-th power
recovers exactly the `q`-th power of the original odd base.
@isnad1 id=eq.3h2v.s6.1cdf61d711de from=translated src=- shape=f6122f08 vocab=e52ff39c
-/
theorem nearestQMirrorOddBase_shifted_pow_eq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    ((((2 * nearestQMirrorIndex q r + 1 : Nat) : Int) -
          (nearestQEvenShift q : Int)) ^ q) =
      (((2 * r + 1 : Nat) : Int) ^ q) := by
  rw [
    nearestQMirrorOddBase_sub_evenShift_eq_neg
      q r hq hqEven hr
  ]
  exact
    hqEven.neg_pow
      (((2 * r + 1 : Nat) : Int))

/--
For even `q ≥ 6`, the original half-shift period candidate
is `2^ν₂(q)` times the exact period.
@isnad1 id=eq.2h1v.s5.7223186bfd5f from=translated src=- shape=570bd661 vocab=b45fddf3
-/
theorem nearestQResiduePeriod_eq_twoAdic_mul_exactPeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQResiduePeriod q =
      2 ^ nearestQTwoAdicOrder q *
        nearestQExactPeriod q := by
  have hsLt :
      nearestQTwoAdicOrder q < q :=
    nearestQTwoAdicOrder_lt_self
      q
      (by omega)
  calc
    nearestQResiduePeriod q =
        2 ^ (q - 1) := by
      exact nearestQResiduePeriod_eq q
    _ =
        2 ^
          (nearestQTwoAdicOrder q +
            (q - 1 - nearestQTwoAdicOrder q)) := by
      congr 1
      omega
    _ =
        2 ^ nearestQTwoAdicOrder q *
          2 ^ (q - 1 - nearestQTwoAdicOrder q) := by
      rw [pow_add]
    _ =
        2 ^ nearestQTwoAdicOrder q *
          nearestQExactPeriod q := by
      rw [
        nearestQExactPeriod_eq_evenResiduePeriod_of_even_ge_six
          q hq hqEven
      ]
      rfl

/--
For even `q ≥ 6`, reflection inside the original candidate
period `2^(q-1)` preserves the q-th power residue.
@isnad1 id=eq.3h2v.s5.33e7259dbad3 from=translated src=- shape=5b06668e vocab=df1324ae
-/
theorem nearestQPowerResidueAt_candidateMirror_eq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQPowerResidueAt q
        (nearestQResiduePeriod q - 1 - r) =
      nearestQPowerResidueAt q r := by
  have hqPos :
      0 < q := by
    omega
  have hperiodLe :
      nearestQExactPeriod q ≤
        nearestQResiduePeriod q := by
    exact
      (nearestQPowerResidueAt_isLeastPeriod
        q hqPos).2.2
        (nearestQResiduePeriod q)
        (nearestQResiduePeriod_pos q)
        (nearestQPowerResidueAt_periodic
          q hqPos)
  have hrCandidate :
      r < nearestQResiduePeriod q :=
    lt_of_lt_of_le hr hperiodLe
  have htwoPeriod :
      2 * nearestQResiduePeriod q =
        2 ^ q := by
    rw [nearestQResiduePeriod_eq]
    calc
      2 * 2 ^ (q - 1) =
          2 ^ (q - 1) * 2 := by
        ac_rfl
      _ =
          2 ^ ((q - 1) + 1) := by
        rw [pow_succ]
      _ =
          2 ^ q := by
        congr 1
        omega
  have hxLt :
      2 * r + 1 < 2 ^ q := by
    omega
  have hbase :
      2 *
            (nearestQResiduePeriod q - 1 - r) +
          1 =
        2 ^ q - (2 * r + 1) := by
    omega
  have hsumZ :
      (((2 ^ q - (2 * r + 1) : Nat) :
          ZMod (2 ^ q))) +
          (((2 * r + 1 : Nat) :
            ZMod (2 ^ q))) =
        0 := by
    have hNat :
        (2 ^ q - (2 * r + 1)) +
            (2 * r + 1) =
          2 ^ q :=
      Nat.sub_add_cancel
        (Nat.le_of_lt hxLt)
    have hCast :=
      congrArg
        (fun z : Nat =>
          (z : ZMod (2 ^ q)))
        hNat
    simpa using hCast
  have hneg :
      (((2 ^ q - (2 * r + 1) : Nat) :
          ZMod (2 ^ q))) =
        -(((2 * r + 1 : Nat) :
          ZMod (2 ^ q))) := by
    have h :=
      congrArg
        (fun z : ZMod (2 ^ q) =>
          z -
            (((2 * r + 1 : Nat) :
              ZMod (2 ^ q))))
        hsumZ
    simpa using h
  have hpowZ :
      ((((2 ^ q - (2 * r + 1)) ^ q : Nat) :
          ZMod (2 ^ q))) =
        (((2 * r + 1) ^ q : Nat) :
          ZMod (2 ^ q)) := by
    have hpow :=
      congrArg
        (fun z : ZMod (2 ^ q) =>
          z ^ q)
        hneg
    calc
      ((((2 ^ q - (2 * r + 1)) ^ q : Nat) :
          ZMod (2 ^ q))) =
        ((((2 ^ q - (2 * r + 1) : Nat) :
            ZMod (2 ^ q))) ^ q) := by
          simp
      _ =
        (-(((2 * r + 1 : Nat) :
            ZMod (2 ^ q)))) ^ q := by
          exact hpow
      _ =
        ((((2 * r + 1 : Nat) :
            ZMod (2 ^ q))) ^ q) := by
          exact
            hqEven.neg_pow
              (((2 * r + 1 : Nat) :
                ZMod (2 ^ q)))
      _ =
        (((2 * r + 1) ^ q : Nat) :
          ZMod (2 ^ q)) := by
          simp
  have hmod :
      (2 ^ q - (2 * r + 1)) ^ q %
          2 ^ q =
        (2 * r + 1) ^ q %
          2 ^ q := by
    exact
      (ZMod.natCast_eq_natCast_iff'
        ((2 ^ q - (2 * r + 1)) ^ q)
        ((2 * r + 1) ^ q)
        (2 ^ q)).1
        hpowZ
  rw [
    nearestQPowerResidueAt_eq_oddPowerMod,
    nearestQPowerResidueAt_eq_oddPowerMod,
    hbase
  ]
  exact hmod

/--
For even `q ≥ 6`, the q-th power residue sequence is
palindromic on its exact period.

In zero-based indexing this is

`ρ(P - 1 - r) = ρ(r)`.
@isnad1 id=eq.3h2v.s5.2c0e0f4db3b5 from=translated src=- shape=c166f6fc vocab=0a61fc3b
-/
theorem nearestQPowerResidueAt_mirror_eq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQPowerResidueAt q
        (nearestQMirrorIndex q r) =
      nearestQPowerResidueAt q r := by
  let K :=
    2 ^ nearestQTwoAdicOrder q
  let P :=
    nearestQExactPeriod q
  have hfactor :
      nearestQResiduePeriod q =
        K * P := by
    dsimp [K, P]
    exact
      nearestQResiduePeriod_eq_twoAdic_mul_exactPeriod
        q hq hqEven
  have hKPos :
      0 < K := by
    dsimp [K]
    positivity
  have hKSplit :
      K = 1 + (K - 1) := by
    omega
  have hperiodSplit :
      nearestQResiduePeriod q =
        P + (K - 1) * P := by
    calc
      nearestQResiduePeriod q =
          K * P :=
        hfactor
      _ =
          (1 + (K - 1)) * P := by
        rw [← hKSplit]
      _ =
          P + (K - 1) * P := by
        rw [Nat.add_mul]
        simp
  have hindex :
      nearestQResiduePeriod q - 1 - r =
        nearestQMirrorIndex q r +
          (K - 1) * P := by
    rw [hperiodSplit]
    dsimp [P]
    unfold nearestQMirrorIndex
    omega
  have hperiod :
      Function.Periodic
        (nearestQPowerResidueAt q)
        P := by
    dsimp [P]
    exact
      (nearestQPowerResidueAt_isLeastPeriod
        q
        (by omega)).2.1
  have hmultiple :
      Function.Periodic
        (nearestQPowerResidueAt q)
        ((K - 1) * P) := by
    exact
      hperiod.nat_mul (K - 1)
  calc
    nearestQPowerResidueAt q
        (nearestQMirrorIndex q r) =
      nearestQPowerResidueAt q
        (nearestQMirrorIndex q r +
          (K - 1) * P) := by
      symm
      exact
        hmultiple
          (nearestQMirrorIndex q r)
    _ =
      nearestQPowerResidueAt q
        (nearestQResiduePeriod q - 1 - r) := by
      congr 1
      exact hindex.symm
    _ =
      nearestQPowerResidueAt q r :=
      nearestQPowerResidueAt_candidateMirror_eq
        q r hq hqEven hr

/--
For even `q ≥ 6`, the nearest-root correction sequence is
palindromic on its exact period.
@isnad1 id=eq.3h2v.s5.879ce38acf5a from=translated src=- shape=afbfc288 vocab=8020579d
-/
theorem nearestQOmegaAt_mirror_eq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQOmegaAt q
        (nearestQMirrorIndex q r) =
      nearestQOmegaAt q r := by
  unfold nearestQOmegaAt
  rw [
    nearestQPowerResidueAt_mirror_eq
      q r hq hqEven hr
  ]

/--
For even `q ≥ 6`, subtracting the exact-period mean preserves
the palindromic symmetry.
@isnad1 id=eq.3h2v.s5.da4e9fc6a46d from=translated src=- shape=afbfc288 vocab=ce7ac87c
-/
theorem nearestQCenteredOmegaAt_mirror_eq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQCenteredOmegaAt q
        (nearestQMirrorIndex q r) =
      nearestQCenteredOmegaAt q r := by
  unfold nearestQCenteredOmegaAt
  rw [
    nearestQOmegaAt_mirror_eq
      q r hq hqEven hr
  ]

/--
In positive indexing, palindromicity of the centered
correction takes the form

`a(P - m) = a(m - 1)`

for `1 ≤ m ≤ P`.
@isnad1 id=eq.4h2v.s6.ba32481fdf50 from=translated src=- shape=090592fb vocab=4c805810
-/
theorem nearestQCenteredOmegaAt_period_sub_eq_pred
    (q m : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hmPos : 0 < m)
    (hmLe :
      m ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaAt q
        (nearestQExactPeriod q - m) =
      nearestQCenteredOmegaAt q
        (m - 1) := by
  have hr :
      m - 1 <
        nearestQExactPeriod q := by
    omega
  have hmirror :
      nearestQMirrorIndex q (m - 1) =
        nearestQExactPeriod q - m := by
    unfold nearestQMirrorIndex
    omega
  rw [← hmirror]
  exact
    nearestQCenteredOmegaAt_mirror_eq
      q
      (m - 1)
      hq
      hqEven
      hr

/--
The periodic antiderivative vanishes at the end of one
exact period.
@isnad1 id=eq.0h1v.s3.87a5f1cef3ca from=translated src=- shape=6ae13bdd vocab=c0fdc3d5
-/
@[simp]
theorem nearestQOmegaTildeAt_exactPeriod_eq_zero
    (q : Nat) :
    nearestQOmegaTildeAt q
        (nearestQExactPeriod q) =
      0 := by
  have h :=
    nearestQOmegaTildeAt_periodic q 0
  simpa using h

/--
Moving one step backward from the end of the exact period
adds the centered correction at the reflected index.

For `1 ≤ m ≤ P`,

`Ω̃(P - (m - 1)) = Ω̃(P - m) + a(m - 1)`.
@isnad1 id=eq.4h2v.s6.92474e4e7493 from=translated src=- shape=d603e738 vocab=1a31c763
-/
theorem nearestQOmegaTildeAt_period_sub_pred
    (q m : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hmPos : 0 < m)
    (hmLe :
      m ≤ nearestQExactPeriod q) :
    nearestQOmegaTildeAt q
        (nearestQExactPeriod q - (m - 1)) =
      nearestQOmegaTildeAt q
          (nearestQExactPeriod q - m) +
        nearestQCenteredOmegaAt q
          (m - 1) := by
  have hqPos :
      0 < q := by
    omega
  have hindex :
      nearestQExactPeriod q - (m - 1) =
        (nearestQExactPeriod q - m) + 1 := by
    omega
  calc
    nearestQOmegaTildeAt q
        (nearestQExactPeriod q - (m - 1)) =
      nearestQOmegaTildeAt q
        ((nearestQExactPeriod q - m) + 1) := by
      rw [hindex]
    _ =
      nearestQOmegaTildeAt q
          (nearestQExactPeriod q - m) +
        nearestQCenteredOmegaAt q
          (nearestQExactPeriod q - m) := by
      exact
        nearestQOmegaTildeAt_succ
          q
          (nearestQExactPeriod q - m)
          hqPos
    _ =
      nearestQOmegaTildeAt q
          (nearestQExactPeriod q - m) +
        nearestQCenteredOmegaAt q
          (m - 1) := by
      rw [
        nearestQCenteredOmegaAt_period_sub_eq_pred
          q m hq hqEven hmPos hmLe
      ]

/--
For even `q ≥ 6`, the periodic antiderivative of the
centered nearest-root correction is antisymmetric on one
exact period:

`Ω̃(P - t) = -Ω̃(t)`

for `0 ≤ t ≤ P`.
@isnad1 id=eq.3h2v.s5.bce6d529964c from=translated src=- shape=c3253fd8 vocab=3e596a38
-/
theorem nearestQOmegaTildeAt_period_sub_eq_neg
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (ht :
      t ≤ nearestQExactPeriod q) :
    nearestQOmegaTildeAt q
        (nearestQExactPeriod q - t) =
      -nearestQOmegaTildeAt q t := by
  have hqPos :
      0 < q := by
    omega
  have hmain :
      ∀ u : Nat,
        u ≤ nearestQExactPeriod q →
        nearestQOmegaTildeAt q
            (nearestQExactPeriod q - u) =
          -nearestQOmegaTildeAt q u := by
    intro u
    induction u with
    | zero =>
        intro _
        simp [
          nearestQOmegaTildeAt_exactPeriod_eq_zero
        ]
    | succ u ih =>
        intro huSucc
        have hu :
            u ≤ nearestQExactPeriod q := by
          omega
        have hih :
            nearestQOmegaTildeAt q
                (nearestQExactPeriod q - u) =
              -nearestQOmegaTildeAt q u :=
          ih hu
        have hback :
            nearestQOmegaTildeAt q
                (nearestQExactPeriod q - u) =
              nearestQOmegaTildeAt q
                  (nearestQExactPeriod q - (u + 1)) +
                nearestQCenteredOmegaAt q u := by
          have h :=
            nearestQOmegaTildeAt_period_sub_pred
              q
              (u + 1)
              hq
              hqEven
              (by omega)
              (by omega)
          simpa using h
        have hforward :
            nearestQOmegaTildeAt q (u + 1) =
              nearestQOmegaTildeAt q u +
                nearestQCenteredOmegaAt q u := by
          exact
            nearestQOmegaTildeAt_succ
              q u hqPos
        linarith
  exact
    hmain t ht

/--
For even `q ≥ 6`, the exact period is twice the
even-residue half-period.
@isnad1 id=eq.2h1v.s5.82ae05285701 from=translated src=- shape=313f7a45 vocab=4d9a9cbb
-/
theorem nearestQExactPeriod_eq_two_mul_halfPeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQExactPeriod q =
      2 * nearestQEvenResidueHalfPeriod q := by
  rw [
    nearestQExactPeriod_eq_evenResiduePeriod_of_even_ge_six
      q hq hqEven
  ]
  symm
  exact
    two_mul_nearestQEvenResidueHalfPeriod
      q hq hqEven

/--
For even `q ≥ 6`, the periodic antiderivative vanishes
at the midpoint of its exact period:

`Ω̃(P / 2) = 0`.
@isnad1 id=eq.2h1v.s5.073ab9b0fb22 from=translated src=- shape=56061316 vocab=20e35567
-/
theorem nearestQOmegaTildeAt_halfPeriod_eq_zero
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQOmegaTildeAt q
        (nearestQExactPeriod q / 2) =
      0 := by
  let H :=
    nearestQEvenResidueHalfPeriod q
  have hperiod :
      nearestQExactPeriod q =
        2 * H := by
    dsimp [H]
    exact
      nearestQExactPeriod_eq_two_mul_halfPeriod
        q hq hqEven
  have hhalf :
      nearestQExactPeriod q / 2 =
        H := by
    omega
  have hHLe :
      H ≤ nearestQExactPeriod q := by
    omega
  have hant :
      nearestQOmegaTildeAt q
          (nearestQExactPeriod q - H) =
        -nearestQOmegaTildeAt q H :=
    nearestQOmegaTildeAt_period_sub_eq_neg
      q H hq hqEven hHLe
  have hsub :
      nearestQExactPeriod q - H =
        H := by
    omega
  rw [hsub] at hant
  rw [hhalf]
  linarith

/--
For even `q ≥ 6`, the normalized finite Fourier synthesis
inherits the antisymmetry of the periodic antiderivative.
@isnad1 id=eq.3h2v.s5.960859e77261 from=translated src=- shape=c3253fd8 vocab=e226f173
-/
theorem nearestQOmegaTildeFourierSeries_period_sub_eq_neg
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (ht :
      t ≤ nearestQExactPeriod q) :
    nearestQOmegaTildeFourierSeries q
        (nearestQExactPeriod q - t) =
      -nearestQOmegaTildeFourierSeries q t := by
  have hqPos :
      0 < q := by
    omega
  rw [
    nearestQOmegaTildeFourierSeries_eq_omegaTilde
      q
      (nearestQExactPeriod q - t)
      hqPos,
    nearestQOmegaTildeFourierSeries_eq_omegaTilde
      q t hqPos
  ]
  have hRat :
      nearestQOmegaTildeAt q
          (nearestQExactPeriod q - t) =
        -nearestQOmegaTildeAt q t :=
    nearestQOmegaTildeAt_period_sub_eq_neg
      q t hq hqEven ht
  have hComplex :=
    congrArg
      (fun x : Rat => (x : ℂ))
      hRat
  simpa using hComplex

/--
For even `q ≥ 6`, the normalized Fourier synthesis also
vanishes at the midpoint of the exact period.
@isnad1 id=eq.2h1v.s5.14c0e3eeebee from=translated src=- shape=56061316 vocab=50f12865
-/
theorem nearestQOmegaTildeFourierSeries_halfPeriod_eq_zero
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQOmegaTildeFourierSeries q
        (nearestQExactPeriod q / 2) =
      0 := by
  have hqPos :
      0 < q := by
    omega
  rw [
    nearestQOmegaTildeFourierSeries_eq_omegaTilde
      q
      (nearestQExactPeriod q / 2)
      hqPos
  ]
  rw [
    nearestQOmegaTildeAt_halfPeriod_eq_zero
      q hq hqEven
  ]
  norm_num

/--
For `q = 2`, the exact period is one, hence the periodic
antiderivative is identically zero.
@isnad1 id=eq.0h1v.s4.bcd7aaa30afb from=translated src=- shape=d7485c18 vocab=fc9d762b
-/
@[simp]
theorem nearestQOmegaTildeAt_two
    (t : Nat) :
    nearestQOmegaTildeAt 2 t = 0 := by
  unfold nearestQOmegaTildeAt
  norm_num [nearestQExactPeriod]

/--
For `q = 4`, the exact period is one, hence the periodic
antiderivative is identically zero.
@isnad1 id=eq.0h1v.s4.1c77952bb8e1 from=translated src=- shape=d7485c18 vocab=fc9d762b
-/
@[simp]
theorem nearestQOmegaTildeAt_four
    (t : Nat) :
    nearestQOmegaTildeAt 4 t = 0 := by
  unfold nearestQOmegaTildeAt
  norm_num [nearestQExactPeriod]

/--
For even `q ≥ 6`, the Fourier phase at the half-period
squares to one.
@isnad1 id=eq.2h1v.s5.520f42183233 from=translated src=- shape=23e77eca vocab=7536b5c1
-/
theorem nearestQFourierRoot_pow_halfPeriod_sq_eq_one
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (nearestQFourierRoot q ^
        nearestQEvenResidueHalfPeriod q) ^ 2 =
      1 := by
  have hqPos :
      0 < q := by
    omega
  have hperiod :
      nearestQExactPeriod q =
        2 * nearestQEvenResidueHalfPeriod q :=
    nearestQExactPeriod_eq_two_mul_halfPeriod
      q hq hqEven
  have hpow :
      nearestQFourierRoot q ^
          nearestQExactPeriod q =
        1 :=
    nearestQFourierRoot_pow_exactPeriod
      q hqPos
  calc
    (nearestQFourierRoot q ^
          nearestQEvenResidueHalfPeriod q) ^ 2 =
        nearestQFourierRoot q ^
          (nearestQEvenResidueHalfPeriod q * 2) := by
      rw [pow_mul]
    _ =
        nearestQFourierRoot q ^
          nearestQExactPeriod q := by
      congr 1
      omega
    _ = 1 := hpow

/--
For even `q ≥ 6`, the half-period Fourier phase is
nontrivial.
@isnad1 id=ne.2h1v.s5.44fd770f86b6 from=translated src=- shape=73c44624 vocab=7536b5c1
-/
theorem nearestQFourierRoot_pow_halfPeriod_ne_one
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQFourierRoot q ^
        nearestQEvenResidueHalfPeriod q ≠
      1 := by
  have hqPos :
      0 < q := by
    omega
  have hperiod :
      nearestQExactPeriod q =
        2 * nearestQEvenResidueHalfPeriod q :=
    nearestQExactPeriod_eq_two_mul_halfPeriod
      q hq hqEven
  have hperiodPos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos
      q hqPos
  have hhalfPos :
      0 < nearestQEvenResidueHalfPeriod q := by
    omega
  have hhalfLt :
      nearestQEvenResidueHalfPeriod q <
        nearestQExactPeriod q := by
    omega
  exact
    nearestQFourierRoot_pow_ne_one
      q
      (nearestQEvenResidueHalfPeriod q)
      hqPos
      hhalfPos
      hhalfLt

/--
For even `q ≥ 6`, the primitive Fourier root evaluated at
the half-period is exactly minus one:

`ζ_q^(P/2) = -1`.
@isnad1 id=eq.2h1v.s5.9d04db2a0365 from=translated src=- shape=51282771 vocab=7a3f3457
-/
theorem nearestQFourierRoot_pow_halfPeriod_eq_neg_one
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQFourierRoot q ^
        nearestQEvenResidueHalfPeriod q =
      (-1 : ℂ) := by
  let z : ℂ :=
    nearestQFourierRoot q ^
      nearestQEvenResidueHalfPeriod q
  have hsq :
      z ^ 2 = 1 := by
    dsimp [z]
    exact
      nearestQFourierRoot_pow_halfPeriod_sq_eq_one
        q hq hqEven
  have hne :
      z ≠ 1 := by
    dsimp [z]
    exact
      nearestQFourierRoot_pow_halfPeriod_ne_one
        q hq hqEven
  have hfactor :
      (z - 1) * (z + 1) = 0 := by
    calc
      (z - 1) * (z + 1) =
          z ^ 2 - 1 := by
        ring
      _ = 0 := by
        rw [hsq]
        ring
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · exfalso
    apply hne
    exact
      sub_eq_zero.mp hleft
  · have hz :
        z - (-1 : ℂ) = 0 := by
      simpa using hright
    exact
      sub_eq_zero.mp hz

/--
For even `q ≥ 6`, the inverse Fourier root evaluated at
the half-period is also minus one.
@isnad1 id=eq.2h1v.s5.be68328b6246 from=translated src=- shape=27c425af vocab=0cd7c26c
-/
theorem nearestQFourierRoot_inv_pow_halfPeriod_eq_neg_one
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    ((nearestQFourierRoot q)⁻¹) ^
        nearestQEvenResidueHalfPeriod q =
      (-1 : ℂ) := by
  rw [
    inv_pow,
    nearestQFourierRoot_pow_halfPeriod_eq_neg_one
      q hq hqEven
  ]
  norm_num

/--
At the Nyquist frequency, the shifted inverse Fourier phase
is simply the alternating sign `(-1)^(r+1)`.
@isnad1 id=eq.2h2v.s6.c239e14e9a71 from=translated src=- shape=74fda43f vocab=3b2b61a4
-/
theorem nearestQNyquistInverseShiftedPhase_eq
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    ((nearestQFourierRoot q)⁻¹) ^
        (nearestQEvenResidueHalfPeriod q * (r + 1)) =
      (-1 : ℂ) ^ (r + 1) := by
  rw [
    pow_mul,
    nearestQFourierRoot_inv_pow_halfPeriod_eq_neg_one
      q hq hqEven
  ]

/--
For even `q ≥ 6`, the Nyquist phases at two mirrored
indices have opposite signs.
@isnad1 id=eq.3h2v.s6.fd1ac1aca576 from=translated src=- shape=7047945f vocab=e1e03b32
-/
theorem nearestQNyquistPhase_mirror_eq_neg
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    (-1 : ℂ) ^
        (nearestQMirrorIndex q r + 1) =
      -((-1 : ℂ) ^ (r + 1)) := by
  have hperiod :
      nearestQExactPeriod q =
        2 * nearestQEvenResidueHalfPeriod q :=
    nearestQExactPeriod_eq_two_mul_halfPeriod
      q hq hqEven
  obtain ⟨k, hkEven | hkOdd⟩ :=
    Nat.even_or_odd' r
  · have hrOneOdd :
        Odd (r + 1) := by
      refine ⟨k, ?_⟩
      omega
    have hmirrorEven :
        Even
          (nearestQMirrorIndex q r + 1) := by
      refine
        ⟨nearestQEvenResidueHalfPeriod q - k, ?_⟩
      unfold nearestQMirrorIndex
      omega
    rw [
      hmirrorEven.neg_one_pow,
      hrOneOdd.neg_one_pow
    ]
    ring
  · have hrOneEven :
        Even (r + 1) := by
      refine ⟨k + 1, ?_⟩
      omega
    have hmirrorOdd :
        Odd
          (nearestQMirrorIndex q r + 1) := by
      refine
        ⟨nearestQEvenResidueHalfPeriod q - k - 1, ?_⟩
      unfold nearestQMirrorIndex
      omega
    rw [
      hmirrorOdd.neg_one_pow,
      hrOneEven.neg_one_pow
    ]

/--
The summand appearing in the centered Fourier coefficient
at the Nyquist frequency.-/
noncomputable def nearestQNyquistSummand
    (q r : Nat) : ℂ :=
  (nearestQCenteredOmegaAt q r : ℂ) *
    (-1 : ℂ) ^ (r + 1)

/--
For even `q ≥ 6`, mirrored Nyquist summands are negatives
of one another.
@isnad1 id=eq.3h2v.s5.48690e39f06b from=translated src=- shape=61dc4440 vocab=ffa184f6
-/
theorem nearestQNyquistSummand_mirror_eq_neg
    (q r : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQNyquistSummand q
        (nearestQMirrorIndex q r) =
      -nearestQNyquistSummand q r := by
  unfold nearestQNyquistSummand
  rw [
    nearestQCenteredOmegaAt_mirror_eq
      q r hq hqEven hr,
    nearestQNyquistPhase_mirror_eq_neg
      q r hq hqEven hr
  ]
  ring

/--
For even `q ≥ 6`, the complete sum of the Nyquist
summands over one exact period vanishes.
@isnad1 id=eq.2h1v.s5.db8a09d4bcd3 from=translated src=- shape=f6ca11c1 vocab=7ee009ba
-/
theorem nearestQNyquistSummand_sum_zero
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (nearestQNyquistSummand q) =
      0 := by
  let P :=
    nearestQExactPeriod q
  have hreindex :
      Finset.sum
          (Finset.range P)
          (nearestQNyquistSummand q) =
        Finset.sum
          (Finset.range P)
          (fun r =>
            nearestQNyquistSummand q
              (nearestQMirrorIndex q r)) := by
    refine
      Finset.sum_nbij'
        (nearestQMirrorIndex q)
        (nearestQMirrorIndex q)
        ?_
        ?_
        ?_
        ?_
        ?_
    · intro r hr
      apply Finset.mem_range.mpr
      exact
        nearestQMirrorIndex_lt_period
          q r hq
          (Finset.mem_range.mp hr)
    · intro r hr
      apply Finset.mem_range.mpr
      exact
        nearestQMirrorIndex_lt_period
          q r hq
          (Finset.mem_range.mp hr)
    · intro r hr
      exact
        nearestQMirrorIndex_involutive
          q r hq
          (Finset.mem_range.mp hr)
    · intro r hr
      exact
        nearestQMirrorIndex_involutive
          q r hq
          (Finset.mem_range.mp hr)
    · intro r hr
      rw [
        nearestQMirrorIndex_involutive
          q r hq
          (Finset.mem_range.mp hr)
      ]
  have hneg :
      Finset.sum
          (Finset.range P)
          (fun r =>
            nearestQNyquistSummand q
              (nearestQMirrorIndex q r)) =
        -Finset.sum
          (Finset.range P)
          (nearestQNyquistSummand q) := by
    calc
      Finset.sum
          (Finset.range P)
          (fun r =>
            nearestQNyquistSummand q
              (nearestQMirrorIndex q r)) =
        Finset.sum
          (Finset.range P)
          (fun r =>
            -nearestQNyquistSummand q r) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact
          nearestQNyquistSummand_mirror_eq_neg
            q r hq hqEven
            (Finset.mem_range.mp hr)
      _ =
        -Finset.sum
          (Finset.range P)
          (nearestQNyquistSummand q) := by
        rw [Finset.sum_neg_distrib]
  have hself :
      Finset.sum
          (Finset.range P)
          (nearestQNyquistSummand q) =
        -Finset.sum
          (Finset.range P)
          (nearestQNyquistSummand q) :=
    hreindex.trans hneg
  let S : ℂ :=
    Finset.sum
      (Finset.range P)
      (nearestQNyquistSummand q)
  have hself' :
      S = -S := by
    exact hself
  have hadd :
      S + S = 0 := by
    calc
      S + S =
          S + (-S) := by
        exact
          congrArg
            (fun z : ℂ => S + z)
            hself'
      _ = 0 := by
        ring
  have htwo :
      (2 : ℂ) * S = 0 := by
    calc
      (2 : ℂ) * S =
          S + S := by
        ring
      _ = 0 :=
        hadd
  have htwoNe :
      (2 : ℂ) ≠ 0 := by
    norm_num
  have hS :
      S = 0 :=
    (mul_eq_zero.mp htwo).resolve_left htwoNe
  exact hS

/--
For even `q ≥ 6`, the centered correction has vanishing
Nyquist Fourier coefficient.
@isnad1 id=eq.2h1v.s4.9a699625e82c from=translated src=- shape=3fcc48f3 vocab=71e9eaa0
-/
theorem nearestQCenteredOmegaFourierCoeff_halfPeriod_eq_zero
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQCenteredOmegaFourierCoeff
        q
        (nearestQEvenResidueHalfPeriod q) =
      0 := by
  unfold nearestQCenteredOmegaFourierCoeff
  have hsum :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQCenteredOmegaAt q r : ℂ) *
              ((nearestQFourierRoot q)⁻¹) ^
                (nearestQEvenResidueHalfPeriod q *
                  (r + 1))) =
        0 := by
    calc
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQCenteredOmegaAt q r : ℂ) *
              ((nearestQFourierRoot q)⁻¹) ^
                (nearestQEvenResidueHalfPeriod q *
                  (r + 1))) =
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (nearestQNyquistSummand q) := by
        apply Finset.sum_congr rfl
        intro r _hr
        unfold nearestQNyquistSummand
        rw [
          nearestQNyquistInverseShiftedPhase_eq
            q r hq hqEven
        ]
      _ = 0 :=
        nearestQNyquistSummand_sum_zero
          q hq hqEven
  rw [hsum]
  ring

/--
The complex conjugate of the Fourier root is its inverse.
@isnad1 id=eq.0h1v.s5.0434072ef173 from=translated src=- shape=60713059 vocab=e37d8e50
-/
theorem nearestQFourierRoot_conj_eq_inv
    (q : Nat) :
    (starRingEnd ℂ) (nearestQFourierRoot q) =
      (nearestQFourierRoot q)⁻¹ := by
  unfold nearestQFourierRoot
  rw [
    ← Complex.exp_conj,
    ← Complex.exp_neg
  ]
  congr 1
  simp [map_ofNat, neg_div]

/--
The conjugate of the inverse Fourier root is the original
Fourier root.
@isnad1 id=eq.0h1v.s5.dd6f2f44fab0 from=translated src=- shape=dee75a20 vocab=e37d8e50
-/
theorem nearestQFourierRoot_inv_conj_eq
    (q : Nat) :
    (starRingEnd ℂ)
        ((nearestQFourierRoot q)⁻¹) =
      nearestQFourierRoot q := by
  calc
    (starRingEnd ℂ)
        ((nearestQFourierRoot q)⁻¹) =
      ((starRingEnd ℂ)
        (nearestQFourierRoot q))⁻¹ := by
      simp
    _ =
      ((nearestQFourierRoot q)⁻¹)⁻¹ := by
      rw [
        nearestQFourierRoot_conj_eq_inv
      ]
    _ =
      nearestQFourierRoot q := by
      simp

/--
Conjugating an inverse Fourier phase produces the
corresponding positive Fourier phase.
@isnad1 id=eq.0h3v.s6.be74df61cf76 from=translated src=- shape=eab78487 vocab=f724cb04
-/
theorem nearestQFourierInversePhase_conj_eq
    (q ell m : Nat) :
    (starRingEnd ℂ)
        (((nearestQFourierRoot q)⁻¹) ^
          (ell * m)) =
      nearestQFourierRoot q ^
        (ell * m) := by
  rw [map_pow]
  rw [
    nearestQFourierRoot_inv_conj_eq
  ]

/--
The conjugate of a centered Fourier coefficient is obtained
by replacing every inverse Fourier phase by the corresponding
positive Fourier phase.
@isnad1 id=eq.0h2v.s7.22f3701bad23 from=translated src=- shape=2c55600c vocab=3d7804af
-/
theorem nearestQCenteredOmegaFourierCoeff_conj_eq_positive_sum
    (q ell : Nat) :
    (starRingEnd ℂ)
        (nearestQCenteredOmegaFourierCoeff q ell) =
      (1 / (nearestQExactPeriod q : ℂ)) *
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQCenteredOmegaAt q r : ℂ) *
              nearestQFourierRoot q ^
                (ell * (r + 1))) := by
  unfold nearestQCenteredOmegaFourierCoeff
  rw [map_mul]
  congr 1
  · simp
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [map_mul]
    congr 1
    · simp
    · exact
        nearestQFourierInversePhase_conj_eq
          q ell (r + 1)

/--
Modulo the exact Fourier period, the inverse phase at the
complementary frequency `P - ell` equals the positive phase
at frequency `ell`.
@isnad1 id=eq.2h3v.s6.cf19598fb9c3 from=translated src=- shape=b0aa07be vocab=4f5ea6fc
-/
theorem nearestQFourierComplementInversePhase_eq
    (q ell m : Nat)
    (hq : 0 < q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    ((nearestQFourierRoot q)⁻¹) ^
        ((nearestQExactPeriod q - ell) * m) =
      nearestQFourierRoot q ^ (ell * m) := by
  let z : ℂ :=
    nearestQFourierRoot q
  let P : Nat :=
    nearestQExactPeriod q
  have hzNe :
      z ≠ 0 := by
    dsimp [z]
    exact nearestQFourierRoot_ne_zero q
  have hsum :
      P - ell + ell = P := by
    dsimp [P]
    exact Nat.sub_add_cancel hellLe
  have hperiod :
      z ^ P = 1 := by
    dsimp [z, P]
    exact
      nearestQFourierRoot_pow_exactPeriod
        q hq
  have hprod :
      z ^ (P - ell) * z ^ ell = 1 := by
    calc
      z ^ (P - ell) * z ^ ell =
          z ^ ((P - ell) + ell) := by
        rw [← pow_add]
      _ = z ^ P := by
        rw [hsum]
      _ = 1 := hperiod
  have hcomp :
      z ^ (P - ell) =
        (z ^ ell)⁻¹ := by
    calc
      z ^ (P - ell) =
          z ^ (P - ell) *
            (z ^ ell * (z ^ ell)⁻¹) := by
        simp [hzNe]
      _ =
          (z ^ (P - ell) * z ^ ell) *
            (z ^ ell)⁻¹ := by
        ring
      _ =
          (z ^ ell)⁻¹ := by
        rw [hprod]
        simp
  calc
    z⁻¹ ^ ((P - ell) * m) =
        (z⁻¹ ^ (P - ell)) ^ m := by
      rw [pow_mul]
    _ =
        ((z ^ (P - ell))⁻¹) ^ m := by
      rw [inv_pow]
    _ =
        (((z ^ ell)⁻¹)⁻¹) ^ m := by
      rw [hcomp]
    _ =
        (z ^ ell) ^ m := by
      simp
    _ =
        z ^ (ell * m) := by
      rw [pow_mul]

/--
Fourier coefficients at complementary frequencies are
complex conjugates:

`â(P - ell) = conj (â ell)`.
@isnad1 id=eq.2h2v.s6.27709cb67150 from=translated src=- shape=bd3431a1 vocab=bdfbebdc
-/
theorem nearestQCenteredOmegaFourierCoeff_complement_eq_conj
    (q ell : Nat)
    (hq : 0 < q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaFourierCoeff
        q
        (nearestQExactPeriod q - ell) =
      (starRingEnd ℂ)
        (nearestQCenteredOmegaFourierCoeff q ell) := by
  calc
    nearestQCenteredOmegaFourierCoeff
        q
        (nearestQExactPeriod q - ell) =
      (1 / (nearestQExactPeriod q : ℂ)) *
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQCenteredOmegaAt q r : ℂ) *
              ((nearestQFourierRoot q)⁻¹) ^
                ((nearestQExactPeriod q - ell) *
                  (r + 1))) := by
      rfl
    _ =
      (1 / (nearestQExactPeriod q : ℂ)) *
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQCenteredOmegaAt q r : ℂ) *
              nearestQFourierRoot q ^
                (ell * (r + 1))) := by
      apply congrArg
        (fun z : ℂ =>
          (1 / (nearestQExactPeriod q : ℂ)) * z)
      apply Finset.sum_congr rfl
      intro r _hr
      congr 1
      exact
        nearestQFourierComplementInversePhase_eq
          q ell (r + 1) hq hellLe
    _ =
      (starRingEnd ℂ)
        (nearestQCenteredOmegaFourierCoeff q ell) := by
      symm
      exact
        nearestQCenteredOmegaFourierCoeff_conj_eq_positive_sum
          q ell

/--
For an index inside one exact period, the positive index
attached to its mirror is `P - r`.
@isnad1 id=eq.1h2v.s5.fbfc4638c0a2 from=translated src=- shape=d81abe3c vocab=ab1ec0c0
-/
theorem nearestQMirrorIndex_add_one_eq_period_sub
    (q r : Nat)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQMirrorIndex q r + 1 =
      nearestQExactPeriod q - r := by
  unfold nearestQMirrorIndex
  omega

/--
Every integer Fourier frequency accumulated over one exact
period gives unit phase.
@isnad1 id=eq.1h2v.s5.d4528cf72334 from=translated src=- shape=3f76ed41 vocab=9db6fdb8
-/
theorem nearestQFourierRoot_pow_frequency_mul_period
    (q ell : Nat)
    (hq : 0 < q) :
    nearestQFourierRoot q ^
        (ell * nearestQExactPeriod q) =
      1 := by
  rw [
    Nat.mul_comm
      ell
      (nearestQExactPeriod q),
    pow_mul,
    nearestQFourierRoot_pow_exactPeriod
      q hq,
    one_pow
  ]

/--
At a mirrored index, the positive Fourier phase equals
`ζ^ell` times the inverse phase at the original shifted
index.
@isnad1 id=eq.2h3v.s7.af4bf47dde93 from=translated src=- shape=6035d64b vocab=ee8acde8
-/
theorem nearestQFourierPositiveMirrorPhase_eq
    (q ell r : Nat)
    (hq : 0 < q)
    (hr :
      r < nearestQExactPeriod q) :
    nearestQFourierRoot q ^
        (ell * (nearestQMirrorIndex q r + 1)) =
      nearestQFourierRoot q ^ ell *
        ((nearestQFourierRoot q)⁻¹) ^
          (ell * (r + 1)) := by
  let z : ℂ :=
    nearestQFourierRoot q
  let P : Nat :=
    nearestQExactPeriod q
  have hzNe :
      z ≠ 0 := by
    dsimp [z]
    exact nearestQFourierRoot_ne_zero q
  have hmirror :
      nearestQMirrorIndex q r + 1 =
        P - r := by
    dsimp [P]
    exact
      nearestQMirrorIndex_add_one_eq_period_sub
        q r hr
  have hperiod :
      z ^ (ell * P) = 1 := by
    dsimp [z, P]
    exact
      nearestQFourierRoot_pow_frequency_mul_period
        q ell hq
  have hrLe :
      r ≤ P := by
    dsimp [P]
    omega
  have hsub :
      P - r + r = P :=
    Nat.sub_add_cancel hrLe
  have hsum :
      ell * (P - r) + ell * r =
        ell * P := by
    calc
      ell * (P - r) + ell * r =
          ell * ((P - r) + r) := by
        symm
        exact
          Nat.mul_add
            ell
            (P - r)
            r
      _ = ell * P := by
        rw [hsub]
  have hleft :
      z ^ (ell * (P - r)) =
        z⁻¹ ^ (ell * r) := by
    calc
      z ^ (ell * (P - r)) =
          z ^ (ell * (P - r)) *
            (z ^ (ell * r) *
              (z ^ (ell * r))⁻¹) := by
        simp [hzNe]
      _ =
          (z ^ (ell * (P - r)) *
              z ^ (ell * r)) *
            (z ^ (ell * r))⁻¹ := by
        ring
      _ =
          z ^ (ell * P) *
            (z ^ (ell * r))⁻¹ := by
        rw [← pow_add, hsum]
      _ =
          (z ^ (ell * r))⁻¹ := by
        rw [hperiod]
        simp
      _ =
          z⁻¹ ^ (ell * r) := by
        rw [inv_pow]
  have hright :
      z ^ ell *
          z⁻¹ ^ (ell * (r + 1)) =
        z⁻¹ ^ (ell * r) := by
    rw [
      Nat.mul_add,
      Nat.mul_one,
      pow_add
    ]
    calc
      z ^ ell *
          (z⁻¹ ^ (ell * r) *
            z⁻¹ ^ ell) =
        z⁻¹ ^ (ell * r) *
          (z ^ ell * z⁻¹ ^ ell) := by
        ring
      _ =
        z⁻¹ ^ (ell * r) := by
        simp [hzNe]
  rw [hmirror]
  change
    z ^ (ell * (P - r)) =
      z ^ ell *
        z⁻¹ ^ (ell * (r + 1))
  exact
    hleft.trans hright.symm

/--
For even `q ≥ 6`, the positive Fourier sum may be
reindexed by the mirror involution.
@isnad1 id=eq.2h2v.s7.cacff901a0c5 from=translated src=- shape=b1bc8eba vocab=11858013
-/
theorem nearestQCenteredOmegaPositiveFourierSum_mirror_eq
    (q ell : Nat)
    (hq : 6 ≤ q)
    (_hqEven : Even q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun r =>
          (nearestQCenteredOmegaAt q r : ℂ) *
            nearestQFourierRoot q ^
              (ell * (r + 1))) =
      Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun r =>
          (nearestQCenteredOmegaAt q
              (nearestQMirrorIndex q r) : ℂ) *
            nearestQFourierRoot q ^
              (ell *
                (nearestQMirrorIndex q r + 1))) := by
  refine
    Finset.sum_nbij'
      (nearestQMirrorIndex q)
      (nearestQMirrorIndex q)
      ?_
      ?_
      ?_
      ?_
      ?_
  · intro r hr
    apply Finset.mem_range.mpr
    exact
      nearestQMirrorIndex_lt_period
        q r hq
        (Finset.mem_range.mp hr)
  · intro r hr
    apply Finset.mem_range.mpr
    exact
      nearestQMirrorIndex_lt_period
        q r hq
        (Finset.mem_range.mp hr)
  · intro r hr
    exact
      nearestQMirrorIndex_involutive
        q r hq
        (Finset.mem_range.mp hr)
  · intro r hr
    exact
      nearestQMirrorIndex_involutive
        q r hq
        (Finset.mem_range.mp hr)
  · intro r hr
    rw [
      nearestQMirrorIndex_involutive
        q r hq
        (Finset.mem_range.mp hr)
    ]

/--
For even `q ≥ 6`, palindromicity imposes the phase relation

`conj(â ell) = ζ^ell * â ell`.
@isnad1 id=eq.2h2v.s6.5478e0430563 from=translated src=- shape=86d6b332 vocab=4e5786b5
-/
theorem nearestQCenteredOmegaFourierCoeff_conj_eq_root_mul
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (starRingEnd ℂ)
        (nearestQCenteredOmegaFourierCoeff q ell) =
      nearestQFourierRoot q ^ ell *
        nearestQCenteredOmegaFourierCoeff q ell := by
  have hqPos :
      0 < q := by
    omega
  rw [
    nearestQCenteredOmegaFourierCoeff_conj_eq_positive_sum
      q ell
  ]
  rw [
    nearestQCenteredOmegaPositiveFourierSum_mirror_eq
      q ell hq hqEven
  ]
  calc
    (1 / (nearestQExactPeriod q : ℂ)) *
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQCenteredOmegaAt q
                (nearestQMirrorIndex q r) : ℂ) *
              nearestQFourierRoot q ^
                (ell *
                  (nearestQMirrorIndex q r + 1))) =
      (1 / (nearestQExactPeriod q : ℂ)) *
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            nearestQFourierRoot q ^ ell *
              ((nearestQCenteredOmegaAt q r : ℂ) *
                ((nearestQFourierRoot q)⁻¹) ^
                  (ell * (r + 1)))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      have hrLt :
          r < nearestQExactPeriod q :=
        Finset.mem_range.mp hr
      rw [
        nearestQCenteredOmegaAt_mirror_eq
          q r hq hqEven hrLt,
        nearestQFourierPositiveMirrorPhase_eq
          q ell r hqPos hrLt
      ]
      ring
    _ =
      (1 / (nearestQExactPeriod q : ℂ)) *
        (nearestQFourierRoot q ^ ell *
          Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun r =>
              (nearestQCenteredOmegaAt q r : ℂ) *
                ((nearestQFourierRoot q)⁻¹) ^
                  (ell * (r + 1)))) := by
      congr 1
      rw [Finset.mul_sum]
    _ =
      nearestQFourierRoot q ^ ell *
        ((1 / (nearestQExactPeriod q : ℂ)) *
          Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun r =>
              (nearestQCenteredOmegaAt q r : ℂ) *
                ((nearestQFourierRoot q)⁻¹) ^
                  (ell * (r + 1)))) := by
      ring
    _ =
      nearestQFourierRoot q ^ ell *
        nearestQCenteredOmegaFourierCoeff q ell := by
      rfl

/--
For even `q ≥ 6`, the Fourier coefficient at the
complementary frequency is obtained by multiplying the
original coefficient by `ζ^ell`.
@isnad1 id=eq.3h2v.s6.0fd91f05fb22 from=translated src=- shape=df5251b8 vocab=d4ac2401
-/
theorem nearestQCenteredOmegaFourierCoeff_complement_eq_root_mul
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaFourierCoeff
        q
        (nearestQExactPeriod q - ell) =
      nearestQFourierRoot q ^ ell *
        nearestQCenteredOmegaFourierCoeff q ell := by
  have hqPos :
      0 < q := by
    omega
  rw [
    nearestQCenteredOmegaFourierCoeff_complement_eq_conj
      q ell hqPos hellLe,
    nearestQCenteredOmegaFourierCoeff_conj_eq_root_mul
      q ell hq hqEven
  ]

/--
The half Fourier root corresponds to the angle `π / P`.
Its square is the ordinary Fourier root.-/
noncomputable def nearestQFourierHalfRoot
    (q : Nat) : ℂ :=
  Complex.exp
    (((Real.pi : ℂ) * Complex.I) /
      (nearestQExactPeriod q : ℂ))

/--
@isnad1 id=eq.0h1v.s4.45a7cf1b0639 from=translated src=- shape=266a7c95 vocab=b3033db0
-/
theorem nearestQFourierHalfRoot_sq_eq_root
    (q : Nat) :
    nearestQFourierHalfRoot q ^ 2 =
      nearestQFourierRoot q := by
  unfold
    nearestQFourierHalfRoot
    nearestQFourierRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/--
The half Fourier root also lies on the unit circle:
its conjugate is its inverse.
@isnad1 id=eq.0h1v.s5.adcbc3a4f3a3 from=translated src=- shape=60713059 vocab=53eeb756
-/
theorem nearestQFourierHalfRoot_conj_eq_inv
    (q : Nat) :
    (starRingEnd ℂ)
        (nearestQFourierHalfRoot q) =
      (nearestQFourierHalfRoot q)⁻¹ := by
  unfold nearestQFourierHalfRoot
  rw [
    ← Complex.exp_conj,
    ← Complex.exp_neg
  ]
  congr 1
  simp [neg_div]

/--
The half phase belonging to frequency `ell`.-/
noncomputable def nearestQFourierHalfPhase
    (q ell : Nat) : ℂ :=
  nearestQFourierHalfRoot q ^ ell

/--
Squaring the half phase gives the ordinary Fourier phase.
@isnad1 id=eq.0h2v.s5.dad0720d5f38 from=translated src=- shape=1211c241 vocab=bbaab1a1
-/
theorem nearestQFourierHalfPhase_sq_eq
    (q ell : Nat) :
    nearestQFourierHalfPhase q ell ^ 2 =
      nearestQFourierRoot q ^ ell := by
  unfold nearestQFourierHalfPhase
  rw [← pow_mul]
  rw [Nat.mul_comm ell 2]
  rw [pow_mul]
  rw [
    nearestQFourierHalfRoot_sq_eq_root
      q
  ]

/--
The conjugate of every half Fourier phase is its inverse.
@isnad1 id=eq.0h2v.s5.a51330706531 from=translated src=- shape=1d68dde7 vocab=07cd1824
-/
theorem nearestQFourierHalfPhase_conj_eq_inv
    (q ell : Nat) :
    (starRingEnd ℂ)
        (nearestQFourierHalfPhase q ell) =
      (nearestQFourierHalfPhase q ell)⁻¹ := by
  unfold nearestQFourierHalfPhase
  rw [
    map_pow,
    nearestQFourierHalfRoot_conj_eq_inv,
    inv_pow
  ]

/--
The half Fourier root is nonzero.
@isnad1 id=ne.0h1v.s3.e8727ec5d875 from=translated src=- shape=a311c14d vocab=83d21e8b
-/
theorem nearestQFourierHalfRoot_ne_zero
    (q : Nat) :
    nearestQFourierHalfRoot q ≠ 0 := by
  unfold nearestQFourierHalfRoot
  exact Complex.exp_ne_zero _

/--
Every half Fourier phase is nonzero.
@isnad1 id=ne.0h2v.s3.1f00e90cc02b from=translated src=- shape=628a94f6 vocab=f53f2975
-/
theorem nearestQFourierHalfPhase_ne_zero
    (q ell : Nat) :
    nearestQFourierHalfPhase q ell ≠ 0 := by
  unfold nearestQFourierHalfPhase
  exact
    pow_ne_zero
      ell
      (nearestQFourierHalfRoot_ne_zero q)

/--
The Fourier coefficient with its half phase restored.
For even `q ≥ 6`, this quantity is real.-/
noncomputable def nearestQCenteredOmegaPhaseCorrectedCoeff
    (q ell : Nat) : ℂ :=
  nearestQFourierHalfPhase q ell *
    nearestQCenteredOmegaFourierCoeff q ell

/--
For even `q ≥ 6`, the phase-corrected Fourier coefficient
is fixed by complex conjugation, hence is real.
@isnad1 id=eq.2h2v.s5.fa3589a6463e from=translated src=- shape=9cf9010d vocab=fdae529e
-/
theorem nearestQCenteredOmegaPhaseCorrectedCoeff_conj_eq_self
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (starRingEnd ℂ)
        (nearestQCenteredOmegaPhaseCorrectedCoeff q ell) =
      nearestQCenteredOmegaPhaseCorrectedCoeff q ell := by
  unfold nearestQCenteredOmegaPhaseCorrectedCoeff
  rw [
    map_mul,
    nearestQFourierHalfPhase_conj_eq_inv,
    nearestQCenteredOmegaFourierCoeff_conj_eq_root_mul
      q ell hq hqEven,
    ← nearestQFourierHalfPhase_sq_eq
      q ell
  ]
  let h :=
    nearestQFourierHalfPhase q ell
  let a :=
    nearestQCenteredOmegaFourierCoeff q ell
  have hhNe :
      h ≠ 0 := by
    dsimp [h]
    exact
      nearestQFourierHalfPhase_ne_zero
        q ell
  change
    h⁻¹ * (h ^ 2 * a) =
      h * a
  calc
    h⁻¹ * (h ^ 2 * a) =
        (h⁻¹ * h) * (h * a) := by
      ring
    _ = h * a := by
      simp [hhNe]

/--
The real Fourier amplitude obtained after restoring the
half-frequency phase.-/
noncomputable def nearestQCenteredOmegaRealCoeff
    (q ell : Nat) : ℝ :=
  (nearestQCenteredOmegaPhaseCorrectedCoeff q ell).re

/--
For even `q ≥ 6`, the phase-corrected coefficient is exactly
the complex embedding of its real part.
@isnad1 id=eq.2h2v.s4.b41bfefef62c from=translated src=- shape=5bb29611 vocab=ab746c43
-/
theorem nearestQCenteredOmegaRealCoeff_coe_eq
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) =
      nearestQCenteredOmegaPhaseCorrectedCoeff q ell := by
  have hconj :
      (starRingEnd ℂ)
          (nearestQCenteredOmegaPhaseCorrectedCoeff q ell) =
        nearestQCenteredOmegaPhaseCorrectedCoeff q ell :=
    nearestQCenteredOmegaPhaseCorrectedCoeff_conj_eq_self
      q ell hq hqEven
  have him :
      (nearestQCenteredOmegaPhaseCorrectedCoeff q ell).im =
        0 := by
    have h :=
      congrArg Complex.im hconj
    simp at h
    linarith
  apply Complex.ext
  · simp [nearestQCenteredOmegaRealCoeff]
  · simp [
      nearestQCenteredOmegaRealCoeff,
      him
    ]

/--
For even `q ≥ 6`, every centered Fourier coefficient is a
real amplitude multiplied by the inverse half phase.
@isnad1 id=eq.2h2v.s5.f608ea25f4d5 from=translated src=- shape=e3eb8540 vocab=64d060a9
-/
theorem nearestQCenteredOmegaFourierCoeff_eq_halfPhase_inv_mul_realCoeff
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQCenteredOmegaFourierCoeff q ell =
      (nearestQFourierHalfPhase q ell)⁻¹ *
        ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) := by
  have hcoe :
      ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) =
        nearestQCenteredOmegaPhaseCorrectedCoeff q ell :=
    nearestQCenteredOmegaRealCoeff_coe_eq
      q ell hq hqEven
  unfold
    nearestQCenteredOmegaPhaseCorrectedCoeff
      at hcoe
  have hhNe :
      nearestQFourierHalfPhase q ell ≠ 0 :=
    nearestQFourierHalfPhase_ne_zero
      q ell
  calc
    nearestQCenteredOmegaFourierCoeff q ell =
        (nearestQFourierHalfPhase q ell)⁻¹ *
          (nearestQFourierHalfPhase q ell *
            nearestQCenteredOmegaFourierCoeff q ell) := by
      simp [hhNe]
    _ =
        (nearestQFourierHalfPhase q ell)⁻¹ *
          ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) := by
      rw [← hcoe]

/--
For even `q ≥ 6`, the complementary Fourier coefficient
uses the positive half phase and the same real amplitude.
@isnad1 id=eq.3h2v.s5.8257b94e05d4 from=translated src=- shape=e50fb75c vocab=396cabfd
-/
theorem nearestQCenteredOmegaFourierCoeff_complement_eq_halfPhase_mul_realCoeff
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaFourierCoeff
        q
        (nearestQExactPeriod q - ell) =
      nearestQFourierHalfPhase q ell *
        ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) := by
  rw [
    nearestQCenteredOmegaFourierCoeff_complement_eq_root_mul
      q ell hq hqEven hellLe,
    ← nearestQFourierHalfPhase_sq_eq
      q ell,
    nearestQCenteredOmegaFourierCoeff_eq_halfPhase_inv_mul_realCoeff
      q ell hq hqEven
  ]
  let h : ℂ :=
    nearestQFourierHalfPhase q ell
  let b : ℂ :=
    ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ)
  have hhNe :
      h ≠ 0 := by
    dsimp [h]
    exact
      nearestQFourierHalfPhase_ne_zero
        q ell
  change
    h ^ 2 * (h⁻¹ * b) =
      h * b
  calc
    h ^ 2 * (h⁻¹ * b) =
        (h⁻¹ * h) * (h * b) := by
      ring
    _ = h * b := by
      simp [hhNe]

/--
Modulo the exact Fourier period, the positive phase at the
complementary frequency equals the inverse phase at the
original frequency.
@isnad1 id=eq.2h3v.s6.676c1529eea6 from=translated src=- shape=c8e87f27 vocab=4f5ea6fc
-/
theorem nearestQFourierComplementPositivePhase_eq
    (q ell m : Nat)
    (hq : 0 < q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQFourierRoot q ^
        ((nearestQExactPeriod q - ell) * m) =
      ((nearestQFourierRoot q)⁻¹) ^
        (ell * m) := by
  have h :=
    congrArg
      (starRingEnd ℂ)
      (nearestQFourierComplementInversePhase_eq
        q ell m hq hellLe)
  simpa only [
    map_pow,
    nearestQFourierRoot_inv_conj_eq,
    nearestQFourierRoot_conj_eq_inv
  ] using h

/--
The paired contribution of the complementary Fourier
frequencies `ell` and `P - ell`.-/
noncomputable def nearestQCenteredOmegaFourierPairTerm
    (q ell t : Nat) : ℂ :=
  nearestQCenteredOmegaFourierCoeff q ell *
      nearestQFourierRoot q ^
        (ell * (t + 1)) +
    nearestQCenteredOmegaFourierCoeff
        q
        (nearestQExactPeriod q - ell) *
      nearestQFourierRoot q ^
        ((nearestQExactPeriod q - ell) *
          (t + 1))

/--
For even `q ≥ 6`, the paired Fourier contribution is
expressed using one real amplitude and the two opposite
half-phase directions.
@isnad1 id=eq.3h3v.s7.cc10ed8ef39b from=translated src=- shape=0519b435 vocab=356ffcf5
-/
theorem nearestQCenteredOmegaFourierPairTerm_eq_halfPhase
    (q ell t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaFourierPairTerm q ell t =
      ((nearestQFourierHalfPhase q ell)⁻¹ *
          ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ)) *
        nearestQFourierRoot q ^
          (ell * (t + 1)) +
      (nearestQFourierHalfPhase q ell *
          ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ)) *
        ((nearestQFourierRoot q)⁻¹) ^
          (ell * (t + 1)) := by
  have hqPos :
      0 < q := by
    omega
  unfold nearestQCenteredOmegaFourierPairTerm
  rw [
    nearestQCenteredOmegaFourierCoeff_eq_halfPhase_inv_mul_realCoeff
      q ell hq hqEven,
    nearestQCenteredOmegaFourierCoeff_complement_eq_halfPhase_mul_realCoeff
      q ell hq hqEven hellLe,
    nearestQFourierComplementPositivePhase_eq
      q ell (t + 1) hqPos hellLe
  ]

/--
The positive-frequency phase together with the inverse
half-phase collapses to the odd half-phase power
`h^(2*t+1)`.
@isnad1 id=eq.0h3v.s6.5c84d6684d99 from=translated src=- shape=565ba85d vocab=e85ad178
-/
theorem nearestQFourierHalfPhase_inv_mul_positivePhase_eq
    (q ell t : Nat) :
    (nearestQFourierHalfPhase q ell)⁻¹ *
        nearestQFourierRoot q ^
          (ell * (t + 1)) =
      nearestQFourierHalfPhase q ell ^
        (2 * t + 1) := by
  let h : ℂ :=
    nearestQFourierHalfPhase q ell
  let z : ℂ :=
    nearestQFourierRoot q
  have hhNe :
      h ≠ 0 := by
    dsimp [h]
    exact
      nearestQFourierHalfPhase_ne_zero
        q ell
  have hsq :
      h ^ 2 = z ^ ell := by
    dsimp [h, z]
    exact
      nearestQFourierHalfPhase_sq_eq
        q ell
  have hexp :
      2 * (t + 1) =
        (2 * t + 1) + 1 := by
    omega
  calc
    h⁻¹ * z ^ (ell * (t + 1)) =
        h⁻¹ * (z ^ ell) ^ (t + 1) := by
      rw [pow_mul]
    _ =
        h⁻¹ * (h ^ 2) ^ (t + 1) := by
      rw [← hsq]
    _ =
        h⁻¹ * h ^ (2 * (t + 1)) := by
      rw [← pow_mul]
    _ =
        h⁻¹ * h ^ ((2 * t + 1) + 1) := by
      rw [hexp]
    _ =
        h⁻¹ *
          (h ^ (2 * t + 1) * h) := by
      rw [pow_succ]
    _ =
        (h⁻¹ * h) *
          h ^ (2 * t + 1) := by
      ring
    _ =
        h ^ (2 * t + 1) := by
      simp [hhNe]

/--
The negative-frequency phase together with the positive
half-phase collapses to the opposite odd half-phase power.
@isnad1 id=eq.0h3v.s6.ad6f759d7572 from=translated src=- shape=9b479c58 vocab=e85ad178
-/
theorem nearestQFourierHalfPhase_mul_inversePositivePhase_eq
    (q ell t : Nat) :
    nearestQFourierHalfPhase q ell *
        ((nearestQFourierRoot q)⁻¹) ^
          (ell * (t + 1)) =
      ((nearestQFourierHalfPhase q ell)⁻¹) ^
        (2 * t + 1) := by
  let h : ℂ :=
    nearestQFourierHalfPhase q ell
  let z : ℂ :=
    nearestQFourierRoot q
  have hhNe :
      h ≠ 0 := by
    dsimp [h]
    exact
      nearestQFourierHalfPhase_ne_zero
        q ell
  have hsq :
      h ^ 2 = z ^ ell := by
    dsimp [h, z]
    exact
      nearestQFourierHalfPhase_sq_eq
        q ell
  have hsqInv :
      h⁻¹ ^ 2 = z⁻¹ ^ ell := by
    calc
      h⁻¹ ^ 2 =
          (h ^ 2)⁻¹ := by
        rw [inv_pow]
      _ =
          (z ^ ell)⁻¹ := by
        rw [hsq]
      _ =
          z⁻¹ ^ ell := by
        rw [inv_pow]
  have hexp :
      2 * (t + 1) =
        (2 * t + 1) + 1 := by
    omega
  calc
    h * z⁻¹ ^ (ell * (t + 1)) =
        h * (z⁻¹ ^ ell) ^ (t + 1) := by
      rw [pow_mul]
    _ =
        h * (h⁻¹ ^ 2) ^ (t + 1) := by
      rw [← hsqInv]
    _ =
        h * h⁻¹ ^ (2 * (t + 1)) := by
      rw [← pow_mul]
    _ =
        h * h⁻¹ ^ ((2 * t + 1) + 1) := by
      rw [hexp]
    _ =
        h *
          (h⁻¹ ^ (2 * t + 1) * h⁻¹) := by
      rw [pow_succ]
    _ =
        (h * h⁻¹) *
          h⁻¹ ^ (2 * t + 1) := by
      ring
    _ =
        h⁻¹ ^ (2 * t + 1) := by
      simp [hhNe]

/--
For even `q ≥ 6`, a complementary Fourier pair is one real
amplitude times the sum of the two opposite odd half-phases.
@isnad1 id=eq.3h3v.s7.e385b64b7c80 from=translated src=- shape=0bdd8939 vocab=2edf95e1
-/
theorem nearestQCenteredOmegaFourierPairTerm_eq_realCoeff_mul_halfPhaseSum
    (q ell t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaFourierPairTerm q ell t =
      ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) *
        (nearestQFourierHalfPhase q ell ^
            (2 * t + 1) +
          ((nearestQFourierHalfPhase q ell)⁻¹) ^
            (2 * t + 1)) := by
  rw [
    nearestQCenteredOmegaFourierPairTerm_eq_halfPhase
      q ell t hq hqEven hellLe
  ]
  calc
    ((nearestQFourierHalfPhase q ell)⁻¹ *
          ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ)) *
          nearestQFourierRoot q ^
            (ell * (t + 1)) +
        (nearestQFourierHalfPhase q ell *
          ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ)) *
          ((nearestQFourierRoot q)⁻¹) ^
            (ell * (t + 1)) =
      ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) *
        (((nearestQFourierHalfPhase q ell)⁻¹ *
            nearestQFourierRoot q ^
              (ell * (t + 1))) +
          (nearestQFourierHalfPhase q ell *
            ((nearestQFourierRoot q)⁻¹) ^
              (ell * (t + 1)))) := by
      ring
    _ =
      ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) *
        (nearestQFourierHalfPhase q ell ^
            (2 * t + 1) +
          ((nearestQFourierHalfPhase q ell)⁻¹) ^
            (2 * t + 1)) := by
      rw [
        nearestQFourierHalfPhase_inv_mul_positivePhase_eq,
        nearestQFourierHalfPhase_mul_inversePositivePhase_eq
      ]

/--
The algebraic cosine kernel associated with frequency `ell`.
It is the sum of the two opposite odd half-phases.-/
noncomputable def nearestQCenteredOmegaCosineKernel
    (q ell t : Nat) : ℂ :=
  nearestQFourierHalfPhase q ell ^
      (2 * t + 1) +
    ((nearestQFourierHalfPhase q ell)⁻¹) ^
      (2 * t + 1)

/--
Every complementary Fourier pair is a real amplitude
multiplied by its algebraic cosine kernel.
@isnad1 id=eq.3h3v.s5.b689b24c6447 from=translated src=- shape=ded3c76d vocab=08d61fe1
-/
theorem nearestQCenteredOmegaFourierPairTerm_eq_realCoeff_mul_cosineKernel
    (q ell t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaFourierPairTerm q ell t =
      ((nearestQCenteredOmegaRealCoeff q ell : ℝ) : ℂ) *
        nearestQCenteredOmegaCosineKernel
          q ell t := by
  unfold nearestQCenteredOmegaCosineKernel
  exact
    nearestQCenteredOmegaFourierPairTerm_eq_realCoeff_mul_halfPhaseSum
      q ell t hq hqEven hellLe

/--
The real angle associated with the paired Fourier mode.-/
noncomputable def nearestQCenteredOmegaCosineAngle
    (q ell t : Nat) : ℝ :=
  (((2 * t + 1 : Nat) : ℝ) *
      (ell : ℝ) * Real.pi) /
    (nearestQExactPeriod q : ℝ)

/--
The complex embedding of the real cosine angle.
@isnad1 id=eq.0h3v.s6.4cf3556d595c from=translated src=- shape=f2c4ba2b vocab=97484a86
-/
theorem nearestQCenteredOmegaCosineAngle_coe
    (q ell t : Nat) :
    ((nearestQCenteredOmegaCosineAngle q ell t : ℝ) : ℂ) =
      (((2 * t + 1 : Nat) : ℂ) *
          (ell : ℂ) * (Real.pi : ℂ)) /
        (nearestQExactPeriod q : ℂ) := by
  simp [nearestQCenteredOmegaCosineAngle]

/--
The positive odd half-phase is the complex exponential
of the corresponding real angle.
@isnad1 id=eq.0h3v.s6.6dcb79c31698 from=translated src=- shape=56a56da1 vocab=b0e3eda2
-/
theorem nearestQFourierHalfPhase_oddPow_eq_exp_angle
    (q ell t : Nat) :
    nearestQFourierHalfPhase q ell ^
        (2 * t + 1) =
      Complex.exp
        (((nearestQCenteredOmegaCosineAngle
            q ell t : ℝ) : ℂ) * Complex.I) := by
  unfold
    nearestQFourierHalfPhase
    nearestQFourierHalfRoot
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_nat_mul]
  rw [
    nearestQCenteredOmegaCosineAngle_coe
      q ell t
  ]
  congr 1
  ring

/--
The opposite odd half-phase is the complex exponential
of the negative real angle.
@isnad1 id=eq.0h3v.s6.57d8595b2b3f from=translated src=- shape=641836d5 vocab=7df33b21
-/
theorem nearestQFourierHalfPhase_inv_oddPow_eq_exp_neg_angle
    (q ell t : Nat) :
    ((nearestQFourierHalfPhase q ell)⁻¹) ^
        (2 * t + 1) =
      Complex.exp
        (-((nearestQCenteredOmegaCosineAngle
              q ell t : ℝ) : ℂ) * Complex.I) := by
  rw [inv_pow]
  rw [
    nearestQFourierHalfPhase_oddPow_eq_exp_angle
      q ell t
  ]
  rw [← Complex.exp_neg]
  congr 1
  ring

/--
The algebraic cosine kernel is exactly twice the complex
cosine of its real Fourier angle.
@isnad1 id=eq.0h3v.s5.d861590c0d91 from=translated src=- shape=ff21732a vocab=ceb50916
-/
theorem nearestQCenteredOmegaCosineKernel_eq_two_mul_cos
    (q ell t : Nat) :
    nearestQCenteredOmegaCosineKernel q ell t =
      (2 : ℂ) *
        Complex.cos
          ((nearestQCenteredOmegaCosineAngle
              q ell t : ℝ) : ℂ) := by
  unfold nearestQCenteredOmegaCosineKernel
  rw [
    nearestQFourierHalfPhase_oddPow_eq_exp_angle
      q ell t,
    nearestQFourierHalfPhase_inv_oddPow_eq_exp_neg_angle
      q ell t
  ]
  exact
    (Complex.two_cos
      ((nearestQCenteredOmegaCosineAngle
          q ell t : ℝ) : ℂ)).symm

/--
The algebraic cosine kernel is the complex embedding of
twice the corresponding real cosine.
@isnad1 id=eq.0h3v.s5.98d0c3943a54 from=translated src=- shape=e33850d7 vocab=15e91d15
-/
theorem nearestQCenteredOmegaCosineKernel_eq_realCos
    (q ell t : Nat) :
    nearestQCenteredOmegaCosineKernel q ell t =
      (((2 : ℝ) *
          Real.cos
            (nearestQCenteredOmegaCosineAngle
              q ell t) : ℝ) : ℂ) := by
  rw [
    nearestQCenteredOmegaCosineKernel_eq_two_mul_cos
      q ell t
  ]
  calc
    (2 : ℂ) *
        Complex.cos
          ((nearestQCenteredOmegaCosineAngle
              q ell t : ℝ) : ℂ) =
      (2 : ℂ) *
        ((Real.cos
          (nearestQCenteredOmegaCosineAngle
            q ell t) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos]
    _ =
      (((2 : ℝ) *
          Real.cos
            (nearestQCenteredOmegaCosineAngle
              q ell t) : ℝ) : ℂ) := by
      norm_num

/--
For even `q ≥ 6`, a complementary Fourier pair is exactly
the complex embedding of a real cosine mode.
@isnad1 id=eq.3h3v.s6.93073343e296 from=translated src=- shape=ccb3bbbc vocab=85e6aca8
-/
theorem nearestQCenteredOmegaFourierPairTerm_eq_realCos
    (q ell t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    nearestQCenteredOmegaFourierPairTerm q ell t =
      (((2 : ℝ) *
          nearestQCenteredOmegaRealCoeff q ell *
          Real.cos
            (nearestQCenteredOmegaCosineAngle
              q ell t) : ℝ) : ℂ) := by
  rw [
    nearestQCenteredOmegaFourierPairTerm_eq_realCoeff_mul_cosineKernel
      q ell t hq hqEven hellLe,
    nearestQCenteredOmegaCosineKernel_eq_realCos
      q ell t
  ]
  push_cast
  ring

/--
The real cosine contribution associated with one
complementary pair of Fourier frequencies.-/
noncomputable def nearestQCenteredOmegaRealFourierPairTerm
    (q ell t : Nat) : ℝ :=
  2 *
    nearestQCenteredOmegaRealCoeff q ell *
    Real.cos
      (nearestQCenteredOmegaCosineAngle
        q ell t)

/--
The complex Fourier pair is precisely the embedding of its
real cosine contribution.
@isnad1 id=eq.3h3v.s5.5c6176278a56 from=translated src=- shape=4c2a291c vocab=a65ceb69
-/
theorem nearestQCenteredOmegaRealFourierPairTerm_coe_eq
    (q ell t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hellLe :
      ell ≤ nearestQExactPeriod q) :
    ((nearestQCenteredOmegaRealFourierPairTerm
        q ell t : ℝ) : ℂ) =
      nearestQCenteredOmegaFourierPairTerm
        q ell t := by
  unfold nearestQCenteredOmegaRealFourierPairTerm
  symm
  exact
    nearestQCenteredOmegaFourierPairTerm_eq_realCos
      q ell t hq hqEven hellLe

/--
The nonzero frequencies strictly below the midpoint.-/
def nearestQLowerFourierFrequencies
    (q : Nat) : Finset Nat :=
  Finset.Ico
    1
    (nearestQEvenResidueHalfPeriod q)

/--
The frequencies strictly above the midpoint and below the
exact period.-/
def nearestQUpperFourierFrequencies
    (q : Nat) : Finset Nat :=
  Finset.Ioo
    (nearestQEvenResidueHalfPeriod q)
    (nearestQExactPeriod q)

/--
For even `q ≥ 6`, the complete nonzero Fourier range splits
into the lower frequencies, the midpoint, and the upper
frequencies.
@isnad1 id=eq.2h1v.s5.3f8f2ebbbbb3 from=translated src=- shape=f6689a02 vocab=54ff9a57
-/
theorem nearestQNonzeroFourierFrequencies_eq_lower_mid_upper
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.Ico
        1
        (nearestQExactPeriod q) =
      nearestQLowerFourierFrequencies q ∪
        (({nearestQEvenResidueHalfPeriod q} : Finset Nat) ∪
          nearestQUpperFourierFrequencies q) := by
  have hqPos :
      0 < q := by
    omega
  have hperiodPos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos q hqPos
  have hperiod :
      nearestQExactPeriod q =
        2 * nearestQEvenResidueHalfPeriod q :=
    nearestQExactPeriod_eq_two_mul_halfPeriod
      q hq hqEven
  have hhalfPos :
      0 < nearestQEvenResidueHalfPeriod q := by
    rw [hperiod] at hperiodPos
    omega
  ext ell
  simp only [
    nearestQLowerFourierFrequencies,
    nearestQUpperFourierFrequencies,
    Finset.mem_Ico,
    Finset.mem_Ioo,
    Finset.mem_union,
    Finset.mem_singleton
  ]
  rw [hperiod]
  omega

/--
For even `q ≥ 6`, complementing a lower frequency by
`ell ↦ P - ell` produces an upper frequency.
@isnad1 id=mem.3h2v.s5.518585c355a9 from=translated src=- shape=90c48615 vocab=be7dbf98
-/
theorem nearestQFrequencyComplement_mem_upper
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hell :
      ell ∈ nearestQLowerFourierFrequencies q) :
    nearestQExactPeriod q - ell ∈
      nearestQUpperFourierFrequencies q := by
  have hperiod :
      nearestQExactPeriod q =
        2 * nearestQEvenResidueHalfPeriod q :=
    nearestQExactPeriod_eq_two_mul_halfPeriod
      q hq hqEven
  have hellBounds :
      1 ≤ ell ∧
        ell < nearestQEvenResidueHalfPeriod q := by
    simpa only [
      nearestQLowerFourierFrequencies,
      Finset.mem_Ico
    ] using hell
  simp only [
    nearestQUpperFourierFrequencies,
    Finset.mem_Ioo
  ]
  rw [hperiod]
  omega

/--
For even `q ≥ 6`, complementing an upper frequency produces
a lower frequency.
@isnad1 id=mem.3h2v.s5.2e19024000fb from=translated src=- shape=90c48615 vocab=be7dbf98
-/
theorem nearestQFrequencyComplement_mem_lower
    (q ell : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hell :
      ell ∈ nearestQUpperFourierFrequencies q) :
    nearestQExactPeriod q - ell ∈
      nearestQLowerFourierFrequencies q := by
  have hperiod :
      nearestQExactPeriod q =
        2 * nearestQEvenResidueHalfPeriod q :=
    nearestQExactPeriod_eq_two_mul_halfPeriod
      q hq hqEven
  have hellBounds :
      nearestQEvenResidueHalfPeriod q < ell ∧
        ell < nearestQExactPeriod q := by
    simpa only [
      nearestQUpperFourierFrequencies,
      Finset.mem_Ioo
    ] using hell
  simp only [
    nearestQLowerFourierFrequencies,
    Finset.mem_Ico
  ]
  rw [hperiod] at hellBounds ⊢
  omega

/--
Complementation inside one exact period is an involution.
@isnad1 id=eq.1h2v.s5.6aafb935a6f7 from=translated src=- shape=f4a6bba0 vocab=9e99791c
-/
theorem nearestQFrequencyComplement_involutive
    (q ell : Nat)
    (hell :
      ell < nearestQExactPeriod q) :
    nearestQExactPeriod q -
        (nearestQExactPeriod q - ell) =
      ell := by
  omega

/--
For even `q ≥ 6`, the Fourier sum over the upper half of
the spectrum can be reindexed by complementary frequencies
from the lower half.
@isnad1 id=eq.2h2v.s7.184ead1073cd from=translated src=- shape=dd18a06f vocab=9740be2a
-/
theorem nearestQUpperFourierSum_eq_complementLowerSum
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (nearestQUpperFourierFrequencies q)
        (fun ell =>
          nearestQCenteredOmegaFourierCoeff q ell *
            nearestQFourierRoot q ^
              (ell * (t + 1))) =
      Finset.sum
        (nearestQLowerFourierFrequencies q)
        (fun ell =>
          nearestQCenteredOmegaFourierCoeff
              q
              (nearestQExactPeriod q - ell) *
            nearestQFourierRoot q ^
              ((nearestQExactPeriod q - ell) *
                (t + 1))) := by
  refine
    Finset.sum_nbij'
      (fun ell =>
        nearestQExactPeriod q - ell)
      (fun ell =>
        nearestQExactPeriod q - ell)
      ?_
      ?_
      ?_
      ?_
      ?_
  · intro ell hell
    exact
      nearestQFrequencyComplement_mem_lower
        q ell hq hqEven hell
  · intro ell hell
    exact
      nearestQFrequencyComplement_mem_upper
        q ell hq hqEven hell
  · intro ell hell
    have hellBounds :
        nearestQEvenResidueHalfPeriod q < ell ∧
          ell < nearestQExactPeriod q := by
      simpa only [
        nearestQUpperFourierFrequencies,
        Finset.mem_Ioo
      ] using hell
    exact
      nearestQFrequencyComplement_involutive
        q ell hellBounds.2
  · intro ell hell
    have hperiod :
        nearestQExactPeriod q =
          2 * nearestQEvenResidueHalfPeriod q :=
      nearestQExactPeriod_eq_two_mul_halfPeriod
        q hq hqEven
    have hellBounds :
        1 ≤ ell ∧
          ell < nearestQEvenResidueHalfPeriod q := by
      simpa only [
        nearestQLowerFourierFrequencies,
        Finset.mem_Ico
      ] using hell
    have hellPeriod :
        ell < nearestQExactPeriod q := by
      rw [hperiod]
      omega
    exact
      nearestQFrequencyComplement_involutive
        q ell hellPeriod
  · intro ell hell
    have hellBounds :
        nearestQEvenResidueHalfPeriod q < ell ∧
          ell < nearestQExactPeriod q := by
      simpa only [
        nearestQUpperFourierFrequencies,
        Finset.mem_Ioo
      ] using hell
    rw [
      nearestQFrequencyComplement_involutive
        q ell hellBounds.2
    ]

/--
For even `q ≥ 6`, adding the lower and upper halves of the
Fourier spectrum is exactly the sum of complementary
Fourier pair terms.
@isnad1 id=eq.2h2v.s7.b597161868e1 from=translated src=- shape=b33fbb82 vocab=e8e6e200
-/
theorem nearestQLower_add_upperFourierSum_eq_pairSum
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (nearestQLowerFourierFrequencies q)
        (fun ell =>
          nearestQCenteredOmegaFourierCoeff q ell *
            nearestQFourierRoot q ^
              (ell * (t + 1))) +
      Finset.sum
        (nearestQUpperFourierFrequencies q)
        (fun ell =>
          nearestQCenteredOmegaFourierCoeff q ell *
            nearestQFourierRoot q ^
              (ell * (t + 1))) =
      Finset.sum
        (nearestQLowerFourierFrequencies q)
        (fun ell =>
          nearestQCenteredOmegaFourierPairTerm
            q ell t) := by
  rw [
    nearestQUpperFourierSum_eq_complementLowerSum
      q t hq hqEven
  ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _hell
  unfold nearestQCenteredOmegaFourierPairTerm
  rfl

/--
For even `q ≥ 6`, the complete nonzero Fourier spectrum is
the sum of its complementary frequency pairs; the midpoint
term vanishes.
@isnad1 id=eq.2h2v.s6.d07542a27c47 from=translated src=- shape=86255f46 vocab=3d9bcff6
-/
theorem nearestQNonzeroFourierSum_eq_pairSum
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (Finset.Ico
          1
          (nearestQExactPeriod q))
        (fun ell =>
          nearestQCenteredOmegaFourierCoeff q ell *
            nearestQFourierRoot q ^
              (ell * (t + 1))) =
      Finset.sum
        (nearestQLowerFourierFrequencies q)
        (fun ell =>
          nearestQCenteredOmegaFourierPairTerm
            q ell t) := by
  have hLowerDisj :
      Disjoint
        (nearestQLowerFourierFrequencies q)
        (({nearestQEvenResidueHalfPeriod q} : Finset Nat) ∪
          nearestQUpperFourierFrequencies q) := by
    apply Finset.disjoint_left.mpr
    intro ell hLower hRest
    have hLowerBounds :
        1 ≤ ell ∧
          ell < nearestQEvenResidueHalfPeriod q := by
      simpa only [
        nearestQLowerFourierFrequencies,
        Finset.mem_Ico
      ] using hLower
    simp only [
      Finset.mem_union,
      Finset.mem_singleton
    ] at hRest
    rcases hRest with hMid | hUpper
    · omega
    · have hUpperBounds :
          nearestQEvenResidueHalfPeriod q < ell ∧
            ell < nearestQExactPeriod q := by
        simpa only [
          nearestQUpperFourierFrequencies,
          Finset.mem_Ioo
        ] using hUpper
      omega
  have hMidUpperDisj :
      Disjoint
        ({nearestQEvenResidueHalfPeriod q} : Finset Nat)
        (nearestQUpperFourierFrequencies q) := by
    apply Finset.disjoint_left.mpr
    intro ell hMid hUpper
    have hMidEq :
        ell = nearestQEvenResidueHalfPeriod q := by
      simpa only [
        Finset.mem_singleton
      ] using hMid
    have hUpperBounds :
        nearestQEvenResidueHalfPeriod q < ell ∧
          ell < nearestQExactPeriod q := by
      simpa only [
        nearestQUpperFourierFrequencies,
        Finset.mem_Ioo
      ] using hUpper
    omega
  rw [
    nearestQNonzeroFourierFrequencies_eq_lower_mid_upper
      q hq hqEven,
    Finset.sum_union hLowerDisj,
    Finset.sum_union hMidUpperDisj,
    Finset.sum_singleton,
    nearestQCenteredOmegaFourierCoeff_halfPeriod_eq_zero
      q hq hqEven
  ]
  simpa only [
    zero_mul,
    zero_add
  ] using
    nearestQLower_add_upperFourierSum_eq_pairSum
      q t hq hqEven

/--
For even `q ≥ 6`, the complete nonzero Fourier sum is the
complex embedding of a finite sum of real cosine modes.
@isnad1 id=eq.2h2v.s6.b47553a39af5 from=translated src=- shape=dde0af6a vocab=2ad34bf0
-/
theorem nearestQNonzeroFourierSum_eq_realCosineSum
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (Finset.Ico
          1
          (nearestQExactPeriod q))
        (fun ell =>
          nearestQCenteredOmegaFourierCoeff q ell *
            nearestQFourierRoot q ^
              (ell * (t + 1))) =
      ((Finset.sum
          (nearestQLowerFourierFrequencies q)
          (fun ell =>
            nearestQCenteredOmegaRealFourierPairTerm
              q ell t) : ℝ) : ℂ) := by
  rw [
    nearestQNonzeroFourierSum_eq_pairSum
      q t hq hqEven
  ]
  push_cast
  apply Finset.sum_congr rfl
  intro ell hell
  have hellBounds :
      1 ≤ ell ∧
        ell < nearestQEvenResidueHalfPeriod q := by
    simpa only [
      nearestQLowerFourierFrequencies,
      Finset.mem_Ico
    ] using hell
  have hperiod :
      nearestQExactPeriod q =
        2 * nearestQEvenResidueHalfPeriod q :=
    nearestQExactPeriod_eq_two_mul_halfPeriod
      q hq hqEven
  have hellLe :
      ell ≤ nearestQExactPeriod q := by
    rw [hperiod]
    omega
  symm
  exact
    nearestQCenteredOmegaRealFourierPairTerm_coe_eq
      q ell t hq hqEven hellLe

/--
The finite real cosine expansion of the centered correction.-/
noncomputable def nearestQCenteredOmegaRealCosineSeries
    (q t : Nat) : ℝ :=
  Finset.sum
    (nearestQLowerFourierFrequencies q)
    (fun ell =>
      nearestQCenteredOmegaRealFourierPairTerm
        q ell t)

/--
The complete nonzero complex Fourier spectrum equals the
embedding of the real cosine series.
@isnad1 id=eq.2h2v.s6.571e494b5051 from=translated src=- shape=d294e578 vocab=3909b638
-/
theorem nearestQNonzeroFourierSum_eq_realCosineSeries
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (Finset.Ico
          1
          (nearestQExactPeriod q))
        (fun ell =>
          nearestQCenteredOmegaFourierCoeff q ell *
            nearestQFourierRoot q ^
              (ell * (t + 1))) =
      ((nearestQCenteredOmegaRealCosineSeries
          q t : ℝ) : ℂ) := by
  unfold nearestQCenteredOmegaRealCosineSeries
  exact
    nearestQNonzeroFourierSum_eq_realCosineSum
      q t hq hqEven

/--
The real cosine series written explicitly in terms of the
real Fourier amplitudes and their angles.
@isnad1 id=eq.0h2v.s5.9c0b21f179fe from=translated src=- shape=7e21af75 vocab=89834aca
-/
theorem nearestQCenteredOmegaRealCosineSeries_eq
    (q t : Nat) :
    nearestQCenteredOmegaRealCosineSeries q t =
      Finset.sum
        (nearestQLowerFourierFrequencies q)
        (fun ell =>
          2 *
            nearestQCenteredOmegaRealCoeff q ell *
            Real.cos
              (nearestQCenteredOmegaCosineAngle
                q ell t)) := by
  rfl

/--
For even `q ≥ 6`, the complete Fourier reconstruction of the
centered correction is exactly the complex embedding of the
finite real cosine series.
@isnad1 id=eq.2h2v.s4.8fd62f9c0797 from=translated src=- shape=85386791 vocab=54186bcf
-/
theorem nearestQCenteredOmegaFourierSeries_eq_realCosineSeries
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQCenteredOmegaFourierSeries q t =
      ((nearestQCenteredOmegaRealCosineSeries q t : ℝ) : ℂ) := by
  unfold nearestQCenteredOmegaFourierSeries
  exact
    nearestQNonzeroFourierSum_eq_realCosineSeries
      q t hq hqEven

/--
For even `q ≥ 6`, the centered nearest-root correction is
exactly the finite real cosine series, viewed in `ℂ`.
@isnad1 id=eq.2h2v.s4.898c50addec1 from=translated src=- shape=68ceec8d vocab=cefa9a45
-/
theorem nearestQCenteredOmegaAt_coe_eq_realCosineSeries
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (nearestQCenteredOmegaAt q t : ℂ) =
      ((nearestQCenteredOmegaRealCosineSeries q t : ℝ) : ℂ) := by
  have hqPos :
      0 < q := by
    omega
  calc
    (nearestQCenteredOmegaAt q t : ℂ) =
        nearestQCenteredOmegaFourierSeries q t := by
      symm
      exact
        nearestQCenteredOmegaFourierSeries_eq
          q t hqPos
    _ =
        ((nearestQCenteredOmegaRealCosineSeries
            q t : ℝ) : ℂ) :=
      nearestQCenteredOmegaFourierSeries_eq_realCosineSeries
        q t hq hqEven

/--
Article-form finite cosine expansion of the centered
nearest-root correction.

For even `q ≥ 6`,

`ω̃_q(t) =
  Σ_{1 ≤ ell < H_q}
    2 b_{q,ell}
      cos ((2t+1) ell π / P_q)`.
@isnad1 id=eq.2h2v.s7.056a34f01fc0 from=translated src=- shape=f67a71d4 vocab=672c87e1
-/
theorem nearestQCenteredOmegaAt_coe_eq_finiteCosineExpansion
    (q t : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (nearestQCenteredOmegaAt q t : ℂ) =
      ((Finset.sum
          (Finset.Ico
            1
            (nearestQEvenResidueHalfPeriod q))
          (fun ell =>
            2 *
              nearestQCenteredOmegaRealCoeff q ell *
              Real.cos
                ((((2 * t + 1 : Nat) : ℝ) *
                    (ell : ℝ) * Real.pi) /
                  (nearestQExactPeriod q : ℝ))) : ℝ) : ℂ) := by
  rw [
    nearestQCenteredOmegaAt_coe_eq_realCosineSeries
      q t hq hqEven
  ]
  congr 1

end RoundedRootSums
