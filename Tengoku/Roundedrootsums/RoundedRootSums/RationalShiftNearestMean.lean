/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftNearest

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residue images and mean corrections for nearest q-th root sums

This file studies the image of the odd q-th power map modulo `2^q`
and uses that image to compute the exact mean of the nearest-root
correction sequence.

For the article, the central finite set is

`H_q = {x^q mod 2^q : x is odd}`.

The relevant step exponent is

* `d_q = 1` for odd `q`;
* `d_q = min(q, ν₂(q) + 2)` for even `q`.
-/

namespace RoundedRootSums

/--
The exponent `d_q` controlling the spacing of the odd q-th power
residues modulo `2^q`.

It equals `1` for odd `q`, and
`min(q, ν₂(q) + 2)` otherwise.-/
def nearestQResidueStepExponent
    (q : Nat) : Nat :=
  if Odd q then
    1
  else
    Nat.min q (nearestQTwoAdicOrder q + 2)

/--
For odd `q`, the residue-step exponent is one.-/
theorem nearestQResidueStepExponent_of_odd
    (q : Nat)
    (hqOdd : Odd q) :
    nearestQResidueStepExponent q = 1 := by
  simp [
    nearestQResidueStepExponent,
    hqOdd
  ]

/--
For nonodd `q`, the residue-step exponent is
`min(q, ν₂(q) + 2)`.-/
theorem nearestQResidueStepExponent_of_not_odd
    (q : Nat)
    (hqNotOdd : ¬Odd q) :
    nearestQResidueStepExponent q =
      Nat.min q (nearestQTwoAdicOrder q + 2) := by
  simp [
    nearestQResidueStepExponent,
    hqNotOdd
  ]

/--
The number of distinct residues predicted by the arithmetic
progression description of the odd q-th power image.-/
def nearestQResidueImageSize
    (q : Nat) : Nat :=
  2 ^ (q - nearestQResidueStepExponent q)

/--
The finite image of the odd q-th power map modulo `2^q`.

The index `r` represents the odd residue `2 * r + 1`.
The range of length `2^(q - 1)` runs through every odd
residue class modulo `2^q` exactly once.-/
def nearestQOddResidueImage
    (q : Nat) : Finset Nat :=
  (Finset.range (nearestQResiduePeriod q)).image
    (nearestQPowerResidueAt q)

/--
The predicted residue-image size is always positive.-/
theorem nearestQResidueImageSize_pos
    (q : Nat) :
    0 < nearestQResidueImageSize q := by
  unfold nearestQResidueImageSize
  positivity

/--
Membership in `H_q` is equivalent to being the q-th power
residue associated with some index in one full odd-residue range.-/
theorem mem_nearestQOddResidueImage_iff
    (q y : Nat) :
    y ∈ nearestQOddResidueImage q ↔
      ∃ r : Nat,
        r < nearestQResiduePeriod q ∧
        nearestQPowerResidueAt q r = y := by
  classical
  simp [nearestQOddResidueImage]

/--
The residue-step exponent never exceeds `q`.-/
theorem nearestQResidueStepExponent_le
    (q : Nat) :
    nearestQResidueStepExponent q ≤ q := by
  unfold nearestQResidueStepExponent
  by_cases hqOdd : Odd q
  · rw [ite_eq_left hqOdd]
    obtain ⟨k, hk⟩ := hqOdd
    omega
  · rw [ite_eq_right hqOdd]
    exact
      Nat.min_le_left
        q
        (nearestQTwoAdicOrder q + 2)

/--
The arithmetic progression predicted to be the image
of the odd q-th power map modulo `2^q`.-/
def nearestQPredictedResidueImage
    (q : Nat) : Finset Nat :=
  (Finset.range (nearestQResidueImageSize q)).image
    (fun j =>
      1 +
        2 ^ nearestQResidueStepExponent q * j)

/--
Membership in the predicted residue image is equivalent
to having the form

`1 + 2^d_q * j`

with `j < 2^(q - d_q)`.-/
theorem mem_nearestQPredictedResidueImage_iff
    (q y : Nat) :
    y ∈ nearestQPredictedResidueImage q ↔
      ∃ j : Nat,
        j < nearestQResidueImageSize q ∧
        1 +
            2 ^ nearestQResidueStepExponent q * j =
          y := by
  classical
  simp [nearestQPredictedResidueImage]

/--
For every positive exponent `q`, the residue-step exponent
is positive.-/
theorem nearestQResidueStepExponent_pos
    (q : Nat)
    (hq : 0 < q) :
    0 < nearestQResidueStepExponent q := by
  unfold nearestQResidueStepExponent
  by_cases hqOdd : Odd q
  · rw [ite_eq_left hqOdd]
    norm_num
  · rw [ite_eq_right hqOdd]
    exact
      (lt_min_iff).2
        ⟨hq, by omega⟩

/--
Every element of the predicted residue image is congruent
to one modulo `2^d_q`.-/
theorem nearestQPredictedResidueImage_mod_step
    (q y : Nat)
    (hy :
      y ∈ nearestQPredictedResidueImage q) :
    y % 2 ^ nearestQResidueStepExponent q =
      1 % 2 ^ nearestQResidueStepExponent q := by
  rcases
      (mem_nearestQPredictedResidueImage_iff
        q y).1 hy with
    ⟨j, _hj, hjy⟩
  rw [← hjy]
  simp [Nat.add_mod]

/--
Every value in the predicted arithmetic progression lies
strictly below the modulus `2^q`.-/
theorem nearestQPredictedResidueValue_lt_modulus
    (q j : Nat)
    (hq : 0 < q)
    (hj :
      j < nearestQResidueImageSize q) :
    1 +
        2 ^ nearestQResidueStepExponent q * j <
      2 ^ q := by
  have hdPos :
      0 < nearestQResidueStepExponent q :=
    nearestQResidueStepExponent_pos q hq
  have hdLe :
      nearestQResidueStepExponent q ≤ q :=
    nearestQResidueStepExponent_le q
  have hsplit :
      2 ^ nearestQResidueStepExponent q *
          nearestQResidueImageSize q =
        2 ^ q := by
    unfold nearestQResidueImageSize
    have hexponent :
        nearestQResidueStepExponent q +
            (q - nearestQResidueStepExponent q) =
          q := by
      omega
    rw [← pow_add, hexponent]
  have hstep :
      1 < 2 ^ nearestQResidueStepExponent q := by
    exact
      Nat.one_lt_two_pow
        (Nat.ne_of_gt hdPos)
  have hjSucc :
      j + 1 ≤ nearestQResidueImageSize q := by
    omega
  have hfirst :
      1 +
          2 ^ nearestQResidueStepExponent q * j <
        2 ^ nearestQResidueStepExponent q *
          (j + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hsecond :
      2 ^ nearestQResidueStepExponent q *
          (j + 1) ≤
        2 ^ nearestQResidueStepExponent q *
          nearestQResidueImageSize q := by
    exact
      Nat.mul_le_mul_left
        (2 ^ nearestQResidueStepExponent q)
        hjSucc
  calc
    1 +
          2 ^ nearestQResidueStepExponent q * j <
        2 ^ nearestQResidueStepExponent q *
          (j + 1) := hfirst
    _ ≤
        2 ^ nearestQResidueStepExponent q *
          nearestQResidueImageSize q := hsecond
    _ = 2 ^ q := hsplit

/--
The parametrization

`j ↦ 1 + 2^d_q * j`

of the predicted residue image is injective.-/
theorem nearestQPredictedResidueParam_injective
    (q : Nat) :
    Function.Injective
      (fun j : Nat =>
        1 +
          2 ^ nearestQResidueStepExponent q * j) := by
  intro a b hab
  have hmul :
      2 ^ nearestQResidueStepExponent q * a =
        2 ^ nearestQResidueStepExponent q * b := by
    exact Nat.add_left_cancel hab
  exact
    Nat.mul_left_cancel
      (by positivity)
      hmul

/--
The predicted residue image contains exactly

`2^(q - d_q)`

elements.-/
theorem nearestQPredictedResidueImage_card
    (q : Nat) :
    (nearestQPredictedResidueImage q).card =
      nearestQResidueImageSize q := by
  classical
  unfold nearestQPredictedResidueImage
  calc
    ((Finset.range (nearestQResidueImageSize q)).image
        (fun j =>
          1 +
            2 ^ nearestQResidueStepExponent q * j)).card =
        (Finset.range
          (nearestQResidueImageSize q)).card := by
      exact
        Finset.card_image_iff.mpr
          (Set.injOn_of_injective
            (nearestQPredictedResidueParam_injective q))
    _ = nearestQResidueImageSize q := by
      exact Finset.card_range _

/--
For positive `q`, the predicted residue image is contained
in the natural residue range `{0, ..., 2^q - 1}`.-/
theorem nearestQPredictedResidueImage_subset_range
    (q : Nat)
    (hq : 0 < q) :
    nearestQPredictedResidueImage q ⊆
      Finset.range (2 ^ q) := by
  intro y hy
  rw [Finset.mem_range]
  rcases
      (mem_nearestQPredictedResidueImage_iff
        q y).1 hy with
    ⟨j, hj, hjy⟩
  rw [← hjy]
  exact
    nearestQPredictedResidueValue_lt_modulus
      q j hq hj

/--
Every value of the nearest-root power-residue sequence
lies strictly below its modulus `2^q`.-/
theorem nearestQPowerResidueAt_lt_modulus
    (q r : Nat) :
    nearestQPowerResidueAt q r < 2 ^ q := by
  rw [nearestQPowerResidueAt_eq_oddPowerMod]
  exact
    Nat.mod_lt
      ((2 * r + 1) ^ q)
      (by positivity)

/--
The actual odd q-th power residue image is contained
in the natural residue range `{0, ..., 2^q - 1}`.-/
theorem nearestQOddResidueImage_subset_range
    (q : Nat) :
    nearestQOddResidueImage q ⊆
      Finset.range (2 ^ q) := by
  intro y hy
  rw [Finset.mem_range]
  rcases
      (mem_nearestQOddResidueImage_iff
        q y).1 hy with
    ⟨r, _hr, hry⟩
  rw [← hry]
  exact
    nearestQPowerResidueAt_lt_modulus
      q r

/--
For odd `q`, every odd q-th power is congruent to one
modulo the predicted step `2^d_q = 2`.-/
theorem nearestQOddPower_mod_step_of_odd
    (q r : Nat)
    (hqOdd : Odd q) :
    (2 * r + 1) ^ q %
        2 ^ nearestQResidueStepExponent q =
      1 % 2 ^ nearestQResidueStepExponent q := by
  rw [
    nearestQResidueStepExponent_of_odd
      q hqOdd
  ]
  have hbaseOdd :
      Odd (2 * r + 1) := by
    exact ⟨r, by omega⟩
  have hpowOdd :
      Odd ((2 * r + 1) ^ q) :=
    hbaseOdd.pow
  obtain ⟨k, hk⟩ := hpowOdd
  rw [hk]
  simp

/--
For positive even `q`, every odd q-th power is congruent
to one modulo

`2^min(q, ν₂(q) + 2)`.-/
theorem nearestQOddPower_mod_step_of_even
    (q r : Nat)
    (hq : 0 < q)
    (hqEven : Even q) :
    (2 * r + 1) ^ q %
        2 ^ nearestQResidueStepExponent q =
      1 % 2 ^ nearestQResidueStepExponent q := by
  have hqNotOdd :
      ¬Odd q := by
    intro hqOdd
    obtain ⟨a, ha⟩ := hqEven
    obtain ⟨b, hb⟩ := hqOdd
    omega
  rw [
    nearestQResidueStepExponent_of_not_odd
      q hqNotOdd
  ]
  by_cases hrZero :
      r = 0
  · subst r
    simp
  · let x : Nat := 2 * r + 1
    have hxGt :
        1 < x := by
      dsimp [x]
      omega
    have hxNotTwo :
        ¬2 ∣ x := by
      intro hx
      obtain ⟨k, hk⟩ := hx
      dsimp [x] at hk
      omega
    have hqNe :
        q ≠ 0 :=
      Nat.ne_of_gt hq
    have hvaluation :
        padicValNat 2 q + 2 ≤
          padicValNat 2 (x ^ q - 1) := by
      exact
        padicValNat.pow_two_sub_one_ge
          hxGt
          hxNotTwo
          hqNe
          hqEven
    have hstepValuation :
        Nat.min
            q
            (nearestQTwoAdicOrder q + 2) ≤
          padicValNat 2 (x ^ q - 1) := by
      have hright :
          nearestQTwoAdicOrder q + 2 ≤
            padicValNat 2 (x ^ q - 1) := by
        simpa [nearestQTwoAdicOrder] using
          hvaluation
      exact
        le_trans
          (Nat.min_le_right
            q
            (nearestQTwoAdicOrder q + 2))
          hright
    have hdvd :
        2 ^
            Nat.min
              q
              (nearestQTwoAdicOrder q + 2) ∣
          x ^ q - 1 := by
      exact
        (padicValNat_dvd_iff
          (Nat.min
            q
            (nearestQTwoAdicOrder q + 2))
          (x ^ q - 1)).2
          (Or.inr hstepValuation)
    have honeLe :
        1 ≤ x ^ q := by
      exact
        Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero q (by omega))
    have hmod :
        Nat.ModEq
          (2 ^
            Nat.min
              q
              (nearestQTwoAdicOrder q + 2))
          (x ^ q)
          1 := by
      exact
        ((Nat.modEq_iff_dvd' honeLe).2
          hdvd).symm
    change
      x ^ q %
          2 ^
            Nat.min
              q
              (nearestQTwoAdicOrder q + 2) =
        1 %
          2 ^
            Nat.min
              q
              (nearestQTwoAdicOrder q + 2)
        at hmod
    simpa [x] using hmod

/--
For every positive `q`, every odd q-th power is congruent
to one modulo the predicted step `2^d_q`.-/
theorem nearestQOddPower_mod_step
    (q r : Nat)
    (hq : 0 < q) :
    (2 * r + 1) ^ q %
        2 ^ nearestQResidueStepExponent q =
      1 % 2 ^ nearestQResidueStepExponent q := by
  by_cases hqOdd :
      Odd q
  · exact
      nearestQOddPower_mod_step_of_odd
        q r hqOdd
  · have hqEven :
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
    exact
      nearestQOddPower_mod_step_of_even
        q r hq hqEven

/--
For every positive `q`, every value of the nearest-root
power-residue sequence is congruent to one modulo `2^d_q`.-/
theorem nearestQPowerResidueAt_mod_step
    (q r : Nat)
    (hq : 0 < q) :
    nearestQPowerResidueAt q r %
        2 ^ nearestQResidueStepExponent q =
      1 % 2 ^ nearestQResidueStepExponent q := by
  change
    Nat.ModEq
      (2 ^ nearestQResidueStepExponent q)
      (nearestQPowerResidueAt q r)
      1
  have hstepDvd :
      2 ^ nearestQResidueStepExponent q ∣
        2 ^ q := by
    exact
      Nat.pow_dvd_pow
        2
        (nearestQResidueStepExponent_le q)
  have hresidueFull :
      Nat.ModEq
        (2 ^ q)
        (nearestQPowerResidueAt q r)
        ((2 * r + 1) ^ q) := by
    rw [nearestQPowerResidueAt_eq_oddPowerMod]
    exact
      Nat.mod_modEq
        ((2 * r + 1) ^ q)
        (2 ^ q)
  have hresidueStep :
      Nat.ModEq
        (2 ^ nearestQResidueStepExponent q)
        (nearestQPowerResidueAt q r)
        ((2 * r + 1) ^ q) := by
    exact
      hresidueFull.of_dvd hstepDvd
  have hpowerStep :
      Nat.ModEq
        (2 ^ nearestQResidueStepExponent q)
        ((2 * r + 1) ^ q)
        1 := by
    exact
      nearestQOddPower_mod_step
        q r hq
  exact
    hresidueStep.trans hpowerStep

/--
The modulus `2^q` factors as the predicted residue step
times the predicted image size.-/
theorem nearestQResidueStep_mul_imageSize
    (q : Nat) :
    2 ^ nearestQResidueStepExponent q *
        nearestQResidueImageSize q =
      2 ^ q := by
  unfold nearestQResidueImageSize
  calc
    2 ^ nearestQResidueStepExponent q *
          2 ^ (q - nearestQResidueStepExponent q) =
        2 ^
          (nearestQResidueStepExponent q +
            (q - nearestQResidueStepExponent q)) := by
      rw [pow_add]
    _ = 2 ^ q := by
      rw [
        Nat.add_sub_of_le
          (nearestQResidueStepExponent_le q)
      ]

/--
Every actual odd q-th power residue has the form

`1 + 2^d_q * j`

for some `j < 2^(q - d_q)`.-/
theorem nearestQPowerResidueAt_exists_predictedParam
    (q r : Nat)
    (hq : 0 < q) :
    ∃ j : Nat,
      j < nearestQResidueImageSize q ∧
      1 +
          2 ^ nearestQResidueStepExponent q * j =
        nearestQPowerResidueAt q r := by
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
  have hsPos :
      0 < s := by
    omega
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
    have hdiv :
        y % s + s * (y / s) = y :=
      Nat.mod_add_div y s
    rw [hmod] at hdiv
    exact hdiv
  have hyLt :
      y < 2 ^ q := by
    dsimp [y]
    exact
      nearestQPowerResidueAt_lt_modulus
        q r
  have hproductLt :
      s * (y / s) <
        s * nearestQResidueImageSize q := by
    have hleft :
        s * (y / s) < 2 ^ q := by
      omega
    have hfactor :
        s * nearestQResidueImageSize q =
          2 ^ q := by
      dsimp [s]
      exact
        nearestQResidueStep_mul_imageSize q
    rw [hfactor]
    exact hleft
  have hjLt :
      y / s < nearestQResidueImageSize q := by
    exact
      (Nat.mul_lt_mul_left hsPos).mp
        hproductLt
  refine ⟨y / s, hjLt, ?_⟩
  simpa [s, y] using hdecomp

/--
For every positive `q`, the actual image of the odd q-th
power map is contained in the predicted arithmetic progression.-/
theorem nearestQOddResidueImage_subset_predicted
    (q : Nat)
    (hq : 0 < q) :
    nearestQOddResidueImage q ⊆
      nearestQPredictedResidueImage q := by
  intro y hy
  rcases
      (mem_nearestQOddResidueImage_iff
        q y).1 hy with
    ⟨r, _hr, hry⟩
  rcases
      nearestQPowerResidueAt_exists_predictedParam
        q r hq with
    ⟨j, hj, hjValue⟩
  apply
    (mem_nearestQPredictedResidueImage_iff
      q y).2
  exact
    ⟨j, hj, hjValue.trans hry⟩

/--
For positive `q`, the number of distinct odd q-th power
residues is at most the predicted image size

`2^(q - d_q)`.-/
theorem nearestQOddResidueImage_card_le
    (q : Nat)
    (hq : 0 < q) :
    (nearestQOddResidueImage q).card ≤
      nearestQResidueImageSize q := by
  calc
    (nearestQOddResidueImage q).card ≤
        (nearestQPredictedResidueImage q).card := by
      exact
        Finset.card_le_card
          (nearestQOddResidueImage_subset_predicted
            q hq)
    _ = nearestQResidueImageSize q :=
      nearestQPredictedResidueImage_card q

/--
The geometric factor associated with the difference

`(2 * a + 1)^q - (2 * b + 1)^q`.-/
def nearestQPairGeomSum
    (q a b : Nat) : Nat :=
  Finset.sum
    (Finset.range q)
    (fun i =>
      (2 * a + 1) ^ i *
        (2 * b + 1) ^ (q - 1 - i))

/--
Modulo two, the pairwise geometric factor has the same
residue as the number `q` of its summands.-/
theorem nearestQPairGeomSum_mod_two
    (q a b : Nat) :
    nearestQPairGeomSum q a b % 2 =
      q % 2 := by
  unfold nearestQPairGeomSum
  rw [Finset.sum_nat_mod]
  have ha :
      (2 * a + 1) % 2 = 1 := by
    omega
  have hb :
      (2 * b + 1) % 2 = 1 := by
    omega
  simp [
    Nat.mul_mod,
    Nat.pow_mod,
    ha,
    hb
  ]

/--
For odd `q`, the geometric factor relating two odd
q-th powers is itself odd.-/
theorem nearestQPairGeomSum_not_two_dvd
    (q a b : Nat)
    (hqOdd : Odd q) :
    ¬2 ∣ nearestQPairGeomSum q a b := by
  rw [Nat.two_dvd_ne_zero]
  rw [nearestQPairGeomSum_mod_two]
  exact Nat.odd_iff.mp hqOdd

/--
For `b ≤ a`, the difference of two odd q-th powers factors as

`G_q(a,b) * (2 * (a - b))`.-/
theorem nearestQPairGeomSum_mul_two_mul_sub
    (q a b : Nat)
    (hba : b ≤ a) :
    nearestQPairGeomSum q a b *
        (2 * (a - b)) =
      (2 * a + 1) ^ q -
        (2 * b + 1) ^ q := by
  have hbaseLe :
      2 * b + 1 ≤ 2 * a + 1 := by
    omega
  have hbaseSub :
      (2 * a + 1) - (2 * b + 1) =
        2 * (a - b) := by
    omega
  simpa [
    nearestQPairGeomSum,
    hbaseSub
  ] using
    (geom_sum₂_mul_of_ge
      (R := Nat)
      hbaseLe
      q)

/--
For odd `q`, if two entries of the power-residue sequence
are equal and `b ≤ a`, then

`2^q ∣ 2 * (a - b)`.-/
theorem nearestQPowerResidueAt_odd_eq_implies_pow_dvd_two_mul_sub
    (q a b : Nat)
    (hqOdd : Odd q)
    (hba : b ≤ a)
    (heq :
      nearestQPowerResidueAt q a =
        nearestQPowerResidueAt q b) :
    2 ^ q ∣ 2 * (a - b) := by
  have hmod :
      Nat.ModEq
        (2 ^ q)
        ((2 * a + 1) ^ q)
        ((2 * b + 1) ^ q) := by
    rw [
      nearestQPowerResidueAt_eq_oddPowerMod,
      nearestQPowerResidueAt_eq_oddPowerMod
    ] at heq
    exact heq
  have hbaseLe :
      2 * b + 1 ≤ 2 * a + 1 := by
    omega
  have hpowLe :
      (2 * b + 1) ^ q ≤
        (2 * a + 1) ^ q := by
    exact
      Nat.pow_le_pow_left
        hbaseLe
        q
  have hpowDvd :
      2 ^ q ∣
        (2 * a + 1) ^ q -
          (2 * b + 1) ^ q := by
    exact
      (Nat.modEq_iff_dvd' hpowLe).1
        hmod.symm
  have hproduct :
      2 ^ q ∣
        nearestQPairGeomSum q a b *
          (2 * (a - b)) := by
    rw [
      nearestQPairGeomSum_mul_two_mul_sub
        q a b hba
    ]
    exact hpowDvd
  have hcoprimeTwo :
      Nat.Coprime
        2
        (nearestQPairGeomSum q a b) := by
    exact
      (Nat.prime_two.coprime_iff_not_dvd).2
        (nearestQPairGeomSum_not_two_dvd
          q a b hqOdd)
  have hcoprimePow :
      Nat.Coprime
        (2 ^ q)
        (nearestQPairGeomSum q a b) :=
    hcoprimeTwo.pow_left q
  exact
    hcoprimePow.dvd_of_dvd_mul_left
      hproduct

/--
For odd positive `q`, equality of two power residues with
`b ≤ a` implies that the candidate odd-case period divides
the difference of their indices.-/
theorem nearestQPowerResidueAt_odd_eq_implies_period_dvd_sub
    (q a b : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q)
    (hba : b ≤ a)
    (heq :
      nearestQPowerResidueAt q a =
        nearestQPowerResidueAt q b) :
    nearestQResiduePeriod q ∣ a - b := by
  rw [nearestQResiduePeriod_eq]
  have htwo :
      2 ^ q ∣ 2 * (a - b) :=
    nearestQPowerResidueAt_odd_eq_implies_pow_dvd_two_mul_sub
      q a b hqOdd hba heq
  have hqSplit :
      (q - 1) + 1 = q := by
    omega
  have hpowEq :
      2 ^ (q - 1) * 2 =
        2 ^ q := by
    calc
      2 ^ (q - 1) * 2 =
          2 ^ ((q - 1) + 1) := by
        rw [pow_succ]
      _ = 2 ^ q := by
        rw [hqSplit]
  have hcancel :
      2 ^ (q - 1) * 2 ∣
        (a - b) * 2 := by
    rw [hpowEq]
    simpa [Nat.mul_comm] using htwo
  exact
    Nat.dvd_of_mul_dvd_mul_right
      (k := 2)
      (by decide)
      hcancel

/--
For odd positive `q`, the power-residue map is injective
on one full range of odd residue classes.-/
theorem nearestQPowerResidueAt_odd_injOn_range
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    Set.InjOn
      (nearestQPowerResidueAt q)
      (↑(Finset.range
        (nearestQResiduePeriod q)) : Set Nat) := by
  intro a ha b hb heq
  have haLt :
      a < nearestQResiduePeriod q := by
    simpa using ha
  have hbLt :
      b < nearestQResiduePeriod q := by
    simpa using hb
  by_cases hba :
      b ≤ a
  · have hdvd :
        nearestQResiduePeriod q ∣ a - b :=
      nearestQPowerResidueAt_odd_eq_implies_period_dvd_sub
        q a b hq hqOdd hba heq
    have hzero :
        a - b = 0 := by
      by_contra hne
      have hpos :
          0 < a - b :=
        Nat.pos_of_ne_zero hne
      have hperiodLe :
          nearestQResiduePeriod q ≤ a - b :=
        Nat.le_of_dvd hpos hdvd
      omega
    omega
  · have hab :
        a ≤ b := by
      omega
    have hdvd :
        nearestQResiduePeriod q ∣ b - a :=
      nearestQPowerResidueAt_odd_eq_implies_period_dvd_sub
        q b a hq hqOdd hab heq.symm
    have hzero :
        b - a = 0 := by
      by_contra hne
      have hpos :
          0 < b - a :=
        Nat.pos_of_ne_zero hne
      have hperiodLe :
          nearestQResiduePeriod q ≤ b - a :=
        Nat.le_of_dvd hpos hdvd
      omega
    omega

/--
For odd positive `q`, the actual odd q-th power residue
image has exactly the predicted number of elements.-/
theorem nearestQOddResidueImage_card_of_odd
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    (nearestQOddResidueImage q).card =
      nearestQResidueImageSize q := by
  classical
  unfold nearestQOddResidueImage
  calc
    ((Finset.range
          (nearestQResiduePeriod q)).image
        (nearestQPowerResidueAt q)).card =
        (Finset.range
          (nearestQResiduePeriod q)).card := by
      exact
        Finset.card_image_iff.mpr
          (nearestQPowerResidueAt_odd_injOn_range
            q hq hqOdd)
    _ = nearestQResiduePeriod q := by
      exact Finset.card_range _
    _ = nearestQResidueImageSize q := by
      unfold nearestQResidueImageSize
      rw [
        nearestQResidueStepExponent_of_odd
          q hqOdd
      ]
      rw [nearestQResiduePeriod_eq]

/--
For odd positive `q`, the actual image of the odd q-th
power map is exactly the predicted arithmetic progression.-/
theorem nearestQOddResidueImage_eq_predicted_of_odd
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    nearestQOddResidueImage q =
      nearestQPredictedResidueImage q := by
  apply
    Finset.eq_of_subset_of_card_le
  · exact
      nearestQOddResidueImage_subset_predicted
        q hq
  · rw [
      nearestQPredictedResidueImage_card,
      nearestQOddResidueImage_card_of_odd
        q hq hqOdd
    ]

/--
For even `q ≥ 6`, the residue-step exponent is exactly

`ν₂(q) + 2`.-/
theorem nearestQResidueStepExponent_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQResidueStepExponent q =
      nearestQTwoAdicOrder q + 2 := by
  have hqNotOdd :
      ¬Odd q := by
    intro hqOdd
    obtain ⟨a, ha⟩ := hqEven
    obtain ⟨b, hb⟩ := hqOdd
    omega
  rw [
    nearestQResidueStepExponent_of_not_odd
      q hqNotOdd
  ]
  apply Nat.min_eq_right
  exact
    nearestQTwoAdicOrder_add_two_le_of_even_ge_six
      q hq hqEven

/--
For even `q ≥ 6`, the predicted number of distinct residues

`2^(q - ν₂(q) - 2)`

is exactly the previously defined even-case half-period.-/
theorem nearestQResidueImageSize_eq_evenHalfPeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQResidueImageSize q =
      nearestQEvenResidueHalfPeriod q := by
  unfold nearestQResidueImageSize
  unfold nearestQEvenResidueHalfPeriod
  rw [
    nearestQResidueStepExponent_of_even_ge_six
      q hq hqEven
  ]
  have hbound :
      nearestQTwoAdicOrder q + 2 ≤ q :=
    nearestQTwoAdicOrder_add_two_le_of_even_ge_six
      q hq hqEven
  have hexponent :
      q - (nearestQTwoAdicOrder q + 2) =
        q - 2 - nearestQTwoAdicOrder q := by
    omega
  rw [hexponent]

/--
For positive even `q` and `b < a`, the exact two-adic
valuation of the difference of the corresponding odd powers is

`v₂((2a+1)^q - (2b+1)^q) + 1
   = v₂(a+b+1) + v₂(a-b) + v₂(q) + 2`.-/
theorem nearestQOddBases_pow_sub_valuation
    (q a b : Nat)
    (hq : 0 < q)
    (hqEven : Even q)
    (hba : b < a) :
    padicValNat 2
          ((2 * a + 1) ^ q -
            (2 * b + 1) ^ q) +
        1 =
      padicValNat 2 (a + b + 1) +
          padicValNat 2 (a - b) +
          nearestQTwoAdicOrder q +
        2 := by
  have hbaseLt :
      2 * b + 1 < 2 * a + 1 := by
    omega
  have hbaseSub :
      (2 * a + 1) - (2 * b + 1) =
        2 * (a - b) := by
    omega
  have hbaseAdd :
      (2 * a + 1) + (2 * b + 1) =
        2 * (a + b + 1) := by
    omega
  have htwoDvd :
      2 ∣ (2 * a + 1) - (2 * b + 1) := by
    rw [hbaseSub]
    exact dvd_mul_right 2 (a - b)
  have hbaseOdd :
      ¬2 ∣ 2 * a + 1 :=
    Nat.two_not_dvd_two_mul_add_one a
  have hvaluation :=
    padicValNat.pow_two_sub_pow
      hbaseLt
      htwoDvd
      hbaseOdd
      (Nat.ne_of_gt hq)
      hqEven
  rw [hbaseAdd, hbaseSub] at hvaluation
  have hdiffNe :
      a - b ≠ 0 := by
    omega
  have hsumNe :
      a + b + 1 ≠ 0 := by
    omega
  have hvalDiff :
      padicValNat 2 (2 * (a - b)) =
        1 + padicValNat 2 (a - b) := by
    rw [
      padicValNat.mul
        (p := 2)
        (by norm_num)
        hdiffNe
    ]
    norm_num
  have hvalSum :
      padicValNat 2 (2 * (a + b + 1)) =
        1 + padicValNat 2 (a + b + 1) := by
    rw [
      padicValNat.mul
        (p := 2)
        (by norm_num)
        hsumNe
    ]
    norm_num
  rw [hvalSum, hvalDiff] at hvaluation
  unfold nearestQTwoAdicOrder
  omega

/--
For even `q ≥ 6`, equality of two power residues with
`b < a` forces

`2^(q - 1 - ν₂(q)) ∣ (a - b) * (a + b + 1)`.-/
theorem nearestQPowerResidueAt_even_eq_implies_period_dvd_product
    (q a b : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (hba : b < a)
    (heq :
      nearestQPowerResidueAt q a =
        nearestQPowerResidueAt q b) :
    2 ^ (q - 1 - nearestQTwoAdicOrder q) ∣
      (a - b) * (a + b + 1) := by
  have hqPos :
      0 < q := by
    omega
  have hmod :
      Nat.ModEq
        (2 ^ q)
        ((2 * a + 1) ^ q)
        ((2 * b + 1) ^ q) := by
    rw [
      nearestQPowerResidueAt_eq_oddPowerMod,
      nearestQPowerResidueAt_eq_oddPowerMod
    ] at heq
    exact heq
  have hbaseLt :
      2 * b + 1 < 2 * a + 1 := by
    omega
  have hpowLt :
      (2 * b + 1) ^ q <
        (2 * a + 1) ^ q := by
    exact
      Nat.pow_lt_pow_left
        hbaseLt
        (Nat.ne_of_gt hqPos)
  have hpowLe :
      (2 * b + 1) ^ q ≤
        (2 * a + 1) ^ q :=
    hpowLt.le
  have hpowDvd :
      2 ^ q ∣
        (2 * a + 1) ^ q -
          (2 * b + 1) ^ q := by
    exact
      (Nat.modEq_iff_dvd' hpowLe).1
        hmod.symm
  have hpowSubNe :
      (2 * a + 1) ^ q -
          (2 * b + 1) ^ q ≠ 0 := by
    omega
  have hvaluationLower :
      q ≤
        padicValNat 2
          ((2 * a + 1) ^ q -
            (2 * b + 1) ^ q) := by
    exact
      (padicValNat_dvd_iff_le
        hpowSubNe).1
        hpowDvd
  have hvaluation :=
    nearestQOddBases_pow_sub_valuation
      q a b hqPos hqEven hba
  have hdiffNe :
      a - b ≠ 0 := by
    omega
  have hsumNe :
      a + b + 1 ≠ 0 := by
    omega
  have hproductNe :
      (a - b) * (a + b + 1) ≠ 0 :=
    mul_ne_zero hdiffNe hsumNe
  have hproductValuation :
      padicValNat 2
          ((a - b) * (a + b + 1)) =
        padicValNat 2 (a - b) +
          padicValNat 2 (a + b + 1) := by
    exact
      padicValNat.mul
        hdiffNe
        hsumNe
  apply
    (padicValNat_dvd_iff_le
      hproductNe).2
  rw [hproductValuation]
  omega

/--
For `b ≤ a`, at least one of the two factors

`a - b` and `a + b + 1`

is odd.-/
theorem nearestQIndexDifference_or_sum_not_two_dvd
    (a b : Nat)
    (hba : b ≤ a) :
    ¬2 ∣ a - b ∨
      ¬2 ∣ a + b + 1 := by
  by_cases hdiff :
      2 ∣ a - b
  · right
    intro hsum
    have htotal :
        2 ∣
          (a - b) + (a + b + 1) :=
      Nat.dvd_add hdiff hsum
    have htotalEq :
        (a - b) + (a + b + 1) =
          2 * a + 1 := by
      omega
    rw [htotalEq] at htotal
    exact
      Nat.two_not_dvd_two_mul_add_one
        a
        htotal
  · exact Or.inl hdiff

/--
For even `q ≥ 6`, two distinct indices in the first
predicted half-period cannot have the same q-th power residue.-/
theorem nearestQPowerResidueAt_even_ne_of_lt_halfPeriod
    (q a b : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (ha :
      a < nearestQEvenResidueHalfPeriod q)
    (hb :
      b < nearestQEvenResidueHalfPeriod q)
    (hba : b < a) :
    nearestQPowerResidueAt q a ≠
      nearestQPowerResidueAt q b := by
  intro heq
  have hproduct :
      nearestQEvenResiduePeriod q ∣
        (a - b) * (a + b + 1) := by
    change
      2 ^ (q - 1 - nearestQTwoAdicOrder q) ∣
        (a - b) * (a + b + 1)
    exact
      nearestQPowerResidueAt_even_eq_implies_period_dvd_product
        q a b hq hqEven hba heq
  have hperiodEq :
      nearestQEvenResiduePeriod q =
        2 * nearestQEvenResidueHalfPeriod q := by
    symm
    exact
      two_mul_nearestQEvenResidueHalfPeriod
        q hq hqEven
  rcases
      nearestQIndexDifference_or_sum_not_two_dvd
        a b hba.le with
    hdiffOdd | hsumOdd
  · have hcoprimeTwo :
        Nat.Coprime 2 (a - b) := by
      exact
        (Nat.prime_two.coprime_iff_not_dvd).2
          hdiffOdd
    have hcoprimePeriod :
        Nat.Coprime
          (nearestQEvenResiduePeriod q)
          (a - b) := by
      unfold nearestQEvenResiduePeriod
      exact
        hcoprimeTwo.pow_left
          (q - 1 - nearestQTwoAdicOrder q)
    have hdvdSum :
        nearestQEvenResiduePeriod q ∣
          a + b + 1 := by
      exact
        hcoprimePeriod.dvd_of_dvd_mul_left
          hproduct
    have hsumPos :
        0 < a + b + 1 := by
      omega
    have hperiodLe :
        nearestQEvenResiduePeriod q ≤
          a + b + 1 :=
      Nat.le_of_dvd hsumPos hdvdSum
    have hsumLt :
        a + b + 1 <
          nearestQEvenResiduePeriod q := by
      rw [hperiodEq]
      omega
    omega
  · have hcoprimeTwo :
        Nat.Coprime 2 (a + b + 1) := by
      exact
        (Nat.prime_two.coprime_iff_not_dvd).2
          hsumOdd
    have hcoprimePeriod :
        Nat.Coprime
          (nearestQEvenResiduePeriod q)
          (a + b + 1) := by
      unfold nearestQEvenResiduePeriod
      exact
        hcoprimeTwo.pow_left
          (q - 1 - nearestQTwoAdicOrder q)
    have hproductComm :
        nearestQEvenResiduePeriod q ∣
          (a + b + 1) * (a - b) := by
      simpa [Nat.mul_comm] using hproduct
    have hdvdDiff :
        nearestQEvenResiduePeriod q ∣
          a - b := by
      exact
        hcoprimePeriod.dvd_of_dvd_mul_left
          hproductComm
    have hdiffPos :
        0 < a - b := by
      omega
    have hperiodLe :
        nearestQEvenResiduePeriod q ≤
          a - b :=
      Nat.le_of_dvd hdiffPos hdvdDiff
    have hdiffLt :
        a - b <
          nearestQEvenResiduePeriod q := by
      rw [hperiodEq]
      omega
    omega

/--
For even `q ≥ 6`, the power-residue map is injective
on the first predicted half-period.-/
theorem nearestQPowerResidueAt_even_injOn_halfPeriod
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Set.InjOn
      (nearestQPowerResidueAt q)
      (↑(Finset.range
        (nearestQEvenResidueHalfPeriod q)) : Set Nat) := by
  intro a ha b hb heq
  have haLt :
      a < nearestQEvenResidueHalfPeriod q := by
    simpa using ha
  have hbLt :
      b < nearestQEvenResidueHalfPeriod q := by
    simpa using hb
  by_contra hne
  by_cases hba :
      b < a
  · exact
      (nearestQPowerResidueAt_even_ne_of_lt_halfPeriod
        q a b
        hq hqEven
        haLt hbLt
        hba)
        heq
  · have hab :
        a < b := by
      omega
    exact
      (nearestQPowerResidueAt_even_ne_of_lt_halfPeriod
        q b a
        hq hqEven
        hbLt haLt
        hab)
        heq.symm

/--
For even `q ≥ 6`, the actual odd q-th power residue
image has exactly the predicted number of elements.-/
theorem nearestQOddResidueImage_card_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (nearestQOddResidueImage q).card =
      nearestQResidueImageSize q := by
  classical
  have hqPos :
      0 < q := by
    omega
  have hhalfLe :
      nearestQEvenResidueHalfPeriod q ≤
        nearestQResiduePeriod q := by
    unfold nearestQEvenResidueHalfPeriod
    rw [nearestQResiduePeriod_eq]
    exact
      Nat.le_of_dvd
        (by positivity)
        (Nat.pow_dvd_pow
          2
          (by omega))
  have hsmallCard :
      ((Finset.range
          (nearestQEvenResidueHalfPeriod q)).image
        (nearestQPowerResidueAt q)).card =
        nearestQEvenResidueHalfPeriod q := by
    calc
      ((Finset.range
            (nearestQEvenResidueHalfPeriod q)).image
          (nearestQPowerResidueAt q)).card =
          (Finset.range
            (nearestQEvenResidueHalfPeriod q)).card := by
        exact
          Finset.card_image_iff.mpr
            (nearestQPowerResidueAt_even_injOn_halfPeriod
              q hq hqEven)
      _ = nearestQEvenResidueHalfPeriod q := by
        exact Finset.card_range _
  have hsmallSubset :
      (Finset.range
          (nearestQEvenResidueHalfPeriod q)).image
          (nearestQPowerResidueAt q) ⊆
        nearestQOddResidueImage q := by
    unfold nearestQOddResidueImage
    intro y hy
    rw [Finset.mem_image] at hy ⊢
    rcases hy with
      ⟨r, hr, hry⟩
    refine
      ⟨r, ?_, hry⟩
    rw [Finset.mem_range] at hr ⊢
    exact
      lt_of_lt_of_le
        hr
        hhalfLe
  have hlower :
      nearestQEvenResidueHalfPeriod q ≤
        (nearestQOddResidueImage q).card := by
    rw [← hsmallCard]
    exact
      Finset.card_le_card
        hsmallSubset
  have hupper :
      (nearestQOddResidueImage q).card ≤
        nearestQEvenResidueHalfPeriod q := by
    simpa [
      nearestQResidueImageSize_eq_evenHalfPeriod
        q hq hqEven
    ] using
      nearestQOddResidueImage_card_le
        q hqPos
  rw [
    nearestQResidueImageSize_eq_evenHalfPeriod
      q hq hqEven
  ]
  exact
    Nat.le_antisymm
      hupper
      hlower

/--
For even `q ≥ 6`, the actual image of the odd q-th
power map is exactly the predicted arithmetic progression.-/
theorem nearestQOddResidueImage_eq_predicted_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQOddResidueImage q =
      nearestQPredictedResidueImage q := by
  apply
    Finset.eq_of_subset_of_card_le
  · exact
      nearestQOddResidueImage_subset_predicted
        q
        (by omega)
  · rw [
      nearestQPredictedResidueImage_card,
      nearestQOddResidueImage_card_of_even_ge_six
        q hq hqEven
    ]

/--
For every positive even `q`, the actual odd q-th power
residue image is exactly the predicted arithmetic progression.-/
theorem nearestQOddResidueImage_eq_predicted_of_even
    (q : Nat)
    (hq : 0 < q)
    (hqEven : Even q) :
    nearestQOddResidueImage q =
      nearestQPredictedResidueImage q := by
  classical
  by_cases hqSix :
      6 ≤ q
  · exact
      nearestQOddResidueImage_eq_predicted_of_even_ge_six
        q hqSix hqEven
  · have hqCases :
        q = 2 ∨ q = 4 := by
      rcases hqEven with ⟨k, hk⟩
      omega
    rcases hqCases with hqTwo | hqFour
    · subst q
      have hstep :
          nearestQResidueStepExponent 2 = 2 := by
        rw [
          nearestQResidueStepExponent_of_not_odd
            2
            (by norm_num)
        ]
        apply Nat.min_eq_left
        omega
      have hsize :
          nearestQResidueImageSize 2 = 1 := by
        unfold nearestQResidueImageSize
        rw [hstep]
        norm_num
      have hactual :
          nearestQOddResidueImage 2 = {1} := by
        ext y
        constructor
        · intro hy
          rw [Finset.mem_singleton]
          rcases
              (mem_nearestQOddResidueImage_iff
                2 y).1 hy with
            ⟨r, _hr, hry⟩
          rw [nearestQPowerResidueAt_two] at hry
          omega
        · intro hy
          rw [Finset.mem_singleton] at hy
          subst y
          apply
            (mem_nearestQOddResidueImage_iff
              2 1).2
          refine ⟨0, ?_, ?_⟩
          · rw [nearestQResiduePeriod_eq]
            norm_num
          · exact
              nearestQPowerResidueAt_two 0
      have hpredicted :
          nearestQPredictedResidueImage 2 = {1} := by
        ext y
        constructor
        · intro hy
          rw [Finset.mem_singleton]
          rcases
              (mem_nearestQPredictedResidueImage_iff
                2 y).1 hy with
            ⟨j, hj, hjy⟩
          rw [hsize] at hj
          have hjZero :
              j = 0 := by
            omega
          subst j
          simp [hstep] at hjy
          omega
        · intro hy
          rw [Finset.mem_singleton] at hy
          subst y
          apply
            (mem_nearestQPredictedResidueImage_iff
              2 1).2
          refine ⟨0, ?_, ?_⟩
          · rw [hsize]
            norm_num
          · simp
      exact
        hactual.trans
          hpredicted.symm
    · subst q
      have hvaluation :
          2 ≤ nearestQTwoAdicOrder 4 := by
        unfold nearestQTwoAdicOrder
        exact
          (padicValNat_dvd_iff_le
            (by norm_num : (4 : Nat) ≠ 0)).1
            (by norm_num :
              2 ^ 2 ∣ (4 : Nat))
      have hstep :
          nearestQResidueStepExponent 4 = 4 := by
        rw [
          nearestQResidueStepExponent_of_not_odd
            4
            (by norm_num)
        ]
        apply Nat.min_eq_left
        omega
      have hsize :
          nearestQResidueImageSize 4 = 1 := by
        unfold nearestQResidueImageSize
        rw [hstep]
        norm_num
      have hactual :
          nearestQOddResidueImage 4 = {1} := by
        ext y
        constructor
        · intro hy
          rw [Finset.mem_singleton]
          rcases
              (mem_nearestQOddResidueImage_iff
                4 y).1 hy with
            ⟨r, _hr, hry⟩
          rw [nearestQPowerResidueAt_four] at hry
          omega
        · intro hy
          rw [Finset.mem_singleton] at hy
          subst y
          apply
            (mem_nearestQOddResidueImage_iff
              4 1).2
          refine ⟨0, ?_, ?_⟩
          · rw [nearestQResiduePeriod_eq]
            norm_num
          · exact
              nearestQPowerResidueAt_four 0
      have hpredicted :
          nearestQPredictedResidueImage 4 = {1} := by
        ext y
        constructor
        · intro hy
          rw [Finset.mem_singleton]
          rcases
              (mem_nearestQPredictedResidueImage_iff
                4 y).1 hy with
            ⟨j, hj, hjy⟩
          rw [hsize] at hj
          have hjZero :
              j = 0 := by
            omega
          subst j
          simp [hstep] at hjy
          omega
        · intro hy
          rw [Finset.mem_singleton] at hy
          subst y
          apply
            (mem_nearestQPredictedResidueImage_iff
              4 1).2
          refine ⟨0, ?_, ?_⟩
          · rw [hsize]
            norm_num
          · simp
      exact
        hactual.trans
          hpredicted.symm

/--
For every positive exponent `q`, the actual image of the
odd q-th power map is exactly the predicted arithmetic
progression.-/
theorem nearestQOddResidueImage_eq_predicted
    (q : Nat)
    (hq : 0 < q) :
    nearestQOddResidueImage q =
      nearestQPredictedResidueImage q := by
  by_cases hqOdd :
      Odd q
  · exact
      nearestQOddResidueImage_eq_predicted_of_odd
        q hq hqOdd
  · have hqEven :
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
    exact
      nearestQOddResidueImage_eq_predicted_of_even
        q hq hqEven

/--
For every positive `q`, a natural number belongs to the
odd q-th power residue image precisely when it has the form

`1 + 2^d_q * j`

with `j < 2^(q - d_q)`.-/
theorem mem_nearestQOddResidueImage_iff_predictedParam
    (q y : Nat)
    (hq : 0 < q) :
    y ∈ nearestQOddResidueImage q ↔
      ∃ j : Nat,
        j < nearestQResidueImageSize q ∧
        1 +
            2 ^ nearestQResidueStepExponent q * j =
          y := by
  rw [
    nearestQOddResidueImage_eq_predicted
      q hq
  ]
  exact
    mem_nearestQPredictedResidueImage_iff
      q y

/--
The sum of all distinct odd q-th power residues
modulo `2^q`.-/
def nearestQOddResidueSum
    (q : Nat) : Nat :=
  Finset.sum
    (nearestQOddResidueImage q)
    (fun y => y)

/--
For positive `q`, the sum of the actual residue image
equals the sum over the predicted arithmetic progression.-/
theorem nearestQOddResidueSum_eq_predictedImageSum
    (q : Nat)
    (hq : 0 < q) :
    nearestQOddResidueSum q =
      Finset.sum
        (nearestQPredictedResidueImage q)
        (fun y => y) := by
  unfold nearestQOddResidueSum
  rw [
    nearestQOddResidueImage_eq_predicted
      q hq
  ]

/--
For positive `q`, the sum of all distinct residues is the
sum of the predicted arithmetic progression indexed by

`0 ≤ j < 2^(q - d_q)`.-/
theorem nearestQOddResidueSum_eq_paramSum
    (q : Nat)
    (hq : 0 < q) :
    nearestQOddResidueSum q =
      Finset.sum
        (Finset.range
          (nearestQResidueImageSize q))
        (fun j =>
          1 +
            2 ^ nearestQResidueStepExponent q * j) := by
  rw [
    nearestQOddResidueSum_eq_predictedImageSum
      q hq
  ]
  unfold nearestQPredictedResidueImage
  rw [Finset.sum_image]
  intro a _ha b _hb hab
  exact
    nearestQPredictedResidueParam_injective
      q hab

/--
The sum of the predicted arithmetic progression splits
into its constant part and its linear part.-/
theorem nearestQPredictedParamSum_split
    (q : Nat) :
    Finset.sum
        (Finset.range
          (nearestQResidueImageSize q))
        (fun j =>
          1 +
            2 ^ nearestQResidueStepExponent q * j) =
      nearestQResidueImageSize q +
        2 ^ nearestQResidueStepExponent q *
          Finset.sum
            (Finset.range
              (nearestQResidueImageSize q))
            (fun j => j) := by
  generalize hN :
      nearestQResidueImageSize q = N
  clear hN
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [
        Finset.sum_range_succ,
        Finset.sum_range_succ,
        ih,
        Nat.mul_add
      ]
      omega

/--
Twice the sum of the natural numbers in `range N` is

`N * (N - 1)`.-/
theorem two_mul_sum_range_id
    (N : Nat) :
    2 *
        Finset.sum
          (Finset.range N)
          (fun j => j) =
      N * (N - 1) := by
  simpa [Nat.mul_comm] using
    (Finset.sum_range_id_mul_two N)

/--
For positive `q`, twice the sum of all distinct odd
q-th power residues is

`N_q * (2 + 2^d_q * (N_q - 1))`.-/
theorem two_mul_nearestQOddResidueSum
    (q : Nat)
    (hq : 0 < q) :
    2 * nearestQOddResidueSum q =
      nearestQResidueImageSize q *
        (2 +
          2 ^ nearestQResidueStepExponent q *
            (nearestQResidueImageSize q - 1)) := by
  calc
    2 * nearestQOddResidueSum q =
        2 *
          (nearestQResidueImageSize q +
            2 ^ nearestQResidueStepExponent q *
              Finset.sum
                (Finset.range
                  (nearestQResidueImageSize q))
                (fun j => j)) := by
      rw [
        nearestQOddResidueSum_eq_paramSum
          q hq,
        nearestQPredictedParamSum_split
          q
      ]
    _ =
        2 * nearestQResidueImageSize q +
          2 ^ nearestQResidueStepExponent q *
            (2 *
              Finset.sum
                (Finset.range
                  (nearestQResidueImageSize q))
                (fun j => j)) := by
      ring
    _ =
        2 * nearestQResidueImageSize q +
          2 ^ nearestQResidueStepExponent q *
            (nearestQResidueImageSize q *
              (nearestQResidueImageSize q - 1)) := by
      rw [
        two_mul_sum_range_id
          (nearestQResidueImageSize q)
      ]
    _ =
        nearestQResidueImageSize q *
          (2 +
            2 ^ nearestQResidueStepExponent q *
              (nearestQResidueImageSize q - 1)) := by
      ring

/--
The mean of all distinct odd q-th power residues
modulo `2^q`.-/
def nearestQOddResidueMean
    (q : Nat) : Rat :=
  (nearestQOddResidueSum q : Rat) /
    (nearestQResidueImageSize q : Rat)

/--
For positive `q`, twice the mean residue is

`2 + 2^d_q * (N_q - 1)`.-/
theorem two_mul_nearestQOddResidueMean
    (q : Nat)
    (hq : 0 < q) :
    2 * nearestQOddResidueMean q =
      ((2 +
          2 ^ nearestQResidueStepExponent q *
            (nearestQResidueImageSize q - 1) :
        Nat) : Rat) := by
  have hsizePos :
      0 < nearestQResidueImageSize q :=
    nearestQResidueImageSize_pos q
  have hsizeNe :
      (nearestQResidueImageSize q : Rat) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt hsizePos)
  have hcast :
      (2 : Rat) *
          (nearestQOddResidueSum q : Rat) =
        (nearestQResidueImageSize q : Rat) *
          ((2 +
              2 ^ nearestQResidueStepExponent q *
                (nearestQResidueImageSize q - 1) :
            Nat) : Rat) := by
    exact_mod_cast
      (two_mul_nearestQOddResidueSum
        q hq)
  unfold nearestQOddResidueMean
  rw [← mul_div_assoc]
  apply
    (div_eq_iff hsizeNe).2
  simpa [mul_comm] using hcast

/--
For positive `q`, the mean of the distinct odd q-th
power residues is

`(2 + 2^d_q * (N_q - 1)) / 2`.-/
theorem nearestQOddResidueMean_eq
    (q : Nat)
    (hq : 0 < q) :
    nearestQOddResidueMean q =
      ((2 +
          2 ^ nearestQResidueStepExponent q *
            (nearestQResidueImageSize q - 1) :
        Nat) : Rat) / 2 := by
  apply
    (eq_div_iff
      (by norm_num : (2 : Rat) ≠ 0)).2
  simpa [mul_comm] using
    (two_mul_nearestQOddResidueMean
      q hq)
/--
The step of the predicted residue progression multiplied by
the number of its elements is exactly the full modulus `2^q`.-/
theorem nearestQStepPow_mul_imageSize
    (q : Nat) :
    2 ^ nearestQResidueStepExponent q *
        nearestQResidueImageSize q =
      2 ^ q := by
  unfold nearestQResidueImageSize
  rw [← pow_add]
  congr 1
  have hle :
      nearestQResidueStepExponent q ≤ q :=
    nearestQResidueStepExponent_le q
  omega

/--
The mean correction obtained from the mean of the distinct
odd q-th power residues.-/
def nearestQOmegaMean
    (q : Nat) : Rat :=
  1 -
    nearestQOddResidueMean q /
      ((2 : Rat) ^ q)

/--
For positive `q`, the mean correction is obtained by
substituting the explicit residue-mean formula.-/
theorem nearestQOmegaMean_eq_paramFormula
    (q : Nat)
    (hq : 0 < q) :
    nearestQOmegaMean q =
      1 -
        (((2 +
              2 ^ nearestQResidueStepExponent q *
                (nearestQResidueImageSize q - 1) :
            Nat) : Rat) / 2) /
          ((2 : Rat) ^ q) := by
  unfold nearestQOmegaMean
  rw [
    nearestQOddResidueMean_eq
      q hq
  ]

/--
Over the rationals, the step of the predicted progression
multiplied by its size equals the full modulus.-/
theorem nearestQStepPow_mul_imageSize_cast
    (q : Nat) :
    ((2 : Rat) ^ nearestQResidueStepExponent q) *
        (nearestQResidueImageSize q : Rat) =
      (2 : Rat) ^ q := by
  exact_mod_cast
    (nearestQStepPow_mul_imageSize q)

/--
For every positive `q`, the mean correction is

`1 / 2 + (2^d_q - 2) / 2^(q + 1)`.-/
theorem nearestQOmegaMean_eq_closed
    (q : Nat)
    (hq : 0 < q) :
    nearestQOmegaMean q =
      (1 : Rat) / 2 +
        (((2 : Rat) ^
              nearestQResidueStepExponent q -
            2) /
          ((2 : Rat) ^ (q + 1))) := by
  have hsizePos :
      0 < nearestQResidueImageSize q :=
    nearestQResidueImageSize_pos q
  have hsizeOne :
      1 ≤ nearestQResidueImageSize q := by
    omega
  have hsubCast :
      ((nearestQResidueImageSize q - 1 : Nat) : Rat) =
        (nearestQResidueImageSize q : Rat) - 1 := by
    have hnat :
        nearestQResidueImageSize q - 1 + 1 =
          nearestQResidueImageSize q :=
      Nat.sub_add_cancel hsizeOne
    have hrat :
        ((nearestQResidueImageSize q - 1 : Nat) : Rat) +
            1 =
          (nearestQResidueImageSize q : Rat) := by
      exact_mod_cast hnat
    linarith
  have hnumCast :
      ((2 +
            2 ^ nearestQResidueStepExponent q *
              (nearestQResidueImageSize q - 1) :
          Nat) : Rat) =
        2 +
          (2 : Rat) ^
              nearestQResidueStepExponent q *
            ((nearestQResidueImageSize q : Rat) - 1) := by
    push_cast
    rw [hsubCast]
  have hproduct :
      ((2 : Rat) ^
            nearestQResidueStepExponent q) *
          (nearestQResidueImageSize q : Rat) =
        (2 : Rat) ^ q :=
    nearestQStepPow_mul_imageSize_cast q
  have hpowNe :
      (2 : Rat) ^ q ≠ 0 := by
    positivity
  have hpowSucc :
      (2 : Rat) ^ (q + 1) =
        (2 : Rat) ^ q * 2 := by
    rw [pow_succ]
  rw [
    nearestQOmegaMean_eq_paramFormula
      q hq,
    hnumCast,
    hpowSucc
  ]
  field_simp [hpowNe]
  nlinarith [hproduct]

/--
For every positive odd `q`, the mean correction is exactly
one half.-/
theorem nearestQOmegaMean_of_odd
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    nearestQOmegaMean q =
      (1 : Rat) / 2 := by
  rw [
    nearestQOmegaMean_eq_closed
      q hq,
    nearestQResidueStepExponent_of_odd
      q hqOdd
  ]
  norm_num

/--
For every even `q ≥ 6`, the mean correction is

`1 / 2 + (2^(ν₂(q) + 2) - 2) / 2^(q + 1)`.-/
theorem nearestQOmegaMean_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQOmegaMean q =
      (1 : Rat) / 2 +
        (((2 : Rat) ^
              (nearestQTwoAdicOrder q + 2) -
            2) /
          ((2 : Rat) ^ (q + 1))) := by
  rw [
    nearestQOmegaMean_eq_closed
      q
      (by omega),
    nearestQResidueStepExponent_of_even_ge_six
      q hq hqEven
  ]

/--
For `q = 2`, the mean correction is `3 / 4`.-/
theorem nearestQOmegaMean_two :
    nearestQOmegaMean 2 =
      (3 : Rat) / 4 := by
  have hstep :
      nearestQResidueStepExponent 2 = 2 := by
    rw [
      nearestQResidueStepExponent_of_not_odd
        2
        (by norm_num)
    ]
    apply Nat.min_eq_left
    omega
  rw [
    nearestQOmegaMean_eq_closed
      2
      (by norm_num),
    hstep
  ]
  norm_num

/--
For `q = 4`, the mean correction is `15 / 16`.-/
theorem nearestQOmegaMean_four :
    nearestQOmegaMean 4 =
      (15 : Rat) / 16 := by
  have hvaluation :
      2 ≤ nearestQTwoAdicOrder 4 := by
    unfold nearestQTwoAdicOrder
    exact
      (padicValNat_dvd_iff_le
        (by norm_num : (4 : Nat) ≠ 0)).1
        (by norm_num :
          2 ^ 2 ∣ (4 : Nat))
  have hstep :
      nearestQResidueStepExponent 4 = 4 := by
    rw [
      nearestQResidueStepExponent_of_not_odd
        4
        (by norm_num)
    ]
    apply Nat.min_eq_left
    omega
  rw [
    nearestQOmegaMean_eq_closed
      4
      (by norm_num),
    hstep
  ]
  norm_num

/--
The mean of the power-residue sequence over its exact
least positive period.-/
def nearestQPowerResidueExactPeriodMean
    (q : Nat) : Rat :=
  Finset.sum
      (Finset.range
        (nearestQExactPeriod q))
      (fun r =>
        (nearestQPowerResidueAt q r : Rat)) /
    (nearestQExactPeriod q : Rat)

/--
The mean of the correction sequence over its exact
least positive period.-/
def nearestQOmegaExactPeriodMean
    (q : Nat) : Rat :=
  Finset.sum
      (Finset.range
        (nearestQExactPeriod q))
      (fun r =>
        nearestQOmegaAt q r) /
    (nearestQExactPeriod q : Rat)

/--
For every positive `q`, the exact period is positive.-/
theorem nearestQExactPeriod_pos
    (q : Nat)
    (hq : 0 < q) :
    0 < nearestQExactPeriod q := by
  exact
    (nearestQPowerResidueAt_isLeastPeriod
      q hq).1

/--
For positive `q`, the mean correction over the exact period is

`1 - residueMean / 2^q`.-/
theorem nearestQOmegaExactPeriodMean_eq
    (q : Nat)
    (hq : 0 < q) :
    nearestQOmegaExactPeriodMean q =
      1 -
        nearestQPowerResidueExactPeriodMean q /
          ((2 : Rat) ^ q) := by
  have hsum :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            nearestQOmegaAt q r) =
        (nearestQExactPeriod q : Rat) -
          Finset.sum
              (Finset.range
                (nearestQExactPeriod q))
              (fun r =>
                (nearestQPowerResidueAt q r : Rat)) /
            ((2 : Rat) ^ q) := by
    generalize hP :
        nearestQExactPeriod q = P
    clear hP
    induction P with
    | zero =>
        simp
    | succ P ih =>
        rw [
          Finset.sum_range_succ,
          Finset.sum_range_succ,
          ih
        ]
        unfold nearestQOmegaAt
        push_cast
        ring
  have hperiodNe :
      (nearestQExactPeriod q : Rat) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        (nearestQExactPeriod_pos q hq))
  have hpowNe :
      (2 : Rat) ^ q ≠ 0 := by
    positivity
  unfold
    nearestQOmegaExactPeriodMean
    nearestQPowerResidueExactPeriodMean
  rw [hsum]
  field_simp [hperiodNe, hpowNe]

/--
For odd `q`, the number of distinct odd q-th power residues
equals the odd-case residue period.-/
theorem nearestQResidueImageSize_eq_residuePeriod_of_odd
    (q : Nat)
    (hqOdd : Odd q) :
    nearestQResidueImageSize q =
      nearestQResiduePeriod q := by
  unfold nearestQResidueImageSize
  rw [
    nearestQResidueStepExponent_of_odd
      q hqOdd,
    nearestQResiduePeriod_eq
  ]

/--
For positive odd `q`, every distinct residue occurs exactly
once during the exact period. Hence the period mean equals
the mean of the residue image.-/
theorem nearestQPowerResidueExactPeriodMean_of_odd
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    nearestQPowerResidueExactPeriodMean q =
      nearestQOddResidueMean q := by
  classical
  have hExceptional :
      ¬(q = 2 ∨ q = 4) := by
    intro h
    rcases h with hqTwo | hqFour
    · subst q
      norm_num at hqOdd
    · subst q
      norm_num at hqOdd
  have hperiod :
      nearestQExactPeriod q =
        nearestQResiduePeriod q := by
    unfold nearestQExactPeriod
    rw [
      ite_eq_right hExceptional,
      ite_eq_left hqOdd
    ]
  have hsumNat :
      Finset.sum
          (Finset.range
            (nearestQResiduePeriod q))
          (fun r =>
            nearestQPowerResidueAt q r) =
        nearestQOddResidueSum q := by
    unfold
      nearestQOddResidueSum
      nearestQOddResidueImage
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact
      (nearestQPowerResidueAt_odd_injOn_range
        q hq hqOdd)
        ha hb hab
  have hsumRat :
      Finset.sum
          (Finset.range
            (nearestQResiduePeriod q))
          (fun r =>
            (nearestQPowerResidueAt q r : Rat)) =
        (nearestQOddResidueSum q : Rat) := by
    simpa using
      congrArg
        (fun n : Nat => (n : Rat))
        hsumNat
  unfold
    nearestQPowerResidueExactPeriodMean
    nearestQOddResidueMean
  rw [
    hperiod,
    hsumRat,
    nearestQResidueImageSize_eq_residuePeriod_of_odd
      q hqOdd
  ]

/--
For every positive odd `q`, the mean of the correction
sequence over its exact least positive period is exactly
one half.-/
theorem nearestQOmegaExactPeriodMean_of_odd
    (q : Nat)
    (hq : 0 < q)
    (hqOdd : Odd q) :
    nearestQOmegaExactPeriodMean q =
      (1 : Rat) / 2 := by
  calc
    nearestQOmegaExactPeriodMean q =
        1 -
          nearestQOddResidueMean q /
            ((2 : Rat) ^ q) := by
      rw [
        nearestQOmegaExactPeriodMean_eq
          q hq,
        nearestQPowerResidueExactPeriodMean_of_odd
          q hq hqOdd
      ]
    _ = nearestQOmegaMean q := by
      rfl
    _ = (1 : Rat) / 2 := by
      exact
        nearestQOmegaMean_of_odd
          q hq hqOdd

/--
For the exceptional exponents `q = 2` and `q = 4`,
the mean over the exact period agrees with the mean
of the distinct residue image.-/
theorem nearestQOmegaExactPeriodMean_of_exceptional
    (q : Nat)
    (hExceptional :
      q = 2 ∨ q = 4) :
    nearestQOmegaExactPeriodMean q =
      nearestQOmegaMean q := by
  rcases hExceptional with hqTwo | hqFour
  · subst q
    rw [nearestQOmegaMean_two]
    norm_num [
      nearestQOmegaExactPeriodMean,
      nearestQExactPeriod,
      nearestQOmegaAt,
      nearestQPowerResidueAt_two
    ]
  · subst q
    rw [nearestQOmegaMean_four]
    norm_num [
      nearestQOmegaExactPeriodMean,
      nearestQExactPeriod,
      nearestQOmegaAt,
      nearestQPowerResidueAt_four
    ]

/--
For even `q ≥ 6`, two distinct indices in the second half
of the exact period cannot have the same q-th power residue.-/
theorem nearestQPowerResidueAt_even_ne_of_secondHalf
    (q a b : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q)
    (_haLower :
      nearestQEvenResidueHalfPeriod q ≤ a)
    (hbLower :
      nearestQEvenResidueHalfPeriod q ≤ b)
    (haUpper :
      a < nearestQEvenResiduePeriod q)
    (hbUpper :
      b < nearestQEvenResiduePeriod q)
    (hba : b < a) :
    nearestQPowerResidueAt q a ≠
      nearestQPowerResidueAt q b := by
  intro heq
  have hproduct :
      nearestQEvenResiduePeriod q ∣
        (a - b) * (a + b + 1) := by
    change
      2 ^ (q - 1 - nearestQTwoAdicOrder q) ∣
        (a - b) * (a + b + 1)
    exact
      nearestQPowerResidueAt_even_eq_implies_period_dvd_product
        q a b hq hqEven hba heq
  have hperiodEq :
      nearestQEvenResiduePeriod q =
        2 * nearestQEvenResidueHalfPeriod q := by
    symm
    exact
      two_mul_nearestQEvenResidueHalfPeriod
        q hq hqEven
  have hperiodPos :
      0 < nearestQEvenResiduePeriod q := by
    unfold nearestQEvenResiduePeriod
    positivity
  rcases
      nearestQIndexDifference_or_sum_not_two_dvd
        a b hba.le with
    hdiffOdd | hsumOdd
  · have hcoprimeTwo :
        Nat.Coprime 2 (a - b) := by
      exact
        (Nat.prime_two.coprime_iff_not_dvd).2
          hdiffOdd
    have hcoprimePeriod :
        Nat.Coprime
          (nearestQEvenResiduePeriod q)
          (a - b) := by
      unfold nearestQEvenResiduePeriod
      exact
        hcoprimeTwo.pow_left
          (q - 1 - nearestQTwoAdicOrder q)
    have hdvdSum :
        nearestQEvenResiduePeriod q ∣
          a + b + 1 := by
      exact
        hcoprimePeriod.dvd_of_dvd_mul_left
          hproduct
    have hsumLower :
        nearestQEvenResiduePeriod q <
          a + b + 1 := by
      rw [hperiodEq]
      omega
    have hsumUpper :
        a + b + 1 <
          2 * nearestQEvenResiduePeriod q := by
      omega
    obtain ⟨k, hk⟩ := hdvdSum
    have hkPos :
        0 < k := by
      by_contra hkNotPos
      have hkZero :
          k = 0 := by
        omega
      subst k
      simp at hk
    have hkLtTwo :
        k < 2 := by
      have hmulLt :
          nearestQEvenResiduePeriod q * k <
            nearestQEvenResiduePeriod q * 2 := by
        calc
          nearestQEvenResiduePeriod q * k =
              a + b + 1 := hk.symm
          _ <
              2 * nearestQEvenResiduePeriod q :=
            hsumUpper
          _ =
              nearestQEvenResiduePeriod q * 2 := by
            omega
      exact
        (Nat.mul_lt_mul_left hperiodPos).mp
          hmulLt
    have hkOne :
        k = 1 := by
      omega
    have hsumEq :
        a + b + 1 =
          nearestQEvenResiduePeriod q := by
      simpa [hkOne] using hk
    omega
  · have hcoprimeTwo :
        Nat.Coprime 2 (a + b + 1) := by
      exact
        (Nat.prime_two.coprime_iff_not_dvd).2
          hsumOdd
    have hcoprimePeriod :
        Nat.Coprime
          (nearestQEvenResiduePeriod q)
          (a + b + 1) := by
      unfold nearestQEvenResiduePeriod
      exact
        hcoprimeTwo.pow_left
          (q - 1 - nearestQTwoAdicOrder q)
    have hproductComm :
        nearestQEvenResiduePeriod q ∣
          (a + b + 1) * (a - b) := by
      simpa [Nat.mul_comm] using hproduct
    have hdvdDiff :
        nearestQEvenResiduePeriod q ∣
          a - b := by
      exact
        hcoprimePeriod.dvd_of_dvd_mul_left
          hproductComm
    have hdiffPos :
        0 < a - b := by
      omega
    have hperiodLe :
        nearestQEvenResiduePeriod q ≤
          a - b :=
      Nat.le_of_dvd hdiffPos hdvdDiff
    have hdiffLt :
        a - b <
          nearestQEvenResiduePeriod q := by
      omega
    omega

/--
For even `q ≥ 6`, the power-residue map is injective
on the second half of its exact period.-/
theorem nearestQPowerResidueAt_even_injOn_secondHalf
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Set.InjOn
      (nearestQPowerResidueAt q)
      (↑(Finset.Ico
        (nearestQEvenResidueHalfPeriod q)
        (nearestQEvenResiduePeriod q)) : Set Nat) := by
  intro a ha b hb heq
  have haBounds :
      nearestQEvenResidueHalfPeriod q ≤ a ∧
        a < nearestQEvenResiduePeriod q := by
    exact Finset.mem_Ico.mp ha
  have hbBounds :
      nearestQEvenResidueHalfPeriod q ≤ b ∧
        b < nearestQEvenResiduePeriod q := by
    exact Finset.mem_Ico.mp hb
  by_contra hne
  by_cases hba :
      b < a
  · exact
      (nearestQPowerResidueAt_even_ne_of_secondHalf
        q a b
        hq hqEven
        haBounds.1 hbBounds.1
        haBounds.2 hbBounds.2
        hba)
        heq
  · have hab :
        a < b := by
      omega
    exact
      (nearestQPowerResidueAt_even_ne_of_secondHalf
        q b a
        hq hqEven
        hbBounds.1 haBounds.1
        hbBounds.2 haBounds.2
        hab)
        heq.symm

/--
For even `q ≥ 6`, the first half of the exact period
visits every distinct odd q-th power residue exactly once.-/
theorem nearestQPowerResidueFirstHalfImage_eq
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (Finset.range
        (nearestQEvenResidueHalfPeriod q)).image
        (nearestQPowerResidueAt q) =
      nearestQOddResidueImage q := by
  classical
  have hhalfLe :
      nearestQEvenResidueHalfPeriod q ≤
        nearestQResiduePeriod q := by
    unfold nearestQEvenResidueHalfPeriod
    rw [nearestQResiduePeriod_eq]
    exact
      Nat.le_of_dvd
        (by positivity)
        (Nat.pow_dvd_pow
          2
          (by omega))
  have himageCard :
      ((Finset.range
          (nearestQEvenResidueHalfPeriod q)).image
          (nearestQPowerResidueAt q)).card =
        nearestQEvenResidueHalfPeriod q := by
    calc
      ((Finset.range
            (nearestQEvenResidueHalfPeriod q)).image
            (nearestQPowerResidueAt q)).card =
          (Finset.range
            (nearestQEvenResidueHalfPeriod q)).card := by
        exact
          Finset.card_image_iff.mpr
            (nearestQPowerResidueAt_even_injOn_halfPeriod
              q hq hqEven)
      _ = nearestQEvenResidueHalfPeriod q := by
        exact Finset.card_range _
  apply Finset.eq_of_subset_of_card_le
  · unfold nearestQOddResidueImage
    intro y hy
    rw [Finset.mem_image] at hy ⊢
    rcases hy with ⟨r, hr, hry⟩
    refine ⟨r, ?_, hry⟩
    rw [Finset.mem_range] at hr ⊢
    exact
      lt_of_lt_of_le
        hr
        hhalfLe
  · rw [
      nearestQOddResidueImage_card_of_even_ge_six
        q hq hqEven,
      nearestQResidueImageSize_eq_evenHalfPeriod
        q hq hqEven,
      himageCard
    ]

/--
For even `q ≥ 6`, the second half of the exact period
also visits every distinct odd q-th power residue exactly once.-/
theorem nearestQPowerResidueSecondHalfImage_eq
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    (Finset.Ico
        (nearestQEvenResidueHalfPeriod q)
        (nearestQEvenResiduePeriod q)).image
        (nearestQPowerResidueAt q) =
      nearestQOddResidueImage q := by
  classical
  have hperiodLe :
      nearestQEvenResiduePeriod q ≤
        nearestQResiduePeriod q := by
    unfold nearestQEvenResiduePeriod
    rw [nearestQResiduePeriod_eq]
    exact
      Nat.le_of_dvd
        (by positivity)
        (Nat.pow_dvd_pow
          2
          (by omega))
  have hperiodEq :
      nearestQEvenResiduePeriod q =
        2 * nearestQEvenResidueHalfPeriod q := by
    symm
    exact
      two_mul_nearestQEvenResidueHalfPeriod
        q hq hqEven
  have hIcoCard :
      (Finset.Ico
          (nearestQEvenResidueHalfPeriod q)
          (nearestQEvenResiduePeriod q)).card =
        nearestQEvenResidueHalfPeriod q := by
    rw [Nat.card_Ico, hperiodEq]
    omega
  have himageCard :
      ((Finset.Ico
          (nearestQEvenResidueHalfPeriod q)
          (nearestQEvenResiduePeriod q)).image
          (nearestQPowerResidueAt q)).card =
        nearestQEvenResidueHalfPeriod q := by
    calc
      ((Finset.Ico
            (nearestQEvenResidueHalfPeriod q)
            (nearestQEvenResiduePeriod q)).image
            (nearestQPowerResidueAt q)).card =
          (Finset.Ico
            (nearestQEvenResidueHalfPeriod q)
            (nearestQEvenResiduePeriod q)).card := by
        exact
          Finset.card_image_iff.mpr
            (nearestQPowerResidueAt_even_injOn_secondHalf
              q hq hqEven)
      _ = nearestQEvenResidueHalfPeriod q :=
        hIcoCard
  apply Finset.eq_of_subset_of_card_le
  · unfold nearestQOddResidueImage
    intro y hy
    rw [Finset.mem_image] at hy ⊢
    rcases hy with ⟨r, hr, hry⟩
    refine ⟨r, ?_, hry⟩
    have hrBounds :
        nearestQEvenResidueHalfPeriod q ≤ r ∧
          r < nearestQEvenResiduePeriod q :=
      Finset.mem_Ico.mp hr
    rw [Finset.mem_range]
    exact
      lt_of_lt_of_le
        hrBounds.2
        hperiodLe
  · rw [
      nearestQOddResidueImage_card_of_even_ge_six
        q hq hqEven,
      nearestQResidueImageSize_eq_evenHalfPeriod
        q hq hqEven,
      himageCard
    ]

/--
For even `q ≥ 6`, the sum of the power residues over the
first half of the exact period equals the sum of all
distinct residues.-/
theorem nearestQPowerResidueFirstHalfSum_eq
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (Finset.range
          (nearestQEvenResidueHalfPeriod q))
        (fun r =>
          nearestQPowerResidueAt q r) =
      nearestQOddResidueSum q := by
  unfold nearestQOddResidueSum
  rw [
    ← nearestQPowerResidueFirstHalfImage_eq
      q hq hqEven
  ]
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact
    (nearestQPowerResidueAt_even_injOn_halfPeriod
      q hq hqEven)
      ha hb hab

/--
For even `q ≥ 6`, the sum of the power residues over the
second half of the exact period also equals the sum of all
distinct residues.-/
theorem nearestQPowerResidueSecondHalfSum_eq
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (Finset.Ico
          (nearestQEvenResidueHalfPeriod q)
          (nearestQEvenResiduePeriod q))
        (fun r =>
          nearestQPowerResidueAt q r) =
      nearestQOddResidueSum q := by
  unfold nearestQOddResidueSum
  rw [
    ← nearestQPowerResidueSecondHalfImage_eq
      q hq hqEven
  ]
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact
    (nearestQPowerResidueAt_even_injOn_secondHalf
      q hq hqEven)
      ha hb hab

/--
For every even `q ≥ 6`, the exact least positive period is
the previously defined even-case residue period.-/
theorem nearestQExactPeriod_eq_evenResiduePeriod_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQExactPeriod q =
      nearestQEvenResiduePeriod q := by
  have hExceptional :
      ¬(q = 2 ∨ q = 4) := by
    omega
  have hNotOdd :
      ¬Odd q := by
    intro hqOdd
    obtain ⟨a, ha⟩ := hqEven
    obtain ⟨b, hb⟩ := hqOdd
    omega
  unfold nearestQExactPeriod
  rw [
    ite_eq_right hExceptional,
    ite_eq_right hNotOdd
  ]

/--
For even `q ≥ 6`, the sum of the power residues over the
full exact period is twice the sum of the distinct residues.-/
theorem nearestQPowerResidueExactPeriodSum_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun r =>
          nearestQPowerResidueAt q r) =
      2 * nearestQOddResidueSum q := by
  classical
  rw [
    nearestQExactPeriod_eq_evenResiduePeriod_of_even_ge_six
      q hq hqEven
  ]
  have hperiodEq :
      nearestQEvenResiduePeriod q =
        2 * nearestQEvenResidueHalfPeriod q := by
    symm
    exact
      two_mul_nearestQEvenResidueHalfPeriod
        q hq hqEven
  have hdisjoint :
      Disjoint
        (Finset.range
          (nearestQEvenResidueHalfPeriod q))
        (Finset.Ico
          (nearestQEvenResidueHalfPeriod q)
          (nearestQEvenResiduePeriod q)) := by
    rw [Finset.disjoint_left]
    intro r hrange hIco
    rw [Finset.mem_range] at hrange
    have hbounds :
        nearestQEvenResidueHalfPeriod q ≤ r ∧
          r < nearestQEvenResiduePeriod q :=
      Finset.mem_Ico.mp hIco
    omega
  have hunion :
      Finset.range
          (nearestQEvenResidueHalfPeriod q) ∪
        Finset.Ico
          (nearestQEvenResidueHalfPeriod q)
          (nearestQEvenResiduePeriod q) =
      Finset.range
        (nearestQEvenResiduePeriod q) := by
    ext r
    simp only [
      Finset.mem_union,
      Finset.mem_range,
      Finset.mem_Ico
    ]
    omega
  calc
    Finset.sum
        (Finset.range
          (nearestQEvenResiduePeriod q))
        (fun r =>
          nearestQPowerResidueAt q r) =
      Finset.sum
        (Finset.range
            (nearestQEvenResidueHalfPeriod q) ∪
          Finset.Ico
            (nearestQEvenResidueHalfPeriod q)
            (nearestQEvenResiduePeriod q))
        (fun r =>
          nearestQPowerResidueAt q r) := by
      rw [hunion]
    _ =
      Finset.sum
          (Finset.range
            (nearestQEvenResidueHalfPeriod q))
          (fun r =>
            nearestQPowerResidueAt q r) +
        Finset.sum
          (Finset.Ico
            (nearestQEvenResidueHalfPeriod q)
            (nearestQEvenResiduePeriod q))
          (fun r =>
            nearestQPowerResidueAt q r) := by
      exact Finset.sum_union hdisjoint
    _ =
      nearestQOddResidueSum q +
        nearestQOddResidueSum q := by
      rw [
        nearestQPowerResidueFirstHalfSum_eq
          q hq hqEven,
        nearestQPowerResidueSecondHalfSum_eq
          q hq hqEven
      ]
    _ =
      2 * nearestQOddResidueSum q := by
      omega

/--
For even `q ≥ 6`, every distinct odd q-th power residue
occurs exactly twice during the exact period. Hence the
period mean equals the mean of the distinct residue image.-/
theorem nearestQPowerResidueExactPeriodMean_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQPowerResidueExactPeriodMean q =
      nearestQOddResidueMean q := by
  have hhalfPos :
      0 < nearestQEvenResidueHalfPeriod q := by
    rw [
      ← nearestQResidueImageSize_eq_evenHalfPeriod
        q hq hqEven
    ]
    exact
      nearestQResidueImageSize_pos q
  have hhalfNe :
      (nearestQEvenResidueHalfPeriod q : Rat) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt hhalfPos)
  have hperiodEq :
      nearestQEvenResiduePeriod q =
        2 * nearestQEvenResidueHalfPeriod q := by
    symm
    exact
      two_mul_nearestQEvenResidueHalfPeriod
        q hq hqEven
  have hsumNat :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            nearestQPowerResidueAt q r) =
        2 * nearestQOddResidueSum q :=
    nearestQPowerResidueExactPeriodSum_of_even_ge_six
      q hq hqEven
  have hsumRat :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQPowerResidueAt q r : Rat)) =
        ((2 * nearestQOddResidueSum q : Nat) : Rat) := by
    exact_mod_cast hsumNat
  unfold
    nearestQPowerResidueExactPeriodMean
    nearestQOddResidueMean
  rw [
    hsumRat,
    nearestQExactPeriod_eq_evenResiduePeriod_of_even_ge_six
      q hq hqEven,
    nearestQResidueImageSize_eq_evenHalfPeriod
      q hq hqEven,
    hperiodEq
  ]
  push_cast
  field_simp [hhalfNe]

/--
For even `q ≥ 6`, the mean of the correction sequence
over its exact period equals the correction mean obtained
from the distinct residue image.-/
theorem nearestQOmegaExactPeriodMean_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQOmegaExactPeriodMean q =
      nearestQOmegaMean q := by
  rw [
    nearestQOmegaExactPeriodMean_eq
      q
      (by omega),
    nearestQPowerResidueExactPeriodMean_of_even_ge_six
      q hq hqEven
  ]
  rfl

/--
For every positive `q`, the mean of the correction sequence
over its exact least positive period agrees with the mean
obtained from the distinct residue image.-/
theorem nearestQOmegaExactPeriodMean_eq_omegaMean
    (q : Nat)
    (hq : 0 < q) :
    nearestQOmegaExactPeriodMean q =
      nearestQOmegaMean q := by
  by_cases hExceptional :
      q = 2 ∨ q = 4
  · exact
      nearestQOmegaExactPeriodMean_of_exceptional
        q hExceptional
  · by_cases hqOdd :
        Odd q
    · calc
        nearestQOmegaExactPeriodMean q =
            (1 : Rat) / 2 := by
          exact
            nearestQOmegaExactPeriodMean_of_odd
              q hq hqOdd
        _ = nearestQOmegaMean q := by
          symm
          exact
            nearestQOmegaMean_of_odd
              q hq hqOdd
    · have hqEven :
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
        exact
          hExceptional
            (Or.inl h)
      have hqNeFour :
          q ≠ 4 := by
        intro h
        exact
          hExceptional
            (Or.inr h)
      have hqSix :
          6 ≤ q := by
        obtain ⟨k, hk⟩ := hqEven
        omega
      exact
        nearestQOmegaExactPeriodMean_of_even_ge_six
          q hqSix hqEven

/--
For every positive `q`, the mean correction over the exact
least positive period is

`1 / 2 + (2^d_q - 2) / 2^(q + 1)`.-/
theorem nearestQOmegaExactPeriodMean_eq_closed
    (q : Nat)
    (hq : 0 < q) :
    nearestQOmegaExactPeriodMean q =
      (1 : Rat) / 2 +
        (((2 : Rat) ^
              nearestQResidueStepExponent q -
            2) /
          ((2 : Rat) ^ (q + 1))) := by
  rw [
    nearestQOmegaExactPeriodMean_eq_omegaMean
      q hq,
    nearestQOmegaMean_eq_closed
      q hq
  ]

/--
For `q = 2`, the mean correction over the exact least
positive period is `3 / 4`.-/
theorem nearestQOmegaExactPeriodMean_two :
    nearestQOmegaExactPeriodMean 2 =
      (3 : Rat) / 4 := by
  rw [
    nearestQOmegaExactPeriodMean_eq_omegaMean
      2
      (by norm_num),
    nearestQOmegaMean_two
  ]

/--
For `q = 4`, the mean correction over the exact least
positive period is `15 / 16`.-/
theorem nearestQOmegaExactPeriodMean_four :
    nearestQOmegaExactPeriodMean 4 =
      (15 : Rat) / 16 := by
  rw [
    nearestQOmegaExactPeriodMean_eq_omegaMean
      4
      (by norm_num),
    nearestQOmegaMean_four
  ]

/--
For every even `q ≥ 6`, the mean correction over the exact
least positive period is

`1 / 2 + (2^(ν₂(q) + 2) - 2) / 2^(q + 1)`.-/
theorem nearestQOmegaExactPeriodMean_closed_of_even_ge_six
    (q : Nat)
    (hq : 6 ≤ q)
    (hqEven : Even q) :
    nearestQOmegaExactPeriodMean q =
      (1 : Rat) / 2 +
        (((2 : Rat) ^
              (nearestQTwoAdicOrder q + 2) -
            2) /
          ((2 : Rat) ^ (q + 1))) := by
  rw [
    nearestQOmegaExactPeriodMean_of_even_ge_six
      q hq hqEven,
    nearestQOmegaMean_of_even_ge_six
      q hq hqEven
  ]

/--
The explicit piecewise formula for the mean correction over
the exact least positive period.-/
def nearestQOmegaExactPeriodMeanFormula
    (q : Nat) : Rat :=
  if q = 2 then
    (3 : Rat) / 4
  else if q = 4 then
    (15 : Rat) / 16
  else if Odd q then
    (1 : Rat) / 2
  else
    (1 : Rat) / 2 +
      (((2 : Rat) ^
            (nearestQTwoAdicOrder q + 2) -
          2) /
        ((2 : Rat) ^ (q + 1)))

/--
For every positive exponent `q`, the exact-period mean
correction is given by the explicit piecewise formula.-/
theorem nearestQOmegaExactPeriodMean_eq_formula
    (q : Nat)
    (hq : 0 < q) :
    nearestQOmegaExactPeriodMean q =
      nearestQOmegaExactPeriodMeanFormula q := by
  unfold nearestQOmegaExactPeriodMeanFormula
  by_cases hqTwo :
      q = 2
  · rw [ite_eq_left hqTwo]
    subst q
    exact nearestQOmegaExactPeriodMean_two
  · rw [ite_eq_right hqTwo]
    by_cases hqFour :
        q = 4
    · rw [ite_eq_left hqFour]
      subst q
      exact nearestQOmegaExactPeriodMean_four
    · rw [ite_eq_right hqFour]
      by_cases hqOdd :
          Odd q
      · rw [ite_eq_left hqOdd]
        exact
          nearestQOmegaExactPeriodMean_of_odd
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
        have hqSix :
            6 ≤ q := by
          obtain ⟨k, hk⟩ := hqEven
          omega
        exact
          nearestQOmegaExactPeriodMean_closed_of_even_ge_six
            q hqSix hqEven

/--
For every positive exponent `q`, `nearestQExactPeriod q`
is the exact least positive period of the correction sequence,
and its mean over that period has the closed form

`1 / 2 + (2^d_q - 2) / 2^(q + 1)`.-/
theorem nearestQOmegaAt_exactPeriod_and_closedMean
    (q : Nat)
    (hq : 0 < q) :
    IsLeastPositiveNatPeriod
        (nearestQOmegaAt q)
        (nearestQExactPeriod q) ∧
      nearestQOmegaExactPeriodMean q =
        (1 : Rat) / 2 +
          (((2 : Rat) ^
                nearestQResidueStepExponent q -
              2) /
            ((2 : Rat) ^ (q + 1))) := by
  constructor
  · exact
      nearestQOmegaAt_isLeastPeriod
        q hq
  · exact
      nearestQOmegaExactPeriodMean_eq_closed
        q hq

/--
The complete nearest-root residue result for every positive
exponent `q`:

* the correction sequence has the exact period
  `nearestQExactPeriod q`;
* the odd q-th power residue image is the predicted
  arithmetic progression;
* the exact-period mean is given by the explicit
  piecewise formula.-/
theorem nearestQNearestRootMainTheorem
    (q : Nat)
    (hq : 0 < q) :
    IsLeastPositiveNatPeriod
        (nearestQOmegaAt q)
        (nearestQExactPeriod q) ∧
      nearestQOddResidueImage q =
        nearestQPredictedResidueImage q ∧
      nearestQOmegaExactPeriodMean q =
        nearestQOmegaExactPeriodMeanFormula q := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      nearestQOmegaAt_isLeastPeriod
        q hq
  · exact
      nearestQOddResidueImage_eq_predicted
        q hq
  · exact
      nearestQOmegaExactPeriodMean_eq_formula
        q hq

end RoundedRootSums
