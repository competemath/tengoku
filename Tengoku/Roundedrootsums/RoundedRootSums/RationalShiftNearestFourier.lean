/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftNearestAntiderivative
import Tengoku.Seed.Analysis.Complex.Exponential
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite Fourier expansion of nearest-root corrections

This file develops the exact finite Fourier description of
the centered nearest-root correction sequence and its
periodic antiderivative.
-/

namespace RoundedRootSums

/--
The primitive complex root used for the discrete Fourier
expansion over the exact period.-/
noncomputable def nearestQFourierRoot
    (q : Nat) : ℂ :=
  Complex.exp
    ((((2 : ℂ) * (Real.pi : ℂ)) * Complex.I) /
      (nearestQExactPeriod q : ℂ))

/--
The Fourier root is nonzero.-/
theorem nearestQFourierRoot_ne_zero
    (q : Nat) :
    nearestQFourierRoot q ≠ 0 := by
  unfold nearestQFourierRoot
  exact Complex.exp_ne_zero _

/--
The discrete Fourier coefficient of the centered correction
sequence.

The index `r` corresponds to the article's index `m = r + 1`,
so the Fourier phase is `ζ^(-ℓ(r+1))`.-/
noncomputable def nearestQCenteredOmegaFourierCoeff
    (q ell : Nat) : ℂ :=
  (1 / (nearestQExactPeriod q : ℂ)) *
    Finset.sum
      (Finset.range
        (nearestQExactPeriod q))
      (fun r =>
        (nearestQCenteredOmegaAt q r : ℂ) *
          ((nearestQFourierRoot q)⁻¹) ^
            (ell * (r + 1)))

/--
The zeroth Fourier coefficient of the centered correction
sequence vanishes.-/
theorem nearestQCenteredOmegaFourierCoeff_zero
    (q : Nat)
    (hq : 0 < q) :
    nearestQCenteredOmegaFourierCoeff q 0 = 0 := by
  have hsumRat :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            nearestQCenteredOmegaAt q r) =
        0 :=
    nearestQCenteredOmegaAt_exactPeriod_sum_zero
      q hq
  have hsumComplex :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (nearestQCenteredOmegaAt q r : ℂ)) =
        0 := by
    exact_mod_cast hsumRat
  unfold nearestQCenteredOmegaFourierCoeff
  simp only [
    zero_mul,
    pow_zero,
    mul_one
  ]
  rw [hsumComplex]
  ring

/--
For every positive `q`, the Fourier root is a primitive
`nearestQExactPeriod q`-th root of unity.-/
theorem nearestQFourierRoot_isPrimitiveRoot
    (q : Nat)
    (hq : 0 < q) :
    IsPrimitiveRoot
      (nearestQFourierRoot q)
      (nearestQExactPeriod q) := by
  unfold nearestQFourierRoot
  simpa only using
    Complex.isPrimitiveRoot_exp
      (nearestQExactPeriod q)
      (Nat.ne_of_gt
        (nearestQExactPeriod_pos q hq))

/--
The Fourier root raised to the exact period is one.-/
theorem nearestQFourierRoot_pow_exactPeriod
    (q : Nat)
    (hq : 0 < q) :
    nearestQFourierRoot q ^
        nearestQExactPeriod q =
      1 := by
  exact
    (nearestQFourierRoot_isPrimitiveRoot
      q hq).pow_eq_one

/--
For every frequency `ell`, the Fourier phase
`ζ_q^(ell * t)` is periodic with period
`nearestQExactPeriod q`.-/
theorem nearestQFourierPower_periodic
    (q ell : Nat)
    (hq : 0 < q) :
    Function.Periodic
      (fun t =>
        nearestQFourierRoot q ^ (ell * t))
      (nearestQExactPeriod q) := by
  have hperiodPower :
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
  intro t
  change
    nearestQFourierRoot q ^
        (ell *
          (t + nearestQExactPeriod q)) =
      nearestQFourierRoot q ^ (ell * t)
  rw [
    Nat.mul_add,
    pow_add,
    hperiodPower,
    mul_one
  ]

/--
For every positive `q`, the inverse Fourier root is also a
primitive `nearestQExactPeriod q`-th root of unity.-/
theorem nearestQFourierRoot_inv_isPrimitiveRoot
    (q : Nat)
    (hq : 0 < q) :
    IsPrimitiveRoot
      ((nearestQFourierRoot q)⁻¹)
      (nearestQExactPeriod q) := by
  exact
    (nearestQFourierRoot_isPrimitiveRoot
      q hq).inv

/--
The inverse Fourier root raised to the exact period is one.-/
theorem nearestQFourierRoot_inv_pow_exactPeriod
    (q : Nat)
    (hq : 0 < q) :
    ((nearestQFourierRoot q)⁻¹) ^
        nearestQExactPeriod q =
      1 := by
  exact
    (nearestQFourierRoot_inv_isPrimitiveRoot
      q hq).pow_eq_one

/--
For every frequency strictly between zero and the exact
period, the corresponding full-period Fourier phase sum
vanishes.-/
theorem nearestQFourierInversePower_sum_zero
    (q ell : Nat)
    (hq : 0 < q)
    (hellPos : 0 < ell)
    (hellLt :
      ell < nearestQExactPeriod q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun r =>
          ((nearestQFourierRoot q)⁻¹) ^
            (ell * r)) =
      0 := by
  have hinvPrimitive :
      IsPrimitiveRoot
        ((nearestQFourierRoot q)⁻¹)
        (nearestQExactPeriod q) :=
    nearestQFourierRoot_inv_isPrimitiveRoot
      q hq
  have hbaseNe :
      ((nearestQFourierRoot q)⁻¹) ^ ell ≠
        1 := by
    exact
      hinvPrimitive.pow_ne_one_of_pos_of_lt
        (Nat.ne_of_gt hellPos)
        hellLt
  have hbasePow :
      ((((nearestQFourierRoot q)⁻¹) ^ ell) ^
          nearestQExactPeriod q) =
        1 := by
    rw [
      ← pow_mul,
      Nat.mul_comm
        ell
        (nearestQExactPeriod q),
      pow_mul,
      nearestQFourierRoot_inv_pow_exactPeriod
        q hq,
      one_pow
    ]
  have honeSubNe :
      (1 : ℂ) -
          ((nearestQFourierRoot q)⁻¹) ^ ell ≠
        0 := by
    exact
      sub_ne_zero.mpr hbaseNe.symm
  have hgeom :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            (((nearestQFourierRoot q)⁻¹) ^ ell) ^ r) =
        0 := by
    refine
      eq_zero_of_ne_zero_of_mul_left_eq_zero
        honeSubNe
        ?_
    rw [
      mul_neg_geom_sum,
      hbasePow,
      sub_self
    ]
  simpa only [pow_mul] using hgeom

/--
A strictly positive frequency below the exact period gives
a nontrivial power of the Fourier root.-/
theorem nearestQFourierRoot_pow_ne_one
    (q ell : Nat)
    (hq : 0 < q)
    (hellPos : 0 < ell)
    (hellLt :
      ell < nearestQExactPeriod q) :
    nearestQFourierRoot q ^ ell ≠ 1 := by
  exact
    (nearestQFourierRoot_isPrimitiveRoot
      q hq).pow_ne_one_of_pos_of_lt
        (Nat.ne_of_gt hellPos)
        hellLt

/--
For every nonzero frequency below the exact period, the
full-period sum of the shifted inverse Fourier phases
`ζ_q^(-ell * (r + 1))` vanishes.-/
theorem nearestQFourierInverseShiftedPower_sum_zero
    (q ell : Nat)
    (hq : 0 < q)
    (hellPos : 0 < ell)
    (hellLt :
      ell < nearestQExactPeriod q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun r =>
          ((nearestQFourierRoot q)⁻¹) ^
            (ell * (r + 1))) =
      0 := by
  have hbase :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            ((nearestQFourierRoot q)⁻¹) ^
              (ell * r)) =
        0 :=
    nearestQFourierInversePower_sum_zero
      q ell hq hellPos hellLt
  calc
    Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            ((nearestQFourierRoot q)⁻¹) ^
              (ell * (r + 1))) =
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            ((nearestQFourierRoot q)⁻¹) ^
                (ell * r) *
              ((nearestQFourierRoot q)⁻¹) ^ ell) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [
        Nat.mul_add,
        Nat.mul_one,
        pow_add
      ]
    _ =
        (Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            ((nearestQFourierRoot q)⁻¹) ^
              (ell * r))) *
          ((nearestQFourierRoot q)⁻¹) ^ ell := by
      rw [Finset.sum_mul]
    _ = 0 := by
      rw [hbase, zero_mul]

/--
The finite Fourier synthesis of the centered correction
sequence, with the zero frequency omitted.

The omission is legitimate because the zeroth Fourier
coefficient is zero.-/
noncomputable def nearestQCenteredOmegaFourierSeries
    (q t : Nat) : ℂ :=
  Finset.sum
    (Finset.Ico
      1
      (nearestQExactPeriod q))
    (fun ell =>
      nearestQCenteredOmegaFourierCoeff q ell *
        nearestQFourierRoot q ^
          (ell * (t + 1)))

/--
A Fourier phase multiplied by the corresponding inverse
phase is equal to one.-/
theorem nearestQFourierPhase_mul_inverse_same
    (q ell a : Nat) :
    ((nearestQFourierRoot q)⁻¹) ^ (ell * a) *
        nearestQFourierRoot q ^ (ell * a) =
      1 := by
  simp [nearestQFourierRoot_ne_zero]

/--
When the two phase indices coincide, the complete Fourier
phase sum equals the exact period.-/
theorem nearestQFourierPhase_same_sum
    (q a : Nat) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun ell =>
          ((nearestQFourierRoot q)⁻¹) ^ (ell * a) *
            nearestQFourierRoot q ^ (ell * a)) =
      (nearestQExactPeriod q : ℂ) := by
  calc
    Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            ((nearestQFourierRoot q)⁻¹) ^ (ell * a) *
              nearestQFourierRoot q ^ (ell * a)) =
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun _ell => (1 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro ell _hell
      exact
        nearestQFourierPhase_mul_inverse_same
          q ell a
    _ = (nearestQExactPeriod q : ℂ) := by
      simp

/--
The ratio between any two Fourier phases, raised to the
exact period, is equal to one.-/
theorem nearestQFourierPhaseRatio_pow_exactPeriod
    (q a b : Nat)
    (hq : 0 < q) :
    ((((nearestQFourierRoot q)⁻¹) ^ a *
          nearestQFourierRoot q ^ b) ^
        nearestQExactPeriod q) =
      1 := by
  have hinv :
      (((nearestQFourierRoot q)⁻¹) ^ a) ^
          nearestQExactPeriod q =
        1 := by
    rw [
      ← pow_mul,
      Nat.mul_comm
        a
        (nearestQExactPeriod q),
      pow_mul,
      nearestQFourierRoot_inv_pow_exactPeriod
        q hq,
      one_pow
    ]
  have hroot :
      (nearestQFourierRoot q ^ b) ^
          nearestQExactPeriod q =
        1 := by
    rw [
      ← pow_mul,
      Nat.mul_comm
        b
        (nearestQExactPeriod q),
      pow_mul,
      nearestQFourierRoot_pow_exactPeriod
        q hq,
      one_pow
    ]
  rw [
    mul_pow,
    hinv,
    hroot,
    one_mul
  ]

/--
For two distinct indices below the exact period, the ratio
of the corresponding Fourier phases is not equal to one.-/
theorem nearestQFourierPhaseRatio_ne_one
    (q a b : Nat)
    (hq : 0 < q)
    (ha :
      a < nearestQExactPeriod q)
    (hb :
      b < nearestQExactPeriod q)
    (hab : a ≠ b) :
    (nearestQFourierRoot q)⁻¹ ^ a *
        nearestQFourierRoot q ^ b ≠
      1 := by
  intro hratio
  have hzNe :
      nearestQFourierRoot q ≠ 0 :=
    nearestQFourierRoot_ne_zero q
  have hcancel :
      nearestQFourierRoot q ^ a *
          ((nearestQFourierRoot q)⁻¹ ^ a *
            nearestQFourierRoot q ^ b) =
        nearestQFourierRoot q ^ b := by
    calc
      nearestQFourierRoot q ^ a *
            ((nearestQFourierRoot q)⁻¹ ^ a *
              nearestQFourierRoot q ^ b) =
          (nearestQFourierRoot q ^ a *
              (nearestQFourierRoot q)⁻¹ ^ a) *
            nearestQFourierRoot q ^ b := by
        rw [← mul_assoc]
      _ =
          ((nearestQFourierRoot q *
              (nearestQFourierRoot q)⁻¹) ^ a) *
            nearestQFourierRoot q ^ b := by
        rw [← mul_pow]
      _ = nearestQFourierRoot q ^ b := by
        simp [hzNe]
  have hphase :
      nearestQFourierRoot q ^ b =
        nearestQFourierRoot q ^ a := by
    calc
      nearestQFourierRoot q ^ b =
          nearestQFourierRoot q ^ a *
            ((nearestQFourierRoot q)⁻¹ ^ a *
              nearestQFourierRoot q ^ b) :=
        hcancel.symm
      _ = nearestQFourierRoot q ^ a * 1 := by
        rw [hratio]
      _ = nearestQFourierRoot q ^ a := by
        rw [mul_one]
  have habEq :
      a = b :=
    (nearestQFourierRoot_isPrimitiveRoot
      q hq).pow_inj
        ha hb hphase.symm
  exact hab habEq

/--
When two indices below the exact period are distinct, their
complete Fourier phase pairing sums to zero.-/
theorem nearestQFourierPhase_different_sum
    (q a b : Nat)
    (hq : 0 < q)
    (ha :
      a < nearestQExactPeriod q)
    (hb :
      b < nearestQExactPeriod q)
    (hab : a ≠ b) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun ell =>
          (nearestQFourierRoot q)⁻¹ ^ (ell * a) *
            nearestQFourierRoot q ^ (ell * b)) =
      0 := by
  have hbaseNe :
      (nearestQFourierRoot q)⁻¹ ^ a *
          nearestQFourierRoot q ^ b ≠
        1 :=
    nearestQFourierPhaseRatio_ne_one
      q a b hq ha hb hab
  have hbasePow :
      (((nearestQFourierRoot q)⁻¹ ^ a *
            nearestQFourierRoot q ^ b) ^
          nearestQExactPeriod q) =
        1 :=
    nearestQFourierPhaseRatio_pow_exactPeriod
      q a b hq
  have honeSubNe :
      (1 : ℂ) -
          ((nearestQFourierRoot q)⁻¹ ^ a *
            nearestQFourierRoot q ^ b) ≠
        0 := by
    exact sub_ne_zero.mpr hbaseNe.symm
  have hgeom :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            ((nearestQFourierRoot q)⁻¹ ^ a *
              nearestQFourierRoot q ^ b) ^ ell) =
        0 := by
    refine
      eq_zero_of_ne_zero_of_mul_left_eq_zero
        honeSubNe
        ?_
    rw [
      mul_neg_geom_sum,
      hbasePow,
      sub_self
    ]
  calc
    Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            (nearestQFourierRoot q)⁻¹ ^ (ell * a) *
              nearestQFourierRoot q ^ (ell * b)) =
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            ((nearestQFourierRoot q)⁻¹ ^ a *
              nearestQFourierRoot q ^ b) ^ ell) := by
      apply Finset.sum_congr rfl
      intro ell _hell
      rw [mul_pow]
      apply congrArg₂ (fun x y : ℂ => x * y)
      · calc
          (nearestQFourierRoot q)⁻¹ ^ (ell * a) =
              (nearestQFourierRoot q)⁻¹ ^ (a * ell) := by
            rw [Nat.mul_comm ell a]
          _ =
              ((nearestQFourierRoot q)⁻¹ ^ a) ^ ell :=
            pow_mul _ _ _
      · calc
          nearestQFourierRoot q ^ (ell * b) =
              nearestQFourierRoot q ^ (b * ell) := by
            rw [Nat.mul_comm ell b]
          _ =
              (nearestQFourierRoot q ^ b) ^ ell :=
            pow_mul _ _ _
    _ = 0 := hgeom

/--
The complete orthogonality relation for Fourier phases over
one exact period.-/
theorem nearestQFourierPhase_orthogonality
    (q a b : Nat)
    (hq : 0 < q)
    (ha :
      a < nearestQExactPeriod q)
    (hb :
      b < nearestQExactPeriod q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun ell =>
          (nearestQFourierRoot q)⁻¹ ^ (ell * a) *
            nearestQFourierRoot q ^ (ell * b)) =
      if a = b then
        (nearestQExactPeriod q : ℂ)
      else
        0 := by
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    exact nearestQFourierPhase_same_sum q a
  · rw [ite_eq_right hab]
    exact
      nearestQFourierPhase_different_sum
        q a b hq ha hb hab

/--
The common shift by one in the analysis and synthesis
Fourier phases cancels.-/
theorem nearestQFourierShiftedPhase_mul_eq
    (q ell r t : Nat) :
    ((nearestQFourierRoot q)⁻¹) ^
          (ell * (r + 1)) *
        nearestQFourierRoot q ^
          (ell * (t + 1)) =
      ((nearestQFourierRoot q)⁻¹) ^
          (ell * r) *
        nearestQFourierRoot q ^
          (ell * t) := by
  have hcancel :
      ((nearestQFourierRoot q)⁻¹) ^ ell *
          nearestQFourierRoot q ^ ell =
        1 := by
    simp [nearestQFourierRoot_ne_zero]
  rw [
    Nat.mul_add,
    Nat.mul_one,
    Nat.mul_add,
    Nat.mul_one,
    pow_add,
    pow_add
  ]
  calc
    ((nearestQFourierRoot q)⁻¹) ^ (ell * r) *
          ((nearestQFourierRoot q)⁻¹) ^ ell *
          (nearestQFourierRoot q ^ (ell * t) *
            nearestQFourierRoot q ^ ell) =
        (((nearestQFourierRoot q)⁻¹) ^ (ell * r) *
            nearestQFourierRoot q ^ (ell * t)) *
          (((nearestQFourierRoot q)⁻¹) ^ ell *
            nearestQFourierRoot q ^ ell) := by
      ring
    _ =
        ((nearestQFourierRoot q)⁻¹) ^ (ell * r) *
          nearestQFourierRoot q ^ (ell * t) := by
      rw [hcancel, mul_one]

/--
The shifted Fourier phases satisfy the same orthogonality
relation as the unshifted phases.-/
theorem nearestQFourierShiftedPhase_orthogonality
    (q r t : Nat)
    (hq : 0 < q)
    (hr :
      r < nearestQExactPeriod q)
    (ht :
      t < nearestQExactPeriod q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun ell =>
          ((nearestQFourierRoot q)⁻¹) ^
              (ell * (r + 1)) *
            nearestQFourierRoot q ^
              (ell * (t + 1))) =
      if r = t then
        (nearestQExactPeriod q : ℂ)
      else
        0 := by
  calc
    Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            ((nearestQFourierRoot q)⁻¹) ^
                (ell * (r + 1)) *
              nearestQFourierRoot q ^
                (ell * (t + 1))) =
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            ((nearestQFourierRoot q)⁻¹) ^
                (ell * r) *
              nearestQFourierRoot q ^
                (ell * t)) := by
      apply Finset.sum_congr rfl
      intro ell _hell
      exact
        nearestQFourierShiftedPhase_mul_eq
          q ell r t
    _ =
        if r = t then
          (nearestQExactPeriod q : ℂ)
        else
          0 :=
      nearestQFourierPhase_orthogonality
        q r t hq hr ht

/--
After multiplication by the centered correction at `r`,
the shifted phase sum selects precisely the term `r = t`.-/
theorem nearestQCenteredOmega_mul_shiftedPhase_sum
    (q r t : Nat)
    (hq : 0 < q)
    (hr :
      r < nearestQExactPeriod q)
    (ht :
      t < nearestQExactPeriod q) :
    Finset.sum
        (Finset.range
          (nearestQExactPeriod q))
        (fun ell =>
          (nearestQCenteredOmegaAt q r : ℂ) *
            ((nearestQFourierRoot q)⁻¹) ^
              (ell * (r + 1)) *
            nearestQFourierRoot q ^
              (ell * (t + 1))) =
      if r = t then
        (nearestQCenteredOmegaAt q r : ℂ) *
          (nearestQExactPeriod q : ℂ)
      else
        0 := by
  calc
    Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            (nearestQCenteredOmegaAt q r : ℂ) *
              ((nearestQFourierRoot q)⁻¹) ^
                (ell * (r + 1)) *
              nearestQFourierRoot q ^
                (ell * (t + 1))) =
        (nearestQCenteredOmegaAt q r : ℂ) *
          Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun ell =>
              ((nearestQFourierRoot q)⁻¹) ^
                  (ell * (r + 1)) *
                nearestQFourierRoot q ^
                  (ell * (t + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _hell
      ring
    _ =
        (nearestQCenteredOmegaAt q r : ℂ) *
          (if r = t then
            (nearestQExactPeriod q : ℂ)
          else
            0) := by
      rw [
        nearestQFourierShiftedPhase_orthogonality
          q r t hq hr ht
      ]
    _ =
        if r = t then
          (nearestQCenteredOmegaAt q r : ℂ) *
            (nearestQExactPeriod q : ℂ)
        else
          0 := by
      split_ifs <;> simp

/--
The full finite Fourier synthesis of the centered correction
sequence, including the zeroth frequency.-/
noncomputable def nearestQCenteredOmegaFullFourierSeries
    (q t : Nat) : ℂ :=
  Finset.sum
    (Finset.range
      (nearestQExactPeriod q))
    (fun ell =>
      nearestQCenteredOmegaFourierCoeff q ell *
        nearestQFourierRoot q ^
          (ell * (t + 1)))

/--
After expanding the Fourier coefficients and interchanging
the two finite sums, the full Fourier synthesis becomes a
scaled sum of the shifted phase pairings.-/
theorem nearestQCenteredOmegaFullFourierSeries_eq_scaledDoubleSum
    (q t : Nat) :
    nearestQCenteredOmegaFullFourierSeries q t =
      (1 / (nearestQExactPeriod q : ℂ)) *
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            Finset.sum
              (Finset.range
                (nearestQExactPeriod q))
              (fun ell =>
                (nearestQCenteredOmegaAt q r : ℂ) *
                  ((nearestQFourierRoot q)⁻¹) ^
                    (ell * (r + 1)) *
                  nearestQFourierRoot q ^
                    (ell * (t + 1)))) := by
  unfold nearestQCenteredOmegaFullFourierSeries
  unfold nearestQCenteredOmegaFourierCoeff
  calc
    Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            ((1 / (nearestQExactPeriod q : ℂ)) *
                Finset.sum
                  (Finset.range
                    (nearestQExactPeriod q))
                  (fun r =>
                    (nearestQCenteredOmegaAt q r : ℂ) *
                      ((nearestQFourierRoot q)⁻¹) ^
                        (ell * (r + 1)))) *
              nearestQFourierRoot q ^
                (ell * (t + 1))) =
        Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun ell =>
            (1 / (nearestQExactPeriod q : ℂ)) *
              (Finset.sum
                  (Finset.range
                    (nearestQExactPeriod q))
                  (fun r =>
                    (nearestQCenteredOmegaAt q r : ℂ) *
                      ((nearestQFourierRoot q)⁻¹) ^
                        (ell * (r + 1))) *
                nearestQFourierRoot q ^
                  (ell * (t + 1)))) := by
      apply Finset.sum_congr rfl
      intro ell _hell
      ring
    _ =
        (1 / (nearestQExactPeriod q : ℂ)) *
          Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun ell =>
              Finset.sum
                  (Finset.range
                    (nearestQExactPeriod q))
                  (fun r =>
                    (nearestQCenteredOmegaAt q r : ℂ) *
                      ((nearestQFourierRoot q)⁻¹) ^
                        (ell * (r + 1))) *
                nearestQFourierRoot q ^
                  (ell * (t + 1))) := by
      rw [Finset.mul_sum]
    _ =
        (1 / (nearestQExactPeriod q : ℂ)) *
          Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun ell =>
              Finset.sum
                (Finset.range
                  (nearestQExactPeriod q))
                (fun r =>
                  (nearestQCenteredOmegaAt q r : ℂ) *
                    ((nearestQFourierRoot q)⁻¹) ^
                      (ell * (r + 1)) *
                    nearestQFourierRoot q ^
                      (ell * (t + 1)))) := by
      apply congrArg
        (fun z : ℂ =>
          (1 / (nearestQExactPeriod q : ℂ)) * z)
      apply Finset.sum_congr rfl
      intro ell _hell
      rw [Finset.sum_mul]
    _ =
        (1 / (nearestQExactPeriod q : ℂ)) *
          Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun r =>
              Finset.sum
                (Finset.range
                  (nearestQExactPeriod q))
                (fun ell =>
                  (nearestQCenteredOmegaAt q r : ℂ) *
                    ((nearestQFourierRoot q)⁻¹) ^
                      (ell * (r + 1)) *
                    nearestQFourierRoot q ^
                      (ell * (t + 1)))) := by
      apply congrArg
        (fun z : ℂ =>
          (1 / (nearestQExactPeriod q : ℂ)) * z)
      rw [Finset.sum_comm]

/--
Inside the first exact period, the full finite Fourier
synthesis reconstructs the centered correction sequence
exactly.-/
theorem nearestQCenteredOmegaFullFourierSeries_eq
    (q t : Nat)
    (hq : 0 < q)
    (ht :
      t < nearestQExactPeriod q) :
    nearestQCenteredOmegaFullFourierSeries q t =
      (nearestQCenteredOmegaAt q t : ℂ) := by
  have hperiodNe :
      (nearestQExactPeriod q : ℂ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        (nearestQExactPeriod_pos q hq))
  have hdouble :
      Finset.sum
          (Finset.range
            (nearestQExactPeriod q))
          (fun r =>
            Finset.sum
              (Finset.range
                (nearestQExactPeriod q))
              (fun ell =>
                (nearestQCenteredOmegaAt q r : ℂ) *
                  ((nearestQFourierRoot q)⁻¹) ^
                    (ell * (r + 1)) *
                  nearestQFourierRoot q ^
                    (ell * (t + 1)))) =
        (nearestQCenteredOmegaAt q t : ℂ) *
          (nearestQExactPeriod q : ℂ) := by
    calc
      Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun r =>
              Finset.sum
                (Finset.range
                  (nearestQExactPeriod q))
                (fun ell =>
                  (nearestQCenteredOmegaAt q r : ℂ) *
                    ((nearestQFourierRoot q)⁻¹) ^
                      (ell * (r + 1)) *
                    nearestQFourierRoot q ^
                      (ell * (t + 1)))) =
          Finset.sum
            (Finset.range
              (nearestQExactPeriod q))
            (fun r =>
              if r = t then
                (nearestQCenteredOmegaAt q r : ℂ) *
                  (nearestQExactPeriod q : ℂ)
              else
                0) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact
          nearestQCenteredOmega_mul_shiftedPhase_sum
            q r t hq
            (Finset.mem_range.mp hr)
            ht
      _ =
          (nearestQCenteredOmegaAt q t : ℂ) *
            (nearestQExactPeriod q : ℂ) := by
        simp [ht]
  rw [
    nearestQCenteredOmegaFullFourierSeries_eq_scaledDoubleSum,
    hdouble
  ]
  field_simp [hperiodNe]

/--
For every positive `q`, the zeroth Fourier mode contributes
nothing, so the full Fourier synthesis equals the synthesis
over the nonzero frequencies.-/
theorem nearestQCenteredOmegaFullFourierSeries_eq_fourierSeries
    (q t : Nat)
    (hq : 0 < q) :
    nearestQCenteredOmegaFullFourierSeries q t =
      nearestQCenteredOmegaFourierSeries q t := by
  have hperiodPos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos q hq
  have hrange :
      Finset.range (nearestQExactPeriod q) =
        ({0} : Finset Nat) ∪
          Finset.Ico 1 (nearestQExactPeriod q) := by
    ext ell
    simp only [
      Finset.mem_range,
      Finset.mem_union,
      Finset.mem_singleton,
      Finset.mem_Ico
    ]
    omega
  have hdisjoint :
      Disjoint
        ({0} : Finset Nat)
        (Finset.Ico 1 (nearestQExactPeriod q)) := by
    refine Finset.disjoint_left.mpr ?_
    intro ell hellZero hellIco
    simp only [Finset.mem_singleton] at hellZero
    simp only [Finset.mem_Ico] at hellIco
    omega
  unfold
    nearestQCenteredOmegaFullFourierSeries
    nearestQCenteredOmegaFourierSeries
  rw [
    hrange,
    Finset.sum_union hdisjoint
  ]
  simp [
    nearestQCenteredOmegaFourierCoeff_zero
      q hq
  ]

/--
The nonzero-frequency Fourier synthesis is periodic with
period `nearestQExactPeriod q`.-/
theorem nearestQCenteredOmegaFourierSeries_periodic
    (q : Nat)
    (hq : 0 < q) :
    Function.Periodic
      (nearestQCenteredOmegaFourierSeries q)
      (nearestQExactPeriod q) := by
  intro t
  unfold nearestQCenteredOmegaFourierSeries
  apply Finset.sum_congr rfl
  intro ell _hell
  have hphase :
      nearestQFourierRoot q ^
          (ell *
            ((t + 1) +
              nearestQExactPeriod q)) =
        nearestQFourierRoot q ^
          (ell * (t + 1)) :=
    nearestQFourierPower_periodic
      q ell hq (t + 1)
  have hindex :
      (t + nearestQExactPeriod q) + 1 =
        (t + 1) + nearestQExactPeriod q := by
    omega
  rw [
    hindex,
    hphase
  ]

/--
For every positive `q` and every index `t`, the finite
Fourier synthesis over the nonzero frequencies reconstructs
the centered nearest-root correction exactly.-/
theorem nearestQCenteredOmegaFourierSeries_eq
    (q t : Nat)
    (hq : 0 < q) :
    nearestQCenteredOmegaFourierSeries q t =
      (nearestQCenteredOmegaAt q t : ℂ) := by
  have hperiodPos :
      0 < nearestQExactPeriod q :=
    nearestQExactPeriod_pos q hq
  have hmodLt :
      t % nearestQExactPeriod q <
        nearestQExactPeriod q :=
    Nat.mod_lt t hperiodPos
  calc
    nearestQCenteredOmegaFourierSeries q t =
        nearestQCenteredOmegaFourierSeries q
          (t % nearestQExactPeriod q) := by
      symm
      exact
        (nearestQCenteredOmegaFourierSeries_periodic
          q hq).map_mod_nat t
    _ =
        nearestQCenteredOmegaFullFourierSeries q
          (t % nearestQExactPeriod q) := by
      symm
      exact
        nearestQCenteredOmegaFullFourierSeries_eq_fourierSeries
          q
          (t % nearestQExactPeriod q)
          hq
    _ =
        (nearestQCenteredOmegaAt q
          (t % nearestQExactPeriod q) : ℂ) :=
      nearestQCenteredOmegaFullFourierSeries_eq
        q
        (t % nearestQExactPeriod q)
        hq
        hmodLt
    _ =
        (nearestQCenteredOmegaAt q t : ℂ) := by
      exact
        congrArg
          (fun x : Rat => (x : ℂ))
          (nearestQCenteredOmegaAt_mod_eq
            q t hq)

/--
For every nonzero Fourier frequency below the exact period,
the denominator `ζ_q^ell - 1` is nonzero.-/
theorem nearestQFourierRoot_pow_sub_one_ne_zero
    (q ell : Nat)
    (hq : 0 < q)
    (hellPos : 0 < ell)
    (hellLt :
      ell < nearestQExactPeriod q) :
    nearestQFourierRoot q ^ ell - 1 ≠ 0 := by
  exact
    sub_ne_zero.mpr
      (nearestQFourierRoot_pow_ne_one
        q ell hq hellPos hellLt)

/--
The Fourier coefficient of the periodic antiderivative.

For a nonzero frequency `ell`, division by
`ζ_q^ell - 1` inverts the forward-difference operator.-/
noncomputable def nearestQOmegaTildeFourierCoeff
    (q ell : Nat) : ℂ :=
  nearestQCenteredOmegaFourierCoeff q ell /
    (nearestQFourierRoot q ^ ell - 1)

/--
Multiplying an antiderivative Fourier coefficient by
`ζ_q^ell - 1` recovers the corresponding centered-correction
coefficient.-/
theorem nearestQOmegaTildeFourierCoeff_mul_sub
    (q ell : Nat)
    (hq : 0 < q)
    (hellPos : 0 < ell)
    (hellLt :
      ell < nearestQExactPeriod q) :
    nearestQOmegaTildeFourierCoeff q ell *
        (nearestQFourierRoot q ^ ell - 1) =
      nearestQCenteredOmegaFourierCoeff q ell := by
  unfold nearestQOmegaTildeFourierCoeff
  field_simp [
    nearestQFourierRoot_pow_sub_one_ne_zero
      q ell hq hellPos hellLt
  ]

/--
The normalized finite Fourier synthesis of the periodic
antiderivative.

The subtraction of `ζ_q^ell` normalizes the value at
`t = 0` to zero.-/
noncomputable def nearestQOmegaTildeFourierSeries
    (q t : Nat) : ℂ :=
  Finset.sum
    (Finset.Ico
      1
      (nearestQExactPeriod q))
    (fun ell =>
      nearestQOmegaTildeFourierCoeff q ell *
        (nearestQFourierRoot q ^
            (ell * (t + 1)) -
          nearestQFourierRoot q ^ ell))

/--
The normalized Fourier synthesis of the periodic
antiderivative vanishes at zero.-/
@[simp]
theorem nearestQOmegaTildeFourierSeries_zero
    (q : Nat) :
    nearestQOmegaTildeFourierSeries q 0 = 0 := by
  unfold nearestQOmegaTildeFourierSeries
  apply Finset.sum_eq_zero
  intro ell _hell
  simp

/--
For every nonzero Fourier frequency, the first difference
of the corresponding antiderivative term is the associated
centered-correction Fourier term.-/
theorem nearestQOmegaTildeFourierTerm_succ_sub
    (q ell t : Nat)
    (hq : 0 < q)
    (hellPos : 0 < ell)
    (hellLt :
      ell < nearestQExactPeriod q) :
    nearestQOmegaTildeFourierCoeff q ell *
          (nearestQFourierRoot q ^
                (ell * ((t + 1) + 1)) -
            nearestQFourierRoot q ^ ell) -
        nearestQOmegaTildeFourierCoeff q ell *
          (nearestQFourierRoot q ^
                (ell * (t + 1)) -
            nearestQFourierRoot q ^ ell) =
      nearestQCenteredOmegaFourierCoeff q ell *
        nearestQFourierRoot q ^
          (ell * (t + 1)) := by
  have hphase :
      nearestQFourierRoot q ^
          (ell * ((t + 1) + 1)) =
        nearestQFourierRoot q ^
            (ell * (t + 1)) *
          nearestQFourierRoot q ^ ell := by
    rw [
      Nat.mul_add,
      Nat.mul_one,
      pow_add
    ]
  have hcoeff :
      nearestQOmegaTildeFourierCoeff q ell *
          (nearestQFourierRoot q ^ ell - 1) =
        nearestQCenteredOmegaFourierCoeff q ell :=
    nearestQOmegaTildeFourierCoeff_mul_sub
      q ell hq hellPos hellLt
  rw [hphase]
  calc
    nearestQOmegaTildeFourierCoeff q ell *
            (nearestQFourierRoot q ^
                  (ell * (t + 1)) *
                nearestQFourierRoot q ^ ell -
              nearestQFourierRoot q ^ ell) -
          nearestQOmegaTildeFourierCoeff q ell *
            (nearestQFourierRoot q ^
                  (ell * (t + 1)) -
              nearestQFourierRoot q ^ ell) =
        (nearestQOmegaTildeFourierCoeff q ell *
            (nearestQFourierRoot q ^ ell - 1)) *
          nearestQFourierRoot q ^
            (ell * (t + 1)) := by
      ring
    _ =
        nearestQCenteredOmegaFourierCoeff q ell *
          nearestQFourierRoot q ^
            (ell * (t + 1)) := by
      rw [hcoeff]

/--
The first difference of the Fourier synthesis of the
periodic antiderivative is the Fourier synthesis of the
centered correction sequence.-/
theorem nearestQOmegaTildeFourierSeries_succ_sub_eq_centeredSeries
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeFourierSeries q (t + 1) -
        nearestQOmegaTildeFourierSeries q t =
      nearestQCenteredOmegaFourierSeries q t := by
  unfold
    nearestQOmegaTildeFourierSeries
    nearestQCenteredOmegaFourierSeries
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  have hellBounds :
      1 ≤ ell ∧
        ell < nearestQExactPeriod q :=
    Finset.mem_Ico.mp hell
  exact
    nearestQOmegaTildeFourierTerm_succ_sub
      q ell t hq
      (by omega)
      hellBounds.2

/--
The first difference of the Fourier antiderivative is
exactly the centered nearest-root correction sequence.-/
theorem nearestQOmegaTildeFourierSeries_succ_sub_eq_centeredOmega
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeFourierSeries q (t + 1) -
        nearestQOmegaTildeFourierSeries q t =
      (nearestQCenteredOmegaAt q t : ℂ) := by
  rw [
    nearestQOmegaTildeFourierSeries_succ_sub_eq_centeredSeries
      q t hq,
    nearestQCenteredOmegaFourierSeries_eq
      q t hq
  ]

/--
For every positive `q`, the normalized Fourier synthesis
coincides with the periodic antiderivative.-/
theorem nearestQOmegaTildeFourierSeries_eq_omegaTilde
    (q t : Nat)
    (hq : 0 < q) :
    nearestQOmegaTildeFourierSeries q t =
      (nearestQOmegaTildeAt q t : ℂ) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have hdiff :
          nearestQOmegaTildeFourierSeries q (t + 1) -
              nearestQOmegaTildeFourierSeries q t =
            (nearestQCenteredOmegaAt q t : ℂ) :=
        nearestQOmegaTildeFourierSeries_succ_sub_eq_centeredOmega
          q t hq
      calc
        nearestQOmegaTildeFourierSeries q (t + 1) =
            (nearestQOmegaTildeFourierSeries q (t + 1) -
                nearestQOmegaTildeFourierSeries q t) +
              nearestQOmegaTildeFourierSeries q t := by
          ring
        _ =
            (nearestQCenteredOmegaAt q t : ℂ) +
              nearestQOmegaTildeFourierSeries q t := by
          rw [hdiff]
        _ =
            (nearestQCenteredOmegaAt q t : ℂ) +
              (nearestQOmegaTildeAt q t : ℂ) := by
          rw [ih]
        _ =
            ((nearestQOmegaTildeAt q t +
                nearestQCenteredOmegaAt q t : Rat) : ℂ) := by
          push_cast
          ring
        _ =
            (nearestQOmegaTildeAt q (t + 1) : ℂ) := by
          rw [
            ← nearestQOmegaTildeAt_succ
              q t hq
          ]

/--
The exact finite Fourier expansion of the periodic
antiderivative:

`Ω̃_q(t) =
  ∑_{1 ≤ ell < P_q}
    ω̂_q(ell) / (ζ_q^ell - 1) *
      (ζ_q^(ell * (t + 1)) - ζ_q^ell)`.-/
theorem nearestQOmegaTildeAt_eq_fourierFormula
    (q t : Nat)
    (hq : 0 < q) :
    (nearestQOmegaTildeAt q t : ℂ) =
      Finset.sum
        (Finset.Ico
          1
          (nearestQExactPeriod q))
        (fun ell =>
          nearestQOmegaTildeFourierCoeff q ell *
            (nearestQFourierRoot q ^
                (ell * (t + 1)) -
              nearestQFourierRoot q ^ ell)) := by
  simpa [nearestQOmegaTildeFourierSeries] using
    (nearestQOmegaTildeFourierSeries_eq_omegaTilde
      q t hq).symm

/--
The complete finite Fourier result for every positive
exponent `q`:

* the centered correction has an exact finite Fourier
  expansion over the nonzero frequencies;
* the periodic antiderivative has the corresponding
  normalized Fourier expansion;
* multiplication by `ζ_q^ell - 1` recovers the Fourier
  coefficient of the centered correction.-/
theorem nearestQFourierMainTheorem
    (q : Nat)
    (hq : 0 < q) :
    (∀ t : Nat,
      (nearestQCenteredOmegaAt q t : ℂ) =
        Finset.sum
          (Finset.Ico
            1
            (nearestQExactPeriod q))
          (fun ell =>
            nearestQCenteredOmegaFourierCoeff q ell *
              nearestQFourierRoot q ^
                (ell * (t + 1)))) ∧
      (∀ t : Nat,
        (nearestQOmegaTildeAt q t : ℂ) =
          Finset.sum
            (Finset.Ico
              1
              (nearestQExactPeriod q))
            (fun ell =>
              nearestQOmegaTildeFourierCoeff q ell *
                (nearestQFourierRoot q ^
                    (ell * (t + 1)) -
                  nearestQFourierRoot q ^ ell))) ∧
      (∀ ell : Nat,
        0 < ell →
        ell < nearestQExactPeriod q →
        nearestQOmegaTildeFourierCoeff q ell *
            (nearestQFourierRoot q ^ ell - 1) =
          nearestQCenteredOmegaFourierCoeff q ell) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simpa [nearestQCenteredOmegaFourierSeries] using
      (nearestQCenteredOmegaFourierSeries_eq
        q t hq).symm
  · intro t
    exact
      nearestQOmegaTildeAt_eq_fourierFormula
        q t hq
  · intro ell hellPos hellLt
    exact
      nearestQOmegaTildeFourierCoeff_mul_sub
        q ell hq hellPos hellLt

end RoundedRootSums
