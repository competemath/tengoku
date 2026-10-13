/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ScaledExponent.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ScaledExponent.Internal

/-!
# Positive rational exponent scales

This module exposes natural-number versions of the rational exponents used in
hardness magnification. Floor and ceiling differ by at most one in the exponent,
so their powers of two differ by at most a factor of two. It also provides the
exact power-of-two input-length identity for a rounded `N^(1+epsilon)` bound.
-/

public section

namespace Complexity

namespace PositiveRationalScale

/-- Every represented rational scale is strictly positive.
@isnad1 id=lt.0h1v.s3.4989d40150a9 from=translated src=- shape=b9369acb vocab=4fb8dc06
-/
theorem value_pos (scale : PositiveRationalScale) :
    0 < scale.value :=
  value_pos_internal scale

/-- A property holds for all sufficiently small positive rational scales exactly
when it holds below one positive rational cutoff.
@isnad1 id=iff.0h1v.s4.87fce37605e7 from=translated src=- shape=c587e620 vocab=f3061d43
-/
theorem eventually_atZeroFromPositive_iff
    {predicate : PositiveRationalScale → Prop} :
    (∀ᶠ scale in atZeroFromPositive, predicate scale) ↔
      ∃ cutoff, ∀ scale ≤ cutoff, predicate scale :=
  eventually_atZeroFromPositive_iff_internal

/-- Scaling zero gives zero under floor rounding.
@isnad1 id=eq.0h1v.s4.5b987456a42d from=translated src=- shape=9b4d794a vocab=7ed38f60
-/
@[simp] theorem floorMul_zero (scale : PositiveRationalScale) :
    scale.floorMul 0 = 0 :=
  floorMul_zero_internal scale

/-- Scaling zero gives zero under ceiling rounding.
@isnad1 id=eq.0h1v.s4.fd204d429bc4 from=translated src=- shape=9b4d794a vocab=8a72ba99
-/
@[simp] theorem ceilMul_zero (scale : PositiveRationalScale) :
    scale.ceilMul 0 = 0 :=
  ceilMul_zero_internal scale

/-- Floor-scaled multiplication is monotone in the natural argument.
@isnad1 id=monotone.0h1v.s3.fcb49fd689f3 from=translated src=- shape=8735051e vocab=419fa146
-/
theorem floorMul_mono (scale : PositiveRationalScale) :
    Monotone scale.floorMul :=
  floorMul_mono_internal scale

/-- The sum of two floor-rounded scaled exponents does not exceed the
floor-rounded scale of their sum.
@isnad1 id=le.0h3v.s5.ef5d6c2fd4f2 from=translated src=- shape=238d4e08 vocab=8c6265d5
-/
theorem floorMul_add_le (scale : PositiveRationalScale)
    (first second : ℕ) :
    scale.floorMul first + scale.floorMul second ≤
      scale.floorMul (first + second) :=
  floorMul_add_le_internal scale first second

/-- The floor-scaled exponent tends to infinity for every positive rational
scale.
@isnad1 id=tendsto.0h1v.s3.7cc18191072d from=translated src=- shape=74931b86 vocab=101548bd
-/
theorem tendsto_floorMul_atTop (scale : PositiveRationalScale) :
    Filter.Tendsto scale.floorMul Filter.atTop Filter.atTop :=
  tendsto_floorMul_atTop_internal scale

/-- Every fixed multiple of `n + 1` is eventually bounded by `2^n`.
@isnad1 id=eventual.0h1v.s5.01bff2b16b08 from=translated src=- shape=ab2d4b63 vocab=0d81815e
-/
theorem eventually_coefficient_mul_succ_le_two_pow (coefficient : ℕ) :
    ∀ᶠ exponent : ℕ in Filter.atTop,
      coefficient * (exponent + 1) ≤ 2 ^ exponent :=
  eventually_coefficient_mul_succ_le_two_pow_internal coefficient

/-- Every fixed coefficient times a fixed power of `n + 1` is eventually
bounded by the binary exponential `2^n`.
@isnad1 id=eventual.0h2v.s6.6523ed3afa7e from=translated src=- shape=b565fae2 vocab=0d81815e
-/
theorem eventually_coefficient_mul_succ_pow_le_two_pow
    (coefficient degree : ℕ) :
    ∀ᶠ exponent : ℕ in Filter.atTop,
      coefficient * (exponent + 1) ^ degree ≤ 2 ^ exponent :=
  eventually_coefficient_mul_succ_pow_le_two_pow_internal
    coefficient degree

/-- Every fixed polynomial is eventually bounded by a floor-rounded binary
exponential at any positive rational scale.
@isnad1 id=eventual.0h3v.s5.2638cc4f42d0 from=translated src=- shape=7fc742a8 vocab=6fa1e9a9
-/
theorem eventually_coefficient_mul_succ_pow_le_powFloor
    (scale : PositiveRationalScale) (coefficient degree : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      coefficient * (n + 1) ^ degree ≤ scale.powFloor n :=
  eventually_coefficient_mul_succ_pow_le_powFloor_internal
    scale coefficient degree

/-- Ceiling-scaled multiplication is monotone in the natural argument.
@isnad1 id=monotone.0h1v.s3.69021038b565 from=translated src=- shape=8735051e vocab=51d3224e
-/
theorem ceilMul_mono (scale : PositiveRationalScale) :
    Monotone scale.ceilMul :=
  ceilMul_mono_internal scale

/-- Floor rounding never exceeds the exact scaled numerator after restoring the
denominator.
@isnad1 id=le.0h2v.s4.90385cf9fb88 from=translated src=- shape=2e9168c3 vocab=7b7227ab
-/
theorem denominator_mul_floorMul_le
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.denominator * scale.floorMul n ≤ scale.numerator * n :=
  denominator_mul_floorMul_le_internal scale n

/-- Ceiling rounding covers the exact scaled numerator after restoring the
denominator.
@isnad1 id=le.0h2v.s4.36e157ff905d from=translated src=- shape=47d71459 vocab=216ccb46
-/
theorem numerator_mul_le_denominator_mul_ceilMul
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.numerator * n ≤ scale.denominator * scale.ceilMul n :=
  numerator_mul_le_denominator_mul_ceilMul_internal scale n

/-- Floor rounding is no larger than ceiling rounding.
@isnad1 id=le.0h2v.s3.78d4ca37541b from=translated src=- shape=d802f31c vocab=6c74cbdc
-/
theorem floorMul_le_ceilMul (scale : PositiveRationalScale) (n : ℕ) :
    scale.floorMul n ≤ scale.ceilMul n :=
  floorMul_le_ceilMul_internal scale n

/-- Floor and ceiling rounding differ by at most one.
@isnad1 id=le.0h2v.s4.62f4f709cf95 from=translated src=- shape=68cd0b88 vocab=868b39ba
-/
theorem ceilMul_le_floorMul_add_one
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.ceilMul n ≤ scale.floorMul n + 1 :=
  ceilMul_le_floorMul_add_one_internal scale n

/-- Once the unrounded numerator reaches the denominator, its floor-scaled
value is positive.
@isnad1 id=lt.1h2v.s4.5ef5a1df132d from=translated src=- shape=02255fdf vocab=ff1c8931
-/
theorem floorMul_pos_of_denominator_le_numerator_mul
    (scale : PositiveRationalScale) {n : ℕ}
    (hlarge : scale.denominator ≤ scale.numerator * n) :
    0 < scale.floorMul n :=
  floorMul_pos_of_denominator_le_numerator_mul_internal scale hlarge

/-- Rounded-down powers of two are positive.
@isnad1 id=lt.0h2v.s3.db64a93c5471 from=translated src=- shape=787c1379 vocab=5a851392
-/
theorem powFloor_pos (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powFloor n :=
  powFloor_pos_internal scale n

/-- Rounded-up powers of two are positive.
@isnad1 id=lt.0h2v.s3.6414931938e1 from=translated src=- shape=787c1379 vocab=40347814
-/
theorem powCeil_pos (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powCeil n :=
  powCeil_pos_internal scale n

/-- Rounded-down powers are monotone in the natural argument.
@isnad1 id=monotone.0h1v.s3.3b331f5f1794 from=translated src=- shape=8735051e vocab=1349d148
-/
theorem powFloor_mono (scale : PositiveRationalScale) :
    Monotone scale.powFloor :=
  powFloor_mono_internal scale

/-- The product of two floor-rounded binary powers is bounded by the rounded
power at the sum of their arguments.
@isnad1 id=le.0h3v.s5.da170945bd79 from=translated src=- shape=a8afc661 vocab=2942c0c0
-/
theorem powFloor_mul_le_powFloor_add
    (scale : PositiveRationalScale) (first second : ℕ) :
    scale.powFloor first * scale.powFloor second ≤
      scale.powFloor (first + second) :=
  powFloor_mul_le_powFloor_add_internal scale first second

/-- A fixed power of a floor-rounded binary power is bounded by scaling the
natural argument by the same multiplier.
@isnad1 id=le.0h3v.s5.6313f72087a1 from=translated src=- shape=6e1c686e vocab=5bc43d6f
-/
theorem powFloor_pow_le_mul
    (scale : PositiveRationalScale) (n multiplier : ℕ) :
    (scale.powFloor n) ^ multiplier ≤
      scale.powFloor (multiplier * n) :=
  powFloor_pow_le_mul_internal scale n multiplier

/-- Rounded-up powers are monotone in the natural argument.
@isnad1 id=monotone.0h1v.s3.13afab62e0a2 from=translated src=- shape=8735051e vocab=0952ad71
-/
theorem powCeil_mono (scale : PositiveRationalScale) :
    Monotone scale.powCeil :=
  powCeil_mono_internal scale

/-- Rounding the exponent down gives no larger a power than rounding it up.
@isnad1 id=le.0h2v.s3.767d1f126290 from=translated src=- shape=d802f31c vocab=e6ce94d2
-/
theorem powFloor_le_powCeil (scale : PositiveRationalScale) (n : ℕ) :
    scale.powFloor n ≤ scale.powCeil n :=
  powFloor_le_powCeil_internal scale n

/-- Changing floor to ceiling costs at most a factor of two for binary
exponentials.
@isnad1 id=le.0h2v.s4.4ef717aebbdc from=translated src=- shape=71f7d852 vocab=9cec39ec
-/
theorem powCeil_le_two_mul_powFloor
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.powCeil n ≤ 2 * scale.powFloor n :=
  powCeil_le_two_mul_powFloor_internal scale n

/-- The rounded `N^(1+scale)` bound factors into its linear and fractional
binary powers.
@isnad1 id=eq.0h2v.s5.58a3aa75d355 from=translated src=- shape=85226024 vocab=caa1dbc2
-/
@[simp] theorem onePlusCeilPow_eq_mul
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPow n = 2 ^ n * scale.powCeil n :=
  onePlusCeilPow_eq_mul_internal scale n

/-- The rounded `N^(1+scale)` bound is at least the raw input length `N`.
@isnad1 id=le.0h2v.s4.d04d4862a830 from=translated src=- shape=148568ff vocab=b9fcea39
-/
theorem two_pow_le_onePlusCeilPow
    (scale : PositiveRationalScale) (n : ℕ) :
    2 ^ n ≤ scale.onePlusCeilPow n :=
  two_pow_le_onePlusCeilPow_internal scale n

/-- On an exact `2^n`-bit input, recovering arity from length gives the intended
rounded `N^(1+scale)` bound exactly.
@isnad1 id=eq.0h2v.s4.82d539f65539 from=translated src=- shape=0c660c4d vocab=2ee32058
-/
@[simp] theorem onePlusCeilPowAtLength_pow
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPowAtLength (2 ^ n) = scale.onePlusCeilPow n :=
  onePlusCeilPowAtLength_pow_internal scale n

end PositiveRationalScale

end Complexity
