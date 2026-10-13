/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ScaledExponent.Defs
public import Tengoku

/-!
# Positive rational exponent scales -- proof internals
-/

public section

namespace Complexity

namespace PositiveRationalScale

private def commonLower (first second : PositiveRationalScale) :
    PositiveRationalScale where
  numerator := 1
  denominator := first.denominator * second.denominator
  numerator_pos := by decide
  denominator_pos := Nat.mul_pos first.denominator_pos second.denominator_pos

private theorem commonLower_le_left (first second : PositiveRationalScale) :
    commonLower first second ≤ first := by
  change value (commonLower first second) ≤ value first
  simp only [value, commonLower, Nat.cast_one, Nat.cast_mul]
  apply (div_le_div_iff₀
    (mul_pos (Nat.cast_pos.mpr first.denominator_pos)
      (Nat.cast_pos.mpr second.denominator_pos))
    (Nat.cast_pos.mpr first.denominator_pos)).mpr
  simp only [one_mul]
  have hnat :
      first.denominator ≤
        first.numerator * (first.denominator * second.denominator) := by
    calc
      first.denominator = 1 * first.denominator * 1 := by simp
      _ ≤ first.numerator * first.denominator * 1 :=
        Nat.mul_le_mul_right 1
          (Nat.mul_le_mul_right first.denominator first.numerator_pos)
      _ ≤ first.numerator * first.denominator * second.denominator :=
        Nat.mul_le_mul_left (first.numerator * first.denominator)
          second.denominator_pos
      _ = first.numerator * (first.denominator * second.denominator) := by
        simp [Nat.mul_assoc]
  simpa only [Nat.cast_mul] using (Nat.cast_le.mpr hnat :
    (first.denominator : ℚ) ≤
      (first.numerator * (first.denominator * second.denominator) : ℕ))

private theorem commonLower_le_right (first second : PositiveRationalScale) :
    commonLower first second ≤ second := by
  change value (commonLower first second) ≤ value second
  simp only [value, commonLower, Nat.cast_one, Nat.cast_mul]
  apply (div_le_div_iff₀
    (mul_pos (Nat.cast_pos.mpr first.denominator_pos)
      (Nat.cast_pos.mpr second.denominator_pos))
    (Nat.cast_pos.mpr second.denominator_pos)).mpr
  simp only [one_mul]
  have hnat :
      second.denominator ≤
        second.numerator * (first.denominator * second.denominator) := by
    calc
      second.denominator = 1 * second.denominator * 1 := by simp
      _ ≤ second.numerator * second.denominator * 1 :=
        Nat.mul_le_mul_right 1
          (Nat.mul_le_mul_right second.denominator second.numerator_pos)
      _ ≤ second.numerator * second.denominator * first.denominator :=
        Nat.mul_le_mul_left (second.numerator * second.denominator)
          first.denominator_pos
      _ = second.numerator *
          (first.denominator * second.denominator) := by
        ac_rfl
  simpa only [Nat.cast_mul] using (Nat.cast_le.mpr hnat :
    (second.denominator : ℚ) ≤
      (second.numerator * (first.denominator * second.denominator) : ℕ))

local instance : Nonempty PositiveRationalScale :=
  ⟨⟨1, 1, by decide, by decide⟩⟩

local instance : IsCodirectedOrder PositiveRationalScale where
  directed first second :=
    ⟨commonLower first second, commonLower_le_left first second,
      commonLower_le_right first second⟩

/--
@isnad1 id=lt.0h1v.s3.4989d40150a9 from=translated src=- shape=b9369acb vocab=4fb8dc06
-/
theorem value_pos_internal (scale : PositiveRationalScale) :
    0 < scale.value := by
  exact div_pos (Nat.cast_pos.mpr scale.numerator_pos)
    (Nat.cast_pos.mpr scale.denominator_pos)

/--
@isnad1 id=iff.0h1v.s4.87fce37605e7 from=translated src=- shape=c587e620 vocab=f3061d43
-/
theorem eventually_atZeroFromPositive_iff_internal
    {predicate : PositiveRationalScale → Prop} :
    (∀ᶠ scale in atZeroFromPositive, predicate scale) ↔
      ∃ cutoff, ∀ scale ≤ cutoff, predicate scale := by
  exact Filter.eventually_atBot

/--
@isnad1 id=eq.0h1v.s4.5b987456a42d from=translated src=- shape=9b4d794a vocab=7ed38f60
-/
theorem floorMul_zero_internal (scale : PositiveRationalScale) :
    scale.floorMul 0 = 0 := by
  simp [floorMul]

/--
@isnad1 id=eq.0h1v.s4.fd204d429bc4 from=translated src=- shape=9b4d794a vocab=8a72ba99
-/
theorem ceilMul_zero_internal (scale : PositiveRationalScale) :
    scale.ceilMul 0 = 0 := by
  simp [ceilMul]

/--
@isnad1 id=monotone.0h1v.s3.fcb49fd689f3 from=translated src=- shape=8735051e vocab=419fa146
-/
theorem floorMul_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.floorMul := by
  intro first second hle
  exact Nat.div_le_div_right (Nat.mul_le_mul_left scale.numerator hle)

/--
@isnad1 id=le.0h3v.s5.ef5d6c2fd4f2 from=translated src=- shape=238d4e08 vocab=8c6265d5
-/
theorem floorMul_add_le_internal (scale : PositiveRationalScale)
    (first second : ℕ) :
    scale.floorMul first + scale.floorMul second ≤
      scale.floorMul (first + second) := by
  unfold floorMul
  rw [Nat.mul_add]
  exact Nat.div_add_div_le_add_div

/--
@isnad1 id=tendsto.0h1v.s3.7cc18191072d from=translated src=- shape=74931b86 vocab=101548bd
-/
theorem tendsto_floorMul_atTop_internal (scale : PositiveRationalScale) :
    Filter.Tendsto scale.floorMul Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro target
  apply Filter.eventually_atTop.mpr
  refine ⟨scale.denominator * target, fun n hn => ?_⟩
  apply (Nat.le_div_iff_mul_le scale.denominator_pos).mpr
  calc
    target * scale.denominator = scale.denominator * target := by
      exact Nat.mul_comm _ _
    _ ≤ n := hn
    _ = 1 * n := by simp
    _ ≤ scale.numerator * n :=
      Nat.mul_le_mul_right n scale.numerator_pos

/--
@isnad1 id=eventual.0h1v.s5.01bff2b16b08 from=translated src=- shape=ab2d4b63 vocab=0d81815e
-/
theorem eventually_coefficient_mul_succ_le_two_pow_internal
    (coefficient : ℕ) :
    ∀ᶠ exponent : ℕ in Filter.atTop,
      coefficient * (exponent + 1) ≤ 2 ^ exponent := by
  have hlittle : ((↑) : ℕ → ℝ) =o[Filter.atTop]
      fun exponent => (2 : ℝ) ^ exponent :=
    isLittleO_coe_const_pow_of_one_lt (by norm_num)
  have hcoefficient :
      (0 : ℝ) < (((coefficient + 1 : ℕ) : ℝ))⁻¹ := by
    positivity
  have hbound := hlittle.bound hcoefficient
  filter_upwards [hbound, Filter.eventually_ge_atTop coefficient]
      with exponent hexponential hcoefficient_le
  simp only [Real.norm_eq_abs] at hexponential
  rw [abs_of_nonneg (Nat.cast_nonneg exponent),
    abs_of_nonneg (pow_nonneg (by norm_num) exponent)] at hexponential
  have hcoefficient_pos :
      (0 : ℝ) < ((coefficient + 1 : ℕ) : ℝ) := by
    positivity
  have hexponential' :
      (((coefficient + 1 : ℕ) : ℝ) * exponent) ≤
        (2 : ℝ) ^ exponent := by
    have hdiv :
        (exponent : ℝ) ≤
          (2 : ℝ) ^ exponent / ((coefficient + 1 : ℕ) : ℝ) := by
      rw [div_eq_inv_mul]
      exact hexponential
    simpa only [mul_comm] using
      (le_div_iff₀ hcoefficient_pos).mp hdiv
  have hnat :
      coefficient * (exponent + 1) ≤ (coefficient + 1) * exponent := by
    calc
      coefficient * (exponent + 1) =
          coefficient * exponent + coefficient := by
        simp [Nat.mul_add]
      _ ≤ coefficient * exponent + exponent :=
        Nat.add_le_add_left hcoefficient_le (coefficient * exponent)
      _ = (coefficient + 1) * exponent := by simp [Nat.add_mul]
  have hnatReal :
      (coefficient : ℝ) * (exponent + 1) ≤
        ((coefficient + 1 : ℕ) : ℝ) * exponent := by
    exact_mod_cast hnat
  exact_mod_cast hnatReal.trans hexponential'

/--
@isnad1 id=eventual.0h2v.s6.6523ed3afa7e from=translated src=- shape=b565fae2 vocab=0d81815e
-/
theorem eventually_coefficient_mul_succ_pow_le_two_pow_internal
    (coefficient degree : ℕ) :
    ∀ᶠ exponent : ℕ in Filter.atTop,
      coefficient * (exponent + 1) ^ degree ≤ 2 ^ exponent := by
  let scaledCoefficient := coefficient * 2 ^ degree
  have hlittle : (fun exponent : ℕ => (exponent : ℝ) ^ degree)
      =o[Filter.atTop] fun exponent => (2 : ℝ) ^ exponent :=
    isLittleO_pow_const_const_pow_of_one_lt degree (by norm_num)
  have hcoefficient :
      (0 : ℝ) < (((scaledCoefficient + 1 : ℕ) : ℝ))⁻¹ := by
    positivity
  have hbound := hlittle.bound hcoefficient
  filter_upwards [hbound, Filter.eventually_ge_atTop 1]
      with exponent hexponential hexponent
  simp only [Real.norm_eq_abs] at hexponential
  rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg exponent) degree),
    abs_of_nonneg (pow_nonneg (by norm_num) exponent)] at hexponential
  have hcoefficientPos :
      (0 : ℝ) < ((scaledCoefficient + 1 : ℕ) : ℝ) := by
    positivity
  have hexponential' :
      ((scaledCoefficient + 1 : ℕ) : ℝ) *
          (exponent : ℝ) ^ degree ≤
        (2 : ℝ) ^ exponent := by
    have hdiv :
        (exponent : ℝ) ^ degree ≤
          (2 : ℝ) ^ exponent /
            ((scaledCoefficient + 1 : ℕ) : ℝ) := by
      rw [div_eq_inv_mul]
      exact hexponential
    simpa only [mul_comm] using
      (le_div_iff₀ hcoefficientPos).mp hdiv
  have hbase : exponent + 1 ≤ 2 * exponent := by
    omega
  have hnat :
      coefficient * (exponent + 1) ^ degree ≤
        (scaledCoefficient + 1) * exponent ^ degree := by
    calc
      coefficient * (exponent + 1) ^ degree ≤
          coefficient * (2 * exponent) ^ degree :=
        Nat.mul_le_mul_left coefficient
          (Nat.pow_le_pow_left hbase degree)
      _ = scaledCoefficient * exponent ^ degree := by
        simp [scaledCoefficient, Nat.mul_pow, Nat.mul_assoc]
      _ ≤ (scaledCoefficient + 1) * exponent ^ degree :=
        Nat.mul_le_mul_right (exponent ^ degree)
          (Nat.le_add_right scaledCoefficient 1)
  have hnatReal :
      (coefficient : ℝ) * (exponent + 1) ^ degree ≤
        ((scaledCoefficient + 1 : ℕ) : ℝ) * exponent ^ degree := by
    exact_mod_cast hnat
  exact_mod_cast hnatReal.trans hexponential'

/--
@isnad1 id=eventual.0h3v.s5.2638cc4f42d0 from=translated src=- shape=7fc742a8 vocab=6fa1e9a9
-/
theorem eventually_coefficient_mul_succ_pow_le_powFloor_internal
    (scale : PositiveRationalScale) (coefficient degree : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      coefficient * (n + 1) ^ degree ≤ scale.powFloor n := by
  have hexponential :=
    (tendsto_floorMul_atTop_internal scale).eventually
      (eventually_coefficient_mul_succ_pow_le_two_pow_internal
        (coefficient * scale.denominator ^ degree) degree)
  filter_upwards [hexponential] with n hn
  have hnle : n ≤ scale.numerator * n := by
    calc
      n = 1 * n := by simp
      _ ≤ scale.numerator * n :=
        Nat.mul_le_mul_right n scale.numerator_pos
  have hfloor :
      scale.numerator * n <
        scale.denominator * (scale.floorMul n + 1) := by
    unfold floorMul
    simpa only [Nat.mul_comm] using
      Nat.lt_mul_div_succ (scale.numerator * n) scale.denominator_pos
  have hbase :
      n + 1 ≤ scale.denominator * (scale.floorMul n + 1) := by
    omega
  calc
    coefficient * (n + 1) ^ degree ≤
        coefficient *
          (scale.denominator * (scale.floorMul n + 1)) ^ degree :=
      Nat.mul_le_mul_left coefficient
        (Nat.pow_le_pow_left hbase degree)
    _ = (coefficient * scale.denominator ^ degree) *
        (scale.floorMul n + 1) ^ degree := by
      simp [Nat.mul_pow, Nat.mul_assoc]
    _ ≤ 2 ^ scale.floorMul n := hn
    _ = scale.powFloor n := rfl

/--
@isnad1 id=monotone.0h1v.s3.69021038b565 from=translated src=- shape=8735051e vocab=51d3224e
-/
theorem ceilMul_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.ceilMul := by
  intro first second hle
  exact (gc_mul_ceilDiv scale.denominator_pos).monotone_l
    (Nat.mul_le_mul_left scale.numerator hle)

/--
@isnad1 id=le.0h2v.s4.90385cf9fb88 from=translated src=- shape=2e9168c3 vocab=7b7227ab
-/
theorem denominator_mul_floorMul_le_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.denominator * scale.floorMul n ≤ scale.numerator * n := by
  simpa [floorMul, Nat.mul_comm] using
    Nat.div_mul_le_self (scale.numerator * n) scale.denominator

/--
@isnad1 id=le.0h2v.s4.36e157ff905d from=translated src=- shape=47d71459 vocab=216ccb46
-/
theorem numerator_mul_le_denominator_mul_ceilMul_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.numerator * n ≤ scale.denominator * scale.ceilMul n := by
  exact (ceilDiv_le_iff_le_mul scale.denominator_pos).mp le_rfl

/--
@isnad1 id=le.0h2v.s3.78d4ca37541b from=translated src=- shape=d802f31c vocab=6c74cbdc
-/
theorem floorMul_le_ceilMul_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.floorMul n ≤ scale.ceilMul n := by
  change (scale.numerator * n ⌊/⌋ scale.denominator) ≤
    (scale.numerator * n ⌈/⌉ scale.denominator)
  exact floorDiv_le_ceilDiv

/--
@isnad1 id=le.0h2v.s4.62f4f709cf95 from=translated src=- shape=68cd0b88 vocab=868b39ba
-/
theorem ceilMul_le_floorMul_add_one_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.ceilMul n ≤ scale.floorMul n + 1 := by
  apply (ceilDiv_le_iff_le_mul scale.denominator_pos).mpr
  exact (Nat.lt_mul_div_succ (scale.numerator * n)
    scale.denominator_pos).le

/--
@isnad1 id=lt.1h2v.s4.5ef5a1df132d from=translated src=- shape=02255fdf vocab=ff1c8931
-/
theorem floorMul_pos_of_denominator_le_numerator_mul_internal
    (scale : PositiveRationalScale) {n : ℕ}
    (hlarge : scale.denominator ≤ scale.numerator * n) :
    0 < scale.floorMul n := by
  exact Nat.div_pos hlarge scale.denominator_pos

/--
@isnad1 id=lt.0h2v.s3.db64a93c5471 from=translated src=- shape=787c1379 vocab=5a851392
-/
theorem powFloor_pos_internal (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powFloor n := by
  exact Nat.two_pow_pos _

/--
@isnad1 id=lt.0h2v.s3.6414931938e1 from=translated src=- shape=787c1379 vocab=40347814
-/
theorem powCeil_pos_internal (scale : PositiveRationalScale) (n : ℕ) :
    0 < scale.powCeil n := by
  exact Nat.two_pow_pos _

/--
@isnad1 id=monotone.0h1v.s3.3b331f5f1794 from=translated src=- shape=8735051e vocab=1349d148
-/
theorem powFloor_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.powFloor := by
  intro first second hle
  exact Nat.pow_le_pow_right (by decide)
    (floorMul_mono_internal scale hle)

/--
@isnad1 id=le.0h3v.s5.da170945bd79 from=translated src=- shape=a8afc661 vocab=2942c0c0
-/
theorem powFloor_mul_le_powFloor_add_internal
    (scale : PositiveRationalScale) (first second : ℕ) :
    scale.powFloor first * scale.powFloor second ≤
      scale.powFloor (first + second) := by
  unfold powFloor
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by decide)
    (floorMul_add_le_internal scale first second)

/--
@isnad1 id=le.0h3v.s5.6313f72087a1 from=translated src=- shape=6e1c686e vocab=5bc43d6f
-/
theorem powFloor_pow_le_mul_internal
    (scale : PositiveRationalScale) (n multiplier : ℕ) :
    (scale.powFloor n) ^ multiplier ≤
      scale.powFloor (multiplier * n) := by
  induction multiplier with
  | zero => simp [powFloor, floorMul]
  | succ multiplier ih =>
      calc
        (scale.powFloor n) ^ (multiplier + 1) =
            (scale.powFloor n) ^ multiplier * scale.powFloor n := by
          rw [pow_succ]
        _ ≤ scale.powFloor (multiplier * n) * scale.powFloor n :=
          Nat.mul_le_mul_right (scale.powFloor n) ih
        _ ≤ scale.powFloor (multiplier * n + n) :=
          powFloor_mul_le_powFloor_add_internal
            scale (multiplier * n) n
        _ = scale.powFloor ((multiplier + 1) * n) := by
          rw [Nat.add_mul, one_mul]

/--
@isnad1 id=monotone.0h1v.s3.13afab62e0a2 from=translated src=- shape=8735051e vocab=0952ad71
-/
theorem powCeil_mono_internal (scale : PositiveRationalScale) :
    Monotone scale.powCeil := by
  intro first second hle
  exact Nat.pow_le_pow_right (by decide)
    (ceilMul_mono_internal scale hle)

/--
@isnad1 id=le.0h2v.s3.767d1f126290 from=translated src=- shape=d802f31c vocab=e6ce94d2
-/
theorem powFloor_le_powCeil_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.powFloor n ≤ scale.powCeil n := by
  exact Nat.pow_le_pow_right (by decide)
    (floorMul_le_ceilMul_internal scale n)

/--
@isnad1 id=le.0h2v.s4.4ef717aebbdc from=translated src=- shape=71f7d852 vocab=9cec39ec
-/
theorem powCeil_le_two_mul_powFloor_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.powCeil n ≤ 2 * scale.powFloor n := by
  calc
    scale.powCeil n ≤ 2 ^ (scale.floorMul n + 1) :=
      Nat.pow_le_pow_right (by decide)
        (ceilMul_le_floorMul_add_one_internal scale n)
    _ = 2 * scale.powFloor n := by
      simp [powFloor, pow_succ, Nat.mul_comm]

/--
@isnad1 id=eq.0h2v.s5.58a3aa75d355 from=translated src=- shape=85226024 vocab=caa1dbc2
-/
theorem onePlusCeilPow_eq_mul_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPow n = 2 ^ n * scale.powCeil n := by
  simp [onePlusCeilPow, onePlusCeilExponent, pow_add, powCeil]

/--
@isnad1 id=le.0h2v.s4.d04d4862a830 from=translated src=- shape=148568ff vocab=b9fcea39
-/
theorem two_pow_le_onePlusCeilPow_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    2 ^ n ≤ scale.onePlusCeilPow n := by
  rw [onePlusCeilPow_eq_mul_internal]
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ n)
    (Nat.succ_le_iff.mpr (powCeil_pos_internal scale n))

/--
@isnad1 id=eq.0h2v.s4.82d539f65539 from=translated src=- shape=0c660c4d vocab=2ee32058
-/
theorem onePlusCeilPowAtLength_pow_internal
    (scale : PositiveRationalScale) (n : ℕ) :
    scale.onePlusCeilPowAtLength (2 ^ n) = scale.onePlusCeilPow n := by
  simp [onePlusCeilPowAtLength,
    Nat.log_pow (show 1 < (2 : ℕ) by decide)]

end PositiveRationalScale

end Complexity
