/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Core.IntervalRat.Taylor
import Tengoku.Leancert.LeanCert.Core.TrigReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Computable Range Reduction for Trigonometric Functions

This file implements range reduction for sin and cos to improve Taylor series
convergence for intervals far from 0.

## Problem

Standard Taylor series for sin/cos centered at 0 have remainder bounds of
`|x|^{n+1} / (n+1)!`. For intervals far from 0 (e.g., [10, 11]), this remainder
is huge even for moderate n.

## Solution: Range Reduction

Use the periodicity of sin/cos:
- `sin(x) = sin(x - 2πk)` for any integer k
- `cos(x) = cos(x - 2πk)` for any integer k

By choosing k to bring x - 2πk into [-π, π], the Taylor series converges much
faster since |x - 2πk| ≤ π ≈ 3.14.

## Main definitions

* `twoPiRatLo`, `twoPiRatHi` - Rational bounds for 2π
* `reduceToMainPeriod` - Shift interval to be near 0
* `sinComputableReduced`, `cosComputableReduced` - Computable evaluation with range reduction
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Core.IntervalRat

/-! ### Shared range-reduction API -/

def piRatLo : ℚ := LeanCert.Core.TrigReduction.piRatLo
def piRatHi : ℚ := LeanCert.Core.TrigReduction.piRatHi
def twoPiRatLo : ℚ := LeanCert.Core.TrigReduction.twoPiRatLo
def twoPiRatHi : ℚ := LeanCert.Core.TrigReduction.twoPiRatHi
def computeShiftK : IntervalRat → ℤ := LeanCert.Core.TrigReduction.computeShiftK
def shiftInterval : IntervalRat → ℤ → IntervalRat := LeanCert.Core.TrigReduction.shiftInterval
def reduceToMainPeriod : IntervalRat → IntervalRat × ℤ :=
  LeanCert.Core.TrigReduction.reduceToMainPeriod

/--
@isnad1 id=lt.0h0v.s3.ecad53a24d21 from=translated src=- shape=28fc0566 vocab=f167e3b2
-/
theorem piRatLo_lt_pi : (piRatLo : ℝ) < Real.pi :=
  LeanCert.Core.TrigReduction.piRatLo_lt_pi

/--
@isnad1 id=lt.0h0v.s3.617af07c0216 from=translated src=- shape=dfaa3aa7 vocab=130cbdd0
-/
theorem pi_lt_piRatHi : Real.pi < (piRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.pi_lt_piRatHi

/--
@isnad1 id=lt.0h0v.s4.1e7972632785 from=translated src=- shape=f88084c2 vocab=4855ec69
-/
theorem twoPiRatLo_lt_two_pi : (twoPiRatLo : ℝ) < 2 * Real.pi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_lt_two_pi

/--
@isnad1 id=lt.0h0v.s4.c9767b18173b from=translated src=- shape=b6e781e9 vocab=75c0c0f8
-/
theorem two_pi_lt_twoPiRatHi : 2 * Real.pi < (twoPiRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.two_pi_lt_twoPiRatHi

/--
@isnad1 id=le.0h0v.s2.258863c967f2 from=translated src=- shape=54c8eceb vocab=fcfd5cda
-/
theorem twoPiRatLo_le_twoPiRatHi : twoPiRatLo ≤ twoPiRatHi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_le_twoPiRatHi

/--
@isnad1 id=mem.1h3v.s5.cd649540a002 from=translated src=- shape=fdef543f vocab=eb6761ed
-/
theorem mem_shiftInterval_of_mem {x : ℝ} {I : IntervalRat} {k : ℤ}
    (hx : x ∈ I) : x - 2 * Real.pi * k ∈ shiftInterval I k := by
  change x - 2 * Real.pi * k ∈ LeanCert.Core.TrigReduction.shiftInterval I k
  exact LeanCert.Core.TrigReduction.mem_shiftInterval_of_mem hx

/-! ### Computable reduced evaluation -/

/-- Computable sin evaluation with range reduction. -/
def sinComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    sinComputable Ired n

/-- Computable cos evaluation with range reduction. -/
def cosComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    cosComputable Ired n

/-- sin x ∈ sinComputableReduced I for all x ∈ I
@isnad1 id=mem.1h3v.s4.c8658f469f6c from=translated src=- shape=71d4a1f7 vocab=9e2cdbf2
-/
theorem mem_sinComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.sin x ∈ sinComputableReduced I n := by
  unfold sinComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hsin_eq : Real.sin x = Real.sin (x - 2 * Real.pi * k) := by
    have h := Real.sin_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  · push Not at hwide
    rw [hsin_eq]
    exact mem_sinComputable hxred n

/-- cos x ∈ cosComputableReduced I for all x ∈ I
@isnad1 id=mem.1h3v.s4.9386c2d03f88 from=translated src=- shape=71d4a1f7 vocab=63d08d4c
-/
theorem mem_cosComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.cos x ∈ cosComputableReduced I n := by
  unfold cosComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hcos_eq : Real.cos x = Real.cos (x - 2 * Real.pi * k) := by
    have h := Real.cos_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  · rw [hcos_eq]
    exact mem_cosComputable hxred n

end LeanCert.Core.IntervalRat
