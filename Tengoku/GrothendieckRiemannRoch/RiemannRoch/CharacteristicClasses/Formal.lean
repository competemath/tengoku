/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.NumberTheory.Bernoulli
import Tengoku.Seed.RingTheory.PowerSeries.Exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal power series for the Chern character and Todd class

The characteristic series used by Hirzebruch--Riemann--Roch are defined independently of any
Euler characteristic or integration map. For a formal Chern root `x`, the Chern character factor
is `exp(x)` and the Todd factor is `x / (1 - exp(-x))`, represented by the Bernoulli-prime power
series. Their normalization and functional equations are kernel checked here.
-/

noncomputable section

open PowerSeries

universe u

namespace CharacteristicClasses

variable (A : Type u) [CommRing A] [Algebra ℚ A]

/-- Universal Chern-character series for one formal Chern root.-/
def chLine : PowerSeries A :=
  PowerSeries.exp A

/-- Universal Todd series for one formal Chern root. This is the series
`x / (1 - exp(-x))`.-/
def toddLine : PowerSeries A :=
  bernoulli'PowerSeries A

/-- A scaled formal Chern root contributes `exp(a X)`.-/
def chRoot (a : A) : PowerSeries A :=
  PowerSeries.rescale a (chLine A)

/-- A scaled formal Chern root contributes the Todd factor `td(a X)`.-/
def toddRoot (a : A) : PowerSeries A :=
  PowerSeries.rescale a (toddLine A)

/-- Coefficients of the universal one-root Chern character.-/
theorem coeff_chLine (n : ℕ) :
    PowerSeries.coeff n (chLine A) =
      algebraMap ℚ A ((1 : ℚ) / Nat.factorial n) := by
  simp [chLine, PowerSeries.coeff_exp]

/-- Coefficients of the Chern-character series for a scaled root.-/
theorem coeff_chRoot (a : A) (n : ℕ) :
    PowerSeries.coeff n (chRoot A a) =
      a ^ n * algebraMap ℚ A ((1 : ℚ) / Nat.factorial n) := by
  rw [chRoot, PowerSeries.coeff_rescale, coeff_chLine]

/-- Coefficients of the universal one-root Todd series.-/
theorem coeff_toddLine (n : ℕ) :
    PowerSeries.coeff n (toddLine A) =
      algebraMap ℚ A (bernoulli' n / Nat.factorial n) := by
  simp [toddLine, bernoulli'PowerSeries]

/-- Coefficients of the Todd series for a scaled root.-/
theorem coeff_toddRoot (a : A) (n : ℕ) :
    PowerSeries.coeff n (toddRoot A a) =
      a ^ n * algebraMap ℚ A (bernoulli' n / Nat.factorial n) := by
  rw [toddRoot, PowerSeries.coeff_rescale, coeff_toddLine]

@[simp]
theorem coeff_one_toddLine :
    PowerSeries.coeff 1 (toddLine A) = algebraMap ℚ A ((1 : ℚ) / 2) := by
  rw [coeff_toddLine]
  norm_num

@[simp]
theorem coeff_two_toddLine :
    PowerSeries.coeff 2 (toddLine A) = algebraMap ℚ A ((1 : ℚ) / 12) := by
  rw [coeff_toddLine]
  norm_num

@[simp]
theorem coeff_one_toddRoot (a : A) :
    PowerSeries.coeff 1 (toddRoot A a) =
      a * algebraMap ℚ A ((1 : ℚ) / 2) := by
  rw [coeff_toddRoot]
  norm_num

@[simp]
theorem coeff_two_toddRoot (a : A) :
    PowerSeries.coeff 2 (toddRoot A a) =
      a ^ 2 * algebraMap ℚ A ((1 : ℚ) / 12) := by
  rw [coeff_toddRoot]
  norm_num

@[simp]
theorem constantCoeff_chLine : PowerSeries.constantCoeff (chLine A) = 1 := by
  simp [chLine]

@[simp]
theorem constantCoeff_toddLine : PowerSeries.constantCoeff (toddLine A) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [toddLine, bernoulli'PowerSeries, bernoulli'_zero]

@[simp]
theorem constantCoeff_chRoot (a : A) :
    PowerSeries.constantCoeff (chRoot A a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_chRoot]
  simp

@[simp]
theorem constantCoeff_toddRoot (a : A) :
    PowerSeries.constantCoeff (toddRoot A a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_toddRoot]
  simp [bernoulli'_zero]

/-- Additivity of first Chern roots becomes multiplicativity of the Chern character.-/
theorem chRoot_add (a b : A) :
    chRoot A a * chRoot A b = chRoot A (a + b) := by
  simpa only [chRoot, chLine] using PowerSeries.exp_mul_exp_eq_exp_add a b

/-- The zero formal root contributes the multiplicative identity series.-/
@[simp]
theorem chRoot_zero : chRoot A 0 = 1 := by
  ext n
  rw [PowerSeries.coeff_one, coeff_chRoot]
  rcases n with (_ | n)
  · simp
  · simp [pow_succ]

/-- The zero formal root contributes the multiplicative identity Todd series.-/
@[simp]
theorem toddRoot_zero : toddRoot A 0 = 1 := by
  ext n
  rw [PowerSeries.coeff_one, coeff_toddRoot]
  rcases n with (_ | n)
  · simp [bernoulli'_zero]
  · simp [pow_succ]

/-- Opposite formal Chern roots are multiplicative inverses for the Chern character.  This is
the one-root algebraic law used by virtual bundles `[L] - [O]`.-/
theorem chRoot_neg_mul (a : A) :
    chRoot A (-a) * chRoot A a = 1 := by
  rw [chRoot_add, neg_add_cancel, chRoot_zero]

theorem chRoot_mul_neg (a : A) :
    chRoot A a * chRoot A (-a) = 1 := by
  rw [chRoot_add, add_neg_cancel, chRoot_zero]

/-- The defining Todd functional equation
`td(X) * (exp(X) - 1) = X * exp(X)`.-/
theorem toddLine_mul_exp_sub_one :
    toddLine A * (chLine A - 1) = PowerSeries.X * chLine A := by
  simpa only [toddLine, chLine] using bernoulli'PowerSeries_mul_exp_sub_one A

end CharacteristicClasses
