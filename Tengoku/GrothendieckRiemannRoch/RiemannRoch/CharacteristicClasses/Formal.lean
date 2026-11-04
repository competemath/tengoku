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

/-- Coefficients of the universal one-root Chern character.
@isnad1 id=eq.0h2v.s7.0a23eec2b1f4 from=translated src=- shape=bfec6b64 vocab=b916000a
-/
theorem coeff_chLine (n : ℕ) :
    PowerSeries.coeff n (chLine A) =
      algebraMap ℚ A ((1 : ℚ) / Nat.factorial n) := by
  simp [chLine, PowerSeries.coeff_exp]

/-- Coefficients of the Chern-character series for a scaled root.
@isnad1 id=eq.0h3v.s8.77df36071487 from=translated src=- shape=9686bce5 vocab=03d9da9a
-/
theorem coeff_chRoot (a : A) (n : ℕ) :
    PowerSeries.coeff n (chRoot A a) =
      a ^ n * algebraMap ℚ A ((1 : ℚ) / Nat.factorial n) := by
  rw [chRoot, PowerSeries.coeff_rescale, coeff_chLine]

/-- Coefficients of the universal one-root Todd series.
@isnad1 id=eq.0h2v.s7.b73ef410a65f from=translated src=- shape=e3da1f76 vocab=e0c2163f
-/
theorem coeff_toddLine (n : ℕ) :
    PowerSeries.coeff n (toddLine A) =
      algebraMap ℚ A (bernoulli' n / Nat.factorial n) := by
  simp [toddLine, bernoulli'PowerSeries]

/-- Coefficients of the Todd series for a scaled root.
@isnad1 id=eq.0h3v.s8.db8fe798092c from=translated src=- shape=6c483d45 vocab=177c3347
-/
theorem coeff_toddRoot (a : A) (n : ℕ) :
    PowerSeries.coeff n (toddRoot A a) =
      a ^ n * algebraMap ℚ A (bernoulli' n / Nat.factorial n) := by
  rw [toddRoot, PowerSeries.coeff_rescale, coeff_toddLine]

/--
@isnad1 id=eq.0h1v.s7.384d9ef2b659 from=translated src=- shape=e39a0782 vocab=edb02221
-/
@[simp]
theorem coeff_one_toddLine :
    PowerSeries.coeff 1 (toddLine A) = algebraMap ℚ A ((1 : ℚ) / 2) := by
  rw [coeff_toddLine]
  norm_num

/--
@isnad1 id=eq.0h1v.s7.00936b7a8f02 from=translated src=- shape=e39a0782 vocab=edb02221
-/
@[simp]
theorem coeff_two_toddLine :
    PowerSeries.coeff 2 (toddLine A) = algebraMap ℚ A ((1 : ℚ) / 12) := by
  rw [coeff_toddLine]
  norm_num

/--
@isnad1 id=eq.0h2v.s8.7d9048db402b from=translated src=- shape=1b97bbd3 vocab=e90e6d0f
-/
@[simp]
theorem coeff_one_toddRoot (a : A) :
    PowerSeries.coeff 1 (toddRoot A a) =
      a * algebraMap ℚ A ((1 : ℚ) / 2) := by
  rw [coeff_toddRoot]
  norm_num

/--
@isnad1 id=eq.0h2v.s8.51d432c1684f from=translated src=- shape=77b796d2 vocab=0ef48b40
-/
@[simp]
theorem coeff_two_toddRoot (a : A) :
    PowerSeries.coeff 2 (toddRoot A a) =
      a ^ 2 * algebraMap ℚ A ((1 : ℚ) / 12) := by
  rw [coeff_toddRoot]
  norm_num

/--
@isnad1 id=eq.0h1v.s6.73661613a71a from=translated src=- shape=03f692ac vocab=097dbe2a
-/
@[simp]
theorem constantCoeff_chLine : PowerSeries.constantCoeff (chLine A) = 1 := by
  simp [chLine]

/--
@isnad1 id=eq.0h1v.s6.7ce7d81ebd4a from=translated src=- shape=03f692ac vocab=b205eef9
-/
@[simp]
theorem constantCoeff_toddLine : PowerSeries.constantCoeff (toddLine A) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [toddLine, bernoulli'PowerSeries, bernoulli'_zero]

/--
@isnad1 id=eq.0h2v.s6.2252e331cb0f from=translated src=- shape=df169495 vocab=85c03e2b
-/
@[simp]
theorem constantCoeff_chRoot (a : A) :
    PowerSeries.constantCoeff (chRoot A a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_chRoot]
  simp

/--
@isnad1 id=eq.0h2v.s6.23886519a6b1 from=translated src=- shape=df169495 vocab=b138573f
-/
@[simp]
theorem constantCoeff_toddRoot (a : A) :
    PowerSeries.constantCoeff (toddRoot A a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_toddRoot]
  simp [bernoulli'_zero]

/-- Additivity of first Chern roots becomes multiplicativity of the Chern character.
@isnad1 id=eq.0h3v.s6.c9cb8597425e from=translated src=- shape=34623b95 vocab=4bb3067d
-/
theorem chRoot_add (a b : A) :
    chRoot A a * chRoot A b = chRoot A (a + b) := by
  simpa only [chRoot, chLine] using PowerSeries.exp_mul_exp_eq_exp_add a b

/-- The zero formal root contributes the multiplicative identity series.
@isnad1 id=eq.0h1v.s5.b7aed2fa0856 from=translated src=- shape=299ab91c vocab=f3c88f20
-/
@[simp]
theorem chRoot_zero : chRoot A 0 = 1 := by
  ext n
  rw [PowerSeries.coeff_one, coeff_chRoot]
  rcases n with (_ | n)
  · simp
  · simp [pow_succ]

/-- The zero formal root contributes the multiplicative identity Todd series.
@isnad1 id=eq.0h1v.s5.196dc10acbe7 from=translated src=- shape=299ab91c vocab=b0b8de89
-/
@[simp]
theorem toddRoot_zero : toddRoot A 0 = 1 := by
  ext n
  rw [PowerSeries.coeff_one, coeff_toddRoot]
  rcases n with (_ | n)
  · simp [bernoulli'_zero]
  · simp [pow_succ]

/-- Opposite formal Chern roots are multiplicative inverses for the Chern character.  This is
the one-root algebraic law used by virtual bundles `[L] - [O]`.
@isnad1 id=eq.0h2v.s6.92f4c7b21d92 from=translated src=- shape=ab96d7b2 vocab=0dce1207
-/
theorem chRoot_neg_mul (a : A) :
    chRoot A (-a) * chRoot A a = 1 := by
  rw [chRoot_add, neg_add_cancel, chRoot_zero]

/--
@isnad1 id=eq.0h2v.s6.36e8a82082ab from=translated src=- shape=f13bfa98 vocab=0dce1207
-/
theorem chRoot_mul_neg (a : A) :
    chRoot A a * chRoot A (-a) = 1 := by
  rw [chRoot_add, add_neg_cancel, chRoot_zero]

/-- The defining Todd functional equation
`td(X) * (exp(X) - 1) = X * exp(X)`.
@isnad1 id=eq.0h1v.s6.17e7929a2066 from=translated src=- shape=46db660e vocab=8a625a14
-/
theorem toddLine_mul_exp_sub_one :
    toddLine A * (chLine A - 1) = PowerSeries.X * chLine A := by
  simpa only [toddLine, chLine] using bernoulli'PowerSeries_mul_exp_sub_one A

end CharacteristicClasses
