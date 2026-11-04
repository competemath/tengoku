/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.GuardDigits
import Tengoku.Seed.Analysis.Complex.Trigonometric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.3.4: Doubling versus tripling

For `sinh x = (e^x − e^(−x)) / 2` the doubling formula `sinh (2x) = 2 sinh x cosh x` needs the
auxiliary `cosh`; since `cosh² − sinh² = 1` one may write `sinh (2x) = 2 sinh x √(1 + sinh² x)`
at the cost of a square root, which suggests the tripling formula

  `sinh (3x) = sinh x (3 + 4 sinh² x)`.                                                 (4.19)

Usually, however, reducing through `exp` with (4.18) is more efficient: a tripling step costs a
multiplication and a squaring, while two doublings cost two squarings and reduce by `4 > 3`.
The drawback of going through `exp` is cancellation in `e^x − e^(−x)` for small `|x|`, cured by

  `sinh x = (expm1 x − expm1 (−x)) / 2`.                                                (4.20)

* `sinh_two_mul'`, `sinh_two_mul_sqrt`, `sinh_three_mul'` — the three formulae, (4.19) in the
  text's form.
* `three_pow_lt_four_pow` — the arithmetic behind "two doublings beat one tripling": `k`
  triplings reduce by `3^k`, the `2k` squarings of equal cost reduce by `4^k`.
* `sinh_of_exp_perturbed`, `relError_sinh_of_exp_ge` — the cancellation: with the two
  exponentials carrying relative errors `±ρ`, the error of `(e^x − e^(−x))/2` is `ρ cosh x`,
  at least `|ρ| / (2x)` relative to `sinh x` for `0 < x`, unbounded as `x → 0`.
* `sinh_eq_expm1` — (4.20); `relError_sinh_expm1_le` — there the two terms add with the same
  sign, so relative errors `≤ η` in `expm1 (±x)` give relative error `≤ η` in `sinh x`.
-/

namespace Azurite

namespace BZ

open Real

/-! ### The three formulae -/

/--
@isnad1 id=eq.0h1v.s5.d7402295b3a7 from=translated src=- shape=1ddba068 vocab=b797531a
-/
theorem sinh_two_mul' (x : ℝ) : sinh (2 * x) = 2 * sinh x * cosh x := sinh_two_mul x

/-- `cosh x = √(1 + sinh² x)`, so the doubling formula can avoid `cosh` at the price of a
square root.
@isnad1 id=eq.0h1v.s5.e030be906c83 from=translated src=- shape=6506bda7 vocab=3a7feeac
-/
theorem cosh_eq_sqrt (x : ℝ) : cosh x = Real.sqrt (1 + sinh x ^ 2) := by
  rw [← cosh_sq', Real.sqrt_sq (cosh_pos x).le]

/--
@isnad1 id=eq.0h1v.s6.96ccfc893b1f from=translated src=- shape=a0932b17 vocab=5879fee1
-/
theorem sinh_two_mul_sqrt (x : ℝ) : sinh (2 * x) = 2 * sinh x * Real.sqrt (1 + sinh x ^ 2) := by
  rw [sinh_two_mul, cosh_eq_sqrt]

/-- (4.19).
@isnad1 id=eq.0h1v.s6.3340164c42cc from=translated src=- shape=82acea6d vocab=650baaf7
-/
theorem sinh_three_mul' (x : ℝ) : sinh (3 * x) = sinh x * (3 + 4 * sinh x ^ 2) := by
  rw [sinh_three_mul]; ring

/-- `3^k < 4^k` for `k ≥ 1`: `k` triplings (each a multiplication and a squaring) reduce the
argument less than the `2k` squarings of the same cost.
@isnad1 id=lt.1h1v.s5.59423ed1eee1 from=translated src=- shape=63c02f1f vocab=191dae4c
-/
theorem three_pow_lt_four_pow {k : ℕ} (hk : 1 ≤ k) : (3 : ℕ) ^ k < 4 ^ k :=
  Nat.pow_lt_pow_left (by norm_num) (by omega)

/-! ### Cancellation in `(e^x − e^(−x)) / 2` -/

/-- With `e^x` and `e^(−x)` carrying relative errors `ρ` and `−ρ`, the computed `sinh x` is off
by `ρ cosh x`.
@isnad1 id=eq.0h2v.s6.f860ffa19004 from=translated src=- shape=71baecaf vocab=68bf21f5
-/
theorem sinh_of_exp_perturbed (x ρ : ℝ) :
    (exp x * (1 + ρ) - exp (-x) * (1 - ρ)) / 2 - sinh x = ρ * cosh x := by
  rw [sinh_eq, cosh_eq]; ring

/-- `sinh x ≤ x exp x` (from `1 − 2x ≤ e^(−2x)`).
@isnad1 id=le.0h1v.s4.49c17405131f from=translated src=- shape=1b4eab40 vocab=b7d4001b
-/
theorem sinh_le_mul_exp (x : ℝ) : sinh x ≤ x * exp x := by
  rw [sinh_eq]
  have h := add_one_le_exp (-(2 * x))
  have hpos := exp_pos x
  have h2 : exp (-(2 * x)) = exp (-x) * exp (-x) := by rw [← exp_add]; ring_nf
  have h3 : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (-x)]

/-- The loss of significance: for `0 < x` the relative error of `(e^x − e^(−x))/2` computed
from exponentials with relative errors `±ρ` is at least `|ρ| / (2x)`.
@isnad1 id=le.1h2v.s7.d0bddded5cc8 from=translated src=- shape=d4cd64fd vocab=1b6e140a
-/
theorem relError_sinh_of_exp_ge {x : ℝ} (hx : 0 < x) (ρ : ℝ) :
    |ρ| / (2 * x) ≤ |(exp x * (1 + ρ) - exp (-x) * (1 - ρ)) / 2 - sinh x| / sinh x := by
  rw [sinh_of_exp_perturbed, abs_mul, abs_of_pos (cosh_pos x)]
  have hs : 0 < sinh x := by
    rw [sinh_eq]; linarith [exp_lt_exp.mpr (show -x < x by linarith)]
  rw [div_le_div_iff₀ (by positivity) hs]
  have h1 := sinh_le_mul_exp x
  have h2 : exp x ≤ 2 * cosh x := by rw [cosh_eq]; linarith [exp_pos (-x)]
  calc |ρ| * sinh x ≤ |ρ| * (x * exp x) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ |ρ| * (x * (2 * cosh x)) := by gcongr
    _ = |ρ| * cosh x * (2 * x) := by ring

/-! ### (4.20): `sinh` from `expm1` -/

/-- (4.20).
@isnad1 id=eq.0h1v.s5.15c0ee1a4920 from=translated src=- shape=9cb663e2 vocab=0c6f51fd
-/
theorem sinh_eq_expm1 (x : ℝ) : sinh x = (expm1 x - expm1 (-x)) / 2 := by
  unfold expm1; rw [sinh_eq]; ring

/-- For `x ≥ 0` the two terms of (4.20) have the same sign (`expm1 x ≥ 0 ≥ expm1 (−x)`), so
relative errors `|ρ₁|, |ρ₂| ≤ η` in them give a relative error at most `η` in `sinh x`.
@isnad1 id=le.3h4v.s7.1d6fe782ddf1 from=translated src=- shape=d93522bf vocab=34202676
-/
theorem relError_sinh_expm1_le {x : ℝ} (hx : 0 ≤ x) {ρ₁ ρ₂ η : ℝ} (h₁ : |ρ₁| ≤ η) (h₂ : |ρ₂| ≤ η) :
    |(expm1 x * (1 + ρ₁) - expm1 (-x) * (1 + ρ₂)) / 2 - sinh x| ≤ η * sinh x := by
  have hid : (expm1 x * (1 + ρ₁) - expm1 (-x) * (1 + ρ₂)) / 2 - sinh x
      = (expm1 x * ρ₁ - expm1 (-x) * ρ₂) / 2 := by rw [sinh_eq_expm1]; ring
  have he₁ : 0 ≤ expm1 x := by unfold expm1; linarith [one_le_exp_iff.mpr hx]
  have he₂ : expm1 (-x) ≤ 0 := by
    unfold expm1; linarith [exp_le_one_iff.mpr (neg_nonpos.mpr hx)]
  rw [hid, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_iff₀ (by norm_num),
    sinh_eq_expm1]
  calc |expm1 x * ρ₁ - expm1 (-x) * ρ₂| ≤ |expm1 x * ρ₁| + |expm1 (-x) * ρ₂| := abs_sub _ _
    _ = expm1 x * |ρ₁| + (-expm1 (-x)) * |ρ₂| := by
        rw [abs_mul, abs_mul, abs_of_nonneg he₁, abs_of_nonpos he₂]
    _ ≤ expm1 x * η + (-expm1 (-x)) * η := by gcongr; linarith
    _ = η * ((expm1 x - expm1 (-x)) / 2) * 2 := by ring

end BZ

end Azurite
