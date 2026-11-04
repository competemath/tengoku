/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.BernoulliRecurrence
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Tengoku.Seed.RingTheory.PowerSeries.Derivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.7.2 (continued): Tangent numbers

The tangent numbers `T_j` are defined by

  `tan x = ∑_{j≥1} T_j x^(2j−1)/(2j−1)!`,                                                     (4.61)

are positive integers, and are related to the Bernoulli numbers by

  `T_j = (−1)^(j−1) 2^(2j) (2^(2j) − 1) B_{2j} / (2j)`,                                       (4.62)

conversely `B_j = (−1)^(j/2−1) j T_{j/2} / (4^j − 2^j)` for even `j > 0` (`B_0 = 1`, `B_1 = −1/2`,
`B_j = 0` for odd `j > 1`).  (4.62) shows that the odd primes in the denominator of `B_{2j}` divide
`2^(2j) − 1` (in fact, by von Staudt–Clausen, `p ∣ den B_{2j}` iff `(p − 1) ∣ 2j`).

With `t = tan x` and `D = d/dx`, `Dt = 1 + t²` and `D(tⁿ) = n tⁿ⁻¹ (1 + t²)`, so `Dⁿ t = P_n(t)`
for polynomials `P_n(t) = ∑_j p_{n,j} t^j` with `P_0 = t`, `P_n = D P_{n−1}`, `deg P_n = n + 1` and

  `p_{n,j} = (j − 1) p_{n−1,j−1} + (j + 1) p_{n−1,j+1}`;                                      (4.63)

`p_{n,j} = 0` when `n + j` is even (`P_{2k}` odd, `P_{2k+1}` even polynomials).

What is formalized:

* `tanDerivPoly n : ℤ[X]` (`P_n`): `P_0 = X`, `P_{n+1} = P_n' (1 + X²)`; (4.63) as
  `coeff_tanDerivPoly_succ_zero` (`p_{n+1,0} = p_{n,1}`) and `coeff_tanDerivPoly_succ`
  (`p_{n+1,j+1} = j p_{n,j} + (j+2) p_{n,j+2}`); `coeff_tanDerivPoly_nonneg`; the parity
  `coeff_tanDerivPoly_eq_zero_of_even`; `coeff_tanDerivPoly_eq_zero_of_lt`,
  `coeff_tanDerivPoly_top` (`p_{n,n+1} = n!`) and `natDegree_tanDerivPoly` (`= n + 1`).
* `tanDerivPoly_succ_eq_sum` — the Leibniz form `P_{n+1} = [n = 0] + ∑_a C(n,a) P_a P_{n−a}`
  (so the exponential generating function `∑ P_n(0) xⁿ/n!` solves `y' = 1 + y²`).
* `iteratedDeriv_tan`: `Dⁿ tan x = P_n(tan x)` wherever `cos x ≠ 0`, hence
  `iteratedDeriv_tan_zero`: `Dⁿ tan 0 = p_{n,0}` — the Taylor coefficients of (4.61) are the
  `p_{2j−1,0}`.
* `tangentNumber j := p_{2j−1,0}` (so `T_j = D^(2j−1) tan 0`, `iteratedDeriv_tan_zero_eq`);
  `tangentNumber_one = 1`, `tangentNumber_two = 2`, `tangentNumber_three = 16`.
* (4.62) `tangentNumber_eq_bernoulli` and its inverse `bernoulli_two_mul_eq_tangentNumber`,
  proved through formal power series over `ℚ`: `tanDerivSeries = ∑ p_{n,0} Xⁿ/n!` satisfies
  `y' = 1 + y²` (from the Leibniz identity); the hyperbolic series `coshSeries`, `sinhSeries`,
  `tanhSeries = sinh/cosh` satisfy `tanh' = 1 − tanh²` and, from (4.57) scaled by `2` and `4`,
  `X tanh = ∑ (16^k − 4^k) C_k X^(2k)` (`X_mul_tanhSeries`), so
  `coeff (2k+1) tanh = (16^(k+1) − 4^(k+1)) C_{k+1}` and the even coefficients vanish; the
  sign-twisted `tanSeries` (`(−1)^k` at `X^(2k+1)`) then satisfies `y' = 1 + y²`
  (`derivative_tanSeries`), and the formal ODE with `y(0) = 0` has a unique solution
  (`eq_of_derivative_eq_one_add_sq`), giving `tanDerivSeries = tanSeries`.
* `tangentNumber_pos` (`T_j > 0`, from the sign of `B_{2j}`), `bernoulli_den_dvd`
  (`den B_{2j} ∣ 4^j (4^j − 1)`) and `odd_prime_dvd_den_bernoulli` (an odd prime dividing
  `den B_{2j}` divides `2^(2j) − 1`).

Not formalized: the analytic identity (4.61) itself (convergence for `|x| < π/2`; Mathlib has
no Taylor series for `tan`) — the Taylor coefficients are identified instead via
`iteratedDeriv_tan_zero`; von Staudt–Clausen is Mathlib's `Bernoulli.vonStaudt_clausen`.
-/

namespace Azurite

namespace BZ

open Finset

section Polys

open Polynomial

/-! ### The derivative polynomials `P_n` and the recurrence (4.63) -/

/-- `P_n`, with `Dⁿ tan = P_n(tan)`: `P_0 = X`, `P_{n+1} = P_n' (1 + X²)`.-/
noncomputable def tanDerivPoly : ℕ → ℤ[X]
  | 0 => X
  | n + 1 => derivative (tanDerivPoly n) * (1 + X ^ 2)

/--
@isnad1 id=eq.0h0v.s3.72f06e0357a9 from=translated src=- shape=58b8d025 vocab=d8497b11
-/
theorem tanDerivPoly_zero : tanDerivPoly 0 = X := rfl

/--
@isnad1 id=eq.0h1v.s7.0492250edcf5 from=translated src=- shape=3be6658d vocab=1b3f8683
-/
theorem tanDerivPoly_succ (n : ℕ) :
    tanDerivPoly (n + 1) = derivative (tanDerivPoly n) * (1 + X ^ 2) := rfl

/--
@isnad1 id=eq.0h0v.s6.be856dcdf26e from=translated src=- shape=8c20346b vocab=445f892f
-/
theorem tanDerivPoly_one : tanDerivPoly 1 = 1 + X ^ 2 := by
  rw [tanDerivPoly_succ, tanDerivPoly_zero, derivative_X, one_mul]

/-- (4.63) at `j = 0`: `p_{n+1,0} = p_{n,1}`.
@isnad1 id=eq.0h1v.s5.e96efe4476ae from=translated src=- shape=f97ad734 vocab=7faa0a8f
-/
theorem coeff_tanDerivPoly_succ_zero (n : ℕ) :
    (tanDerivPoly (n + 1)).coeff 0 = (tanDerivPoly n).coeff 1 := by
  rw [tanDerivPoly_succ, mul_add, mul_one, coeff_add, coeff_mul_X_pow', coeff_derivative]
  simp

/-- (4.63): `p_{n+1,j+1} = j p_{n,j} + (j+2) p_{n,j+2}`.
@isnad1 id=eq.0h2v.s6.c317579875ce from=translated src=- shape=0714c0f6 vocab=0e4b7b25
-/
theorem coeff_tanDerivPoly_succ (n j : ℕ) :
    (tanDerivPoly (n + 1)).coeff (j + 1)
      = j * (tanDerivPoly n).coeff j + (j + 2) * (tanDerivPoly n).coeff (j + 2) := by
  rw [tanDerivPoly_succ, mul_add, mul_one, coeff_add, coeff_mul_X_pow', coeff_derivative]
  rcases j with _ | j
  · simp
    ring
  · rw [ite_eq_left (by omega), show j + 1 + 1 - 2 = j by omega, coeff_derivative,
      show j + 1 + 2 = j + 1 + 1 + 1 from rfl]
    push_cast
    ring

/--
@isnad1 id=le.0h2v.s4.2fca2d8160d1 from=translated src=- shape=5e4deb02 vocab=5cabc276
-/
theorem coeff_tanDerivPoly_nonneg (n j : ℕ) : 0 ≤ (tanDerivPoly n).coeff j := by
  induction n generalizing j with
  | zero =>
    rw [tanDerivPoly_zero, coeff_X]
    split_ifs <;> norm_num
  | succ n ih =>
    rcases j with _ | j
    · rw [coeff_tanDerivPoly_succ_zero]; exact ih 1
    · rw [coeff_tanDerivPoly_succ]
      have h1 := ih j
      have h2 := ih (j + 2)
      positivity

/--
@isnad1 id=eq.1h2v.s5.7bd677ee51f0 from=translated src=- shape=8b3414a5 vocab=8a6c36a9
-/
theorem coeff_tanDerivPoly_eq_zero_of_lt (n : ℕ) : ∀ j, n + 1 < j →
    (tanDerivPoly n).coeff j = 0 := by
  induction n with
  | zero =>
    intro j hj
    rw [tanDerivPoly_zero, coeff_X, ite_eq_right (by omega)]
  | succ n ih =>
    intro j hj
    rcases j with _ | j
    · omega
    · rw [coeff_tanDerivPoly_succ, ih j (by omega), ih (j + 2) (by omega)]
      ring

/-- The leading coefficient: `p_{n,n+1} = n!`.
@isnad1 id=eq.0h1v.s4.a60513eaf69c from=translated src=- shape=ebabd384 vocab=4c6f6521
-/
theorem coeff_tanDerivPoly_top (n : ℕ) : (tanDerivPoly n).coeff (n + 1) = n.factorial := by
  induction n with
  | zero => simp [tanDerivPoly_zero, coeff_X]
  | succ n ih =>
    rw [coeff_tanDerivPoly_succ, ih, coeff_tanDerivPoly_eq_zero_of_lt n (n + 1 + 2) (by omega),
      Nat.factorial_succ]
    push_cast
    ring

/-- `deg P_n = n + 1`.
@isnad1 id=eq.0h1v.s4.7cadf1ef3e05 from=translated src=- shape=73ed59bb vocab=aefcb1c5
-/
theorem natDegree_tanDerivPoly (n : ℕ) : (tanDerivPoly n).natDegree = n + 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => coeff_tanDerivPoly_eq_zero_of_lt n N hN)
    (by rw [coeff_tanDerivPoly_top]; exact_mod_cast Nat.factorial_ne_zero n)

/-! ### The Leibniz identity -/

/-- Pascal's rule, summed: the inductive step of a binomial-type identity.
@isnad1 id=eq.0h3v.s7.15057f1eb425 from=translated src=- shape=40fe3ccc vocab=d3181fca
-/
theorem pascal_sum {R : Type*} [CommSemiring R] (q : ℕ → ℕ → R) (n : ℕ) :
    ∑ a ∈ range (n + 1), (n.choose a : R) * (q (a + 1) (n - a) + q a (n - a + 1))
      = ∑ a ∈ range (n + 2), ((n + 1).choose a : R) * q a (n + 1 - a) := by
  rw [sum_range_succ' (fun a => ((n + 1).choose a : R) * q a (n + 1 - a))]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Nat.choose_zero_right, Nat.cast_one,
    one_mul, Nat.sub_zero, Nat.add_sub_add_right, mul_add]
  rw [sum_add_distrib, sum_add_distrib, sum_range_succ (fun a => (n.choose (a + 1) : R) *
    q (a + 1) (n - a)), Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero,
    sum_range_succ' (fun a => (n.choose a : R) * q a (n - a + 1))]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  have : ∀ a ∈ range n, (n.choose (a + 1) : R) * q (a + 1) (n - (a + 1) + 1)
      = (n.choose (a + 1) : R) * q (a + 1) (n - a) := fun a ha => by
    rw [show n - (a + 1) + 1 = n - a by have := mem_range.mp ha; omega]
  rw [sum_congr rfl this]
  ring

/-- `P_{n+1} = [n = 0] + ∑_{a ≤ n} C(n, a) P_a P_{n−a}`: the Leibniz rule for `Dⁿ(1 + t²)`.
@isnad1 id=eq.0h1v.s7.5235e9203464 from=translated src=- shape=66448fa4 vocab=b30830cf
-/
theorem tanDerivPoly_succ_eq_sum (n : ℕ) :
    tanDerivPoly (n + 1)
      = (if n = 0 then 1 else 0)
        + ∑ a ∈ range (n + 1), (n.choose a : ℤ[X]) * (tanDerivPoly a * tanDerivPoly (n - a)) := by
  induction n with
  | zero =>
    rw [tanDerivPoly_one, sum_range_one]
    simp [tanDerivPoly_zero]
    ring
  | succ n ih =>
    rw [tanDerivPoly_succ, ih, derivative_add, derivative_sum, add_mul, sum_mul,
      ite_eq_right (Nat.succ_ne_zero n), zero_add]
    have hd : derivative (if n = 0 then (1 : ℤ[X]) else 0) = 0 := by split_ifs <;> simp
    rw [hd, zero_mul, zero_add]
    have hterm : ∀ a ∈ range (n + 1),
        derivative ((n.choose a : ℤ[X]) * (tanDerivPoly a * tanDerivPoly (n - a))) * (1 + X ^ 2)
          = (n.choose a : ℤ[X]) * (tanDerivPoly (a + 1) * tanDerivPoly (n - a)
            + tanDerivPoly a * tanDerivPoly (n - a + 1)) := fun a _ => by
      rw [derivative_natCast_mul, derivative_mul, tanDerivPoly_succ, tanDerivPoly_succ]
      ring
    rw [sum_congr rfl hterm]
    exact pascal_sum (fun a b => tanDerivPoly a * tanDerivPoly b) n

/-! ### `Dⁿ tan = P_n(tan)` -/

/-- `Dⁿ tan x = P_n(tan x)` wherever `cos x ≠ 0`.
@isnad1 id=eq.1h2v.s5.8750f60ac1e9 from=translated src=- shape=9d4e7891 vocab=c08c8309
-/
theorem iteratedDeriv_tan (n : ℕ) : ∀ x : ℝ, Real.cos x ≠ 0 →
    iteratedDeriv n Real.tan x
      = ((tanDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan x) := by
  induction n with
  | zero => intro x _; simp [tanDerivPoly_zero]
  | succ n ih =>
    intro x hx
    have hU : IsOpen {y : ℝ | Real.cos y ≠ 0} := isOpen_ne_fun Real.continuous_cos continuous_const
    have heq : iteratedDeriv n Real.tan =ᶠ[nhds x]
        fun y => ((tanDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan y) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => ih y hy
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd : HasDerivAt (fun y => ((tanDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan y))
        ((derivative ((tanDerivPoly n).map (Int.castRingHom ℝ))).eval (Real.tan x)
          * (1 / Real.cos x ^ 2)) x :=
      (Polynomial.hasDerivAt _ (Real.tan x)).comp x (Real.hasDerivAt_tan hx)
    rw [hd.deriv, tanDerivPoly_succ, Polynomial.map_mul, derivative_map, eval_mul, one_div,
      ← Real.inv_one_add_tan_sq hx, inv_inv]
    simp

/-! ### Tangent numbers -/

/-- The tangent numbers `T_j = p_{2j−1,0} = D^(2j−1) tan 0` (`j ≥ 1`).-/
noncomputable def tangentNumber (j : ℕ) : ℤ := (tanDerivPoly (2 * j - 1)).coeff 0

/--
@isnad1 id=eq.0h0v.s3.56deaf8297e3 from=translated src=- shape=1ac31801 vocab=41809480
-/
theorem tangentNumber_one : tangentNumber 1 = 1 := by
  simp [tangentNumber, tanDerivPoly_one]

/--
@isnad1 id=eq.0h0v.s3.96ab7904a515 from=translated src=- shape=1ac31801 vocab=41809480
-/
theorem tangentNumber_two : tangentNumber 2 = 2 := by
  rw [tangentNumber, show 2 * 2 - 1 = 2 + 1 by rfl, coeff_tanDerivPoly_succ_zero,
    coeff_tanDerivPoly_succ, tanDerivPoly_one]
  simp [coeff_X_pow, coeff_one]

/--
@isnad1 id=eq.0h0v.s3.02ce90a62150 from=translated src=- shape=1ac31801 vocab=41809480
-/
theorem tangentNumber_three : tangentNumber 3 = 16 := by
  rw [tangentNumber, show 2 * 3 - 1 = 4 + 1 by rfl, coeff_tanDerivPoly_succ_zero,
    show (4 : ℕ) = 3 + 1 by rfl, coeff_tanDerivPoly_succ, show (3 : ℕ) = 2 + 1 by rfl,
    coeff_tanDerivPoly_succ, show (2 : ℕ) = 1 + 1 by rfl, coeff_tanDerivPoly_succ,
    coeff_tanDerivPoly_succ, coeff_tanDerivPoly_succ, coeff_tanDerivPoly_succ,
    coeff_tanDerivPoly_succ, tanDerivPoly_one]
  simp [tanDerivPoly_zero, coeff_X]

end Polys

section Series

open PowerSeries

/-! ### The formal power series of `tan` from the polynomials -/

/-- `∑ p_{n,0} Xⁿ/n!`, the formal Taylor series of `tan` computed from the `P_n`.-/
noncomputable def tanDerivSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((tanDerivPoly n).coeff 0 : ℚ) / n.factorial

/-! ### The hyperbolic series over `ℚ` -/

/-- `e^(−x)`.-/
noncomputable def expNeg : PowerSeries ℚ := rescale (-1 : ℚ) (exp ℚ)

/--
@isnad1 id=eq.0h0v.s5.4626c21f38db from=translated src=- shape=94b39aaf vocab=0193eabb
-/
theorem exp_mul_expNeg : exp ℚ * expNeg = 1 := exp_mul_exp_neg_eq_one (A := ℚ)

/-- `cosh x = (e^x + e^(−x))/2`.-/
noncomputable def coshSeries : PowerSeries ℚ := C (1 / 2 : ℚ) * (exp ℚ + expNeg)

/-- `sinh x = (e^x − e^(−x))/2`.-/
noncomputable def sinhSeries : PowerSeries ℚ := C (1 / 2 : ℚ) * (exp ℚ - expNeg)

/-- `tanh x = sinh x / cosh x`.-/
noncomputable def tanhSeries : PowerSeries ℚ := sinhSeries * coshSeries⁻¹

/--
@isnad1 id=eq.0h0v.s6.7e7166fd11f9 from=translated src=- shape=3b67fda6 vocab=76c1db3f
-/
theorem coshSeries_sq_sub_sinhSeries_sq : coshSeries ^ 2 - sinhSeries ^ 2 = 1 := by
  unfold coshSeries sinhSeries
  have hc : C (1 / 2 : ℚ) * 2 = (1 : PowerSeries ℚ) := by
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  have h := exp_mul_expNeg
  linear_combination (C (1 / 2 : ℚ) * 2) ^ 2 * h + (C (1 / 2 : ℚ) * 2 + 1) * hc

/--
@isnad1 id=eq.0h0v.s5.a97e859b8294 from=translated src=- shape=8b3e5d3e vocab=08310f37
-/
theorem constantCoeff_coshSeries : constantCoeff coshSeries = 1 := by
  unfold coshSeries expNeg
  simp only [map_mul, map_add, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_exp,
    algebraMap_rat_rat]
  norm_num

/--
@isnad1 id=eq.0h0v.s5.a0e79e41face from=translated src=- shape=3b3ebab3 vocab=58d55846
-/
theorem coshSeries_mul_inv : coshSeries * coshSeries⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_coshSeries]; exact one_ne_zero)

/--
@isnad1 id=eq.0h0v.s5.195b69e3c338 from=translated src=- shape=8b3e5d3e vocab=141eb8e7
-/
theorem constantCoeff_tanhSeries : constantCoeff tanhSeries = 0 := by
  unfold tanhSeries sinhSeries expNeg
  simp only [map_mul, map_sub, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_exp,
    algebraMap_rat_rat]
  norm_num

/--
@isnad1 id=eq.0h2v.s7.a63e3b5da6f4 from=translated src=- shape=c33bfcba vocab=3341c6dc
-/
theorem rescale_C' (a r : ℚ) : rescale a (C r : PowerSeries ℚ) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

/-- (4.57) rescaled by `2`: `S(2x) (e^x − e^(−x)) = x (e^x + e^(−x))`.
@isnad1 id=eq.0h0v.s7.8a5a9e169be5 from=translated src=- shape=242c1e07 vocab=aaa9d04a
-/
theorem rescale_two_scaledBernoulliPowerSeries_mul :
    rescale (2 : ℚ) scaledBernoulliPowerSeries * (exp ℚ - expNeg) = X * (exp ℚ + expNeg) := by
  have h := congrArg (rescale (2 : ℚ)) scaledBernoulliPowerSeries_mul_sinh
  have hc : C (1 / 2 : ℚ) * C (2 : ℚ) = (1 : PowerSeries ℚ) := by rw [← map_mul]; norm_num
  simp only [map_mul, map_sub, map_add, rescale_X, rescale_C'] at h
  rw [← RingHom.comp_apply, ← rescale_mul, ← RingHom.comp_apply, ← rescale_mul] at h
  rw [show (1 / 2 : ℚ) * 2 = 1 by norm_num, show (-1 / 2 : ℚ) * 2 = -1 by norm_num, rescale_one,
    RingHom.id_apply] at h
  unfold expNeg
  linear_combination h + (X * (exp ℚ + rescale (-1 : ℚ) (exp ℚ))) * hc

/-- (4.57) rescaled by `4`: `S(4x) (e^(2x) − e^(−2x)) = 2x (e^(2x) + e^(−2x))`.
@isnad1 id=eq.0h0v.s8.0be636210d54 from=translated src=- shape=8955fad7 vocab=5f00662c
-/
theorem rescale_four_scaledBernoulliPowerSeries_mul :
    rescale (4 : ℚ) scaledBernoulliPowerSeries * (exp ℚ ^ 2 - expNeg ^ 2)
      = C 2 * X * (exp ℚ ^ 2 + expNeg ^ 2) := by
  have h := congrArg (rescale (4 : ℚ)) scaledBernoulliPowerSeries_mul_sinh
  have hc : C (1 / 2 : ℚ) * C (4 : ℚ) = C (2 : ℚ) := by rw [← map_mul]; norm_num
  simp only [map_mul, map_sub, map_add, rescale_X, rescale_C'] at h
  rw [← RingHom.comp_apply, ← rescale_mul, ← RingHom.comp_apply, ← rescale_mul] at h
  rw [show (1 / 2 : ℚ) * 4 = ((2 : ℕ) : ℚ) by norm_num, show (-1 / 2 : ℚ) * 4 = -1 + -1 by norm_num,
    ← exp_pow_eq_rescale_exp, ← exp_mul_exp_eq_exp_add, ← pow_two] at h
  unfold expNeg
  linear_combination h + (X * (exp ℚ ^ 2 + rescale (-1 : ℚ) (exp ℚ) ^ 2)) * hc

/-- `x tanh x = S(4x) − S(2x) = ∑ (16^k − 4^k) C_k x^(2k)`, i.e. `tanh x = 2 coth 2x − coth x`.
@isnad1 id=eq.0h0v.s7.43b31335ae1b from=translated src=- shape=63f81a6e vocab=8b2140b9
-/
theorem X_mul_tanhSeries :
    X * tanhSeries = rescale (4 : ℚ) scaledBernoulliPowerSeries
      - rescale (2 : ℚ) scaledBernoulliPowerSeries := by
  set S₂ := rescale (2 : ℚ) scaledBernoulliPowerSeries
  set S₄ := rescale (4 : ℚ) scaledBernoulliPowerSeries
  set u := exp ℚ
  set v := expNeg
  have h2 : S₂ * (u - v) = X * (u + v) := rescale_two_scaledBernoulliPowerSeries_mul
  have h4 : S₄ * (u ^ 2 - v ^ 2) = C 2 * X * (u ^ 2 + v ^ 2) :=
    rescale_four_scaledBernoulliPowerSeries_mul
  have huv : u * v = 1 := exp_mul_expNeg
  have hc : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
  rw [hc] at h4
  -- `(S₄ − S₂)(u + v)(u − v) = X (u − v)²`
  have hkey : (S₄ - S₂) * (u + v) * (u - v) = X * (u - v) ^ 2 := by
    linear_combination h4 - (u + v) * h2
  have hne : u - v ≠ 0 := by
    intro h0
    have := congrArg (coeff 1) h0
    rw [map_sub, map_zero] at this
    simp [u, v, expNeg, coeff_rescale, coeff_exp] at this
  have hcosh : (S₄ - S₂) * (u + v) = X * (u - v) := by
    apply mul_right_cancel₀ hne
    rw [hkey]; ring
  -- divide by `2 cosh`
  have hinv := coshSeries_mul_inv
  unfold tanhSeries sinhSeries
  have hcosh' : (S₄ - S₂) * coshSeries = X * (C (1 / 2 : ℚ) * (u - v)) := by
    unfold coshSeries
    linear_combination (C (1 / 2 : ℚ)) * hcosh
  calc X * (C (1 / 2 : ℚ) * (u - v) * coshSeries⁻¹)
      = (S₄ - S₂) * coshSeries * coshSeries⁻¹ := by rw [hcosh']; ring
    _ = S₄ - S₂ := by rw [mul_assoc, hinv, mul_one]

/--
@isnad1 id=eq.0h1v.s7.11b94a2818e1 from=translated src=- shape=0a3eb880 vocab=36c82e58
-/
theorem coeff_tanhSeries_odd (k : ℕ) :
    coeff (2 * k + 1) tanhSeries
      = (4 ^ (2 * (k + 1)) - 2 ^ (2 * (k + 1))) * scaledBernoulli (k + 1) := by
  have h := congrArg (coeff (2 * (k + 1))) X_mul_tanhSeries
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, coeff_succ_X_mul, map_sub, coeff_rescale,
    coeff_rescale, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
    coeff_scaledBernoulliPowerSeries_even] at h
  rw [h]
  ring

/--
@isnad1 id=eq.0h1v.s6.a1d79a87ca02 from=translated src=- shape=2c1fb0fa vocab=34e733dc
-/
theorem coeff_tanhSeries_even (k : ℕ) : coeff (2 * k) tanhSeries = 0 := by
  rcases k with _ | k
  · rw [mul_zero, coeff_zero_eq_constantCoeff_apply, constantCoeff_tanhSeries]
  · have h := congrArg (coeff (2 * (k + 1) + 1)) X_mul_tanhSeries
    rw [coeff_succ_X_mul, map_sub, coeff_rescale, coeff_rescale,
      coeff_scaledBernoulliPowerSeries_odd] at h
    rw [h]
    ring

/-! ### The sign twist `tanh ↦ tan` and the formal ODE -/

/-- The formal series of `tan` obtained from `tanh` by the sign twist `(−1)^k` at `x^(2k+1)`
(`tan x = −i tanh(ix)`).-/
noncomputable def tanSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (-1) ^ (n / 2) * coeff n tanhSeries

/--
@isnad1 id=eq.0h1v.s7.292c57f7057f from=translated src=- shape=532594db vocab=a5078ad2
-/
theorem coeff_tanSeries (n : ℕ) : coeff n tanSeries = (-1) ^ (n / 2) * coeff n tanhSeries :=
  coeff_mk _ _

/-- Products of two odd coefficients: the twist contributes `−(−1)^k` on the antidiagonal of `2k`.
@isnad1 id=eq.1h2v.s8.e6127e7c41d3 from=translated src=- shape=a6bb885f vocab=2134a990
-/
theorem tanSeries_mul_term {k : ℕ} {p : ℕ × ℕ} (hp : p ∈ antidiagonal (2 * k)) :
    coeff p.1 tanSeries * coeff p.2 tanSeries
      = -(-1) ^ k * (coeff p.1 tanhSeries * coeff p.2 tanhSeries) := by
  have hsum := mem_antidiagonal.mp hp
  rw [coeff_tanSeries, coeff_tanSeries]
  rcases Nat.even_or_odd p.1 with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [show p.1 = 2 * a by omega, coeff_tanhSeries_even]
    ring
  · obtain ⟨b, hb⟩ : ∃ b, p.2 = 2 * b + 1 := ⟨p.2 / 2, by omega⟩
    obtain rfl : k = a + b + 1 := by omega
    rw [show p.1 = 2 * a + 1 by omega, hb, show (2 * a + 1) / 2 = a by omega,
      show (2 * b + 1) / 2 = b by omega]
    ring

/-! ### (4.62) and consequences -/

end Series

end BZ

end Azurite
