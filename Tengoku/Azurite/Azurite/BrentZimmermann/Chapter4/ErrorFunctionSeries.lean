/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.ErrorFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.4/§4.5 (continued): the error function as an integral and its series

Our `erf` was defined through the tail integral `erfc x = (2/√π) ∫_x^∞ e^(−u²) du`.  Here:

* `erf_eq_integral`: `erf x = (2/√π) ∫_0^x e^(−u²) du` (from `∫_0^∞ e^(−u²) = √π/2`), hence
  `erf_neg` (`erf` is odd), `erf_zero`;
* (4.22) `hasSum_erf_series`: `erf x = (2/√π) ∑_{j≥0} (−1)^j x^(2j+1)/(j! (2j+1))`, by integrating
  the exponential series term by term (dominated convergence on `[0, x]`);
* (4.23) `hasSum_erf_exp_series`: `erf x = (2/√π) e^(−x²) ∑_{j≥0} 2^j x^(2j+1)/(1·3·5⋯(2j+1))`:
  the series `S(x) = ∑ c_j x^(2j+1)`, `c_j = 2^j/(2j+1)‼`, satisfies `S' = 1 + 2xS` (term-by-term
  differentiation on a ball, `c_{j+1}(2j+3) = 2c_j`), so `e^(−x²) S(x) − ∫_0^x e^(−u²)` has zero
  derivative and vanishes at `0`.
-/

namespace Azurite

namespace BZ

open Real MeasureTheory Set Filter Topology Finset
open scoped Interval

/-! ### The integral representation -/

/--
@isnad1 id=eq.0h1v.s6.1702a844eb9d from=translated src=- shape=afd9be4a vocab=38336f4c
-/
theorem gaussTail_zero_eq (x : ℝ) :
    gaussTail 0 x = Real.sqrt π / 2 - ∫ u in (0 : ℝ)..x, exp (-u ^ 2) := by
  unfold gaussTail
  simp only [mul_zero, pow_zero, div_one]
  have h := intervalIntegral.integral_Ioi_sub_Ioi' (integrableOn_exp_neg_sq_Ioi 0)
    (integrableOn_exp_neg_sq_Ioi x)
  have hg : ∫ u in Ioi (0 : ℝ), exp (-u ^ 2) = Real.sqrt π / 2 := by
    have := integral_gaussian_Ioi 1
    simpa using this
  linarith

/-- `erf x = (2/√π) ∫_0^x e^(−u²) du`.
@isnad1 id=eq.0h1v.s6.3142bb3055fd from=translated src=- shape=ef8aeaba vocab=186accab
-/
theorem erf_eq_integral (x : ℝ) : erf x = 2 / Real.sqrt π * ∫ u in (0 : ℝ)..x, exp (-u ^ 2) := by
  rw [erf, erfc, gaussTail_zero_eq]
  have hpi : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
  field_simp
  ring

/--
@isnad1 id=eq.0h0v.s3.777869ab4391 from=translated src=- shape=3c26ae4f vocab=172c396c
-/
theorem erf_zero : erf 0 = 0 := by simp [erf_eq_integral]

/-- `erf` is odd.
@isnad1 id=eq.0h1v.s3.fe5b128ba0fb from=translated src=- shape=c7188113 vocab=09c59d6f
-/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  rw [erf_eq_integral, erf_eq_integral]
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) (fun u : ℝ => exp (-u ^ 2))
  simp only [neg_sq, neg_zero] at h
  rw [intervalIntegral.integral_symm (0 : ℝ) (-x)] at h
  rw [← neg_eq_iff_eq_neg.mpr h]
  ring

/-! ### (4.22): the alternating series -/

/--
@isnad1 id=eq.0h2v.s7.f1a349240825 from=translated src=- shape=e77383a3 vocab=737c6f2a
-/
theorem integral_neg_sq_pow_div_factorial (x : ℝ) (j : ℕ) :
    ∫ u in (0 : ℝ)..x, (-u ^ 2) ^ j / j.factorial
      = (-1) ^ j * x ^ (2 * j + 1) / (j.factorial * (2 * j + 1)) := by
  have : (fun u : ℝ => (-u ^ 2) ^ j / j.factorial)
      = fun u => ((-1 : ℝ) ^ j / j.factorial) * u ^ (2 * j) := by
    funext u
    rw [neg_pow (u ^ 2), pow_mul]
    ring
  rw [this, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

/-- `t² ≤ x²` for `t ∈ Ι 0 x`.
@isnad1 id=le.1h2v.s5.c2e9ef9830af from=translated src=- shape=45f782d3 vocab=95899ea8
-/
theorem sq_le_sq_of_mem_uIoc {x t : ℝ} (ht : t ∈ Ι (0 : ℝ) x) : t ^ 2 ≤ x ^ 2 := by
  rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact pow_le_pow_left₀ h1.le h2 2
  · have h := sq_le_sq' (a := t) (b := -x) (by linarith) (by linarith)
    rwa [neg_sq] at h

/-- (4.22): `erf x = (2/√π) ∑_{j≥0} (−1)^j x^(2j+1)/(j! (2j+1))`.
@isnad1 id=hassum.0h1v.s7.5f4bf143163a from=translated src=- shape=1f24a1af vocab=95fcf283
-/
theorem hasSum_erf_series (x : ℝ) :
    HasSum
      (fun j : ℕ => 2 / Real.sqrt π * ((-1) ^ j * x ^ (2 * j + 1) / (j.factorial * (2 * j + 1))))
      (erf x) := by
  rw [erf_eq_integral]
  refine HasSum.mul_left _ ?_
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun j : ℕ => fun t : ℝ => (-t ^ 2) ^ j / j.factorial) (f := fun t => exp (-t ^ 2))
    (a := 0) (b := x) (μ := volume) (fun j _ => (x ^ 2) ^ j / j.factorial)
    (fun j =>
      (by fun_prop : Continuous fun t : ℝ => (-t ^ 2) ^ j / j.factorial).aestronglyMeasurable)
    (fun j => Eventually.of_forall fun t ht => ?_)
    (Eventually.of_forall fun t _ => Real.summable_pow_div_factorial (x ^ 2))
    intervalIntegrable_const
    (Eventually.of_forall fun t _ => hasSum_exp_series (-t ^ 2))
  · have hfun : (fun j : ℕ => ∫ t in (0 : ℝ)..x, (-t ^ 2) ^ j / j.factorial)
        = fun j : ℕ => (-1) ^ j * x ^ (2 * j + 1) / (j.factorial * (2 * j + 1)) :=
      funext (integral_neg_sq_pow_div_factorial x)
    rwa [hfun] at key
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < j.factorial), abs_pow,
      abs_neg, abs_of_nonneg (sq_nonneg t)]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg t) (sq_le_sq_of_mem_uIoc ht) j)
      (by positivity)

/-! ### (4.23): the positive series -/

/-- The coefficients of (4.23): `c_j = 2^j/(1·3·5⋯(2j+1)) = 2^j/(2j+1)‼`.-/
noncomputable def erfExpCoeff (j : ℕ) : ℝ := 2 ^ j / (2 * j + 1).doubleFactorial

/--
@isnad1 id=lt.0h1v.s3.29ca7c970842 from=translated src=- shape=b9369acb vocab=ccbda483
-/
theorem erfExpCoeff_pos (j : ℕ) : 0 < erfExpCoeff j := by
  unfold erfExpCoeff
  have := Nat.doubleFactorial_pos (2 * j + 1)
  positivity

/--
@isnad1 id=eq.0h0v.s3.1fa3dc5e8b82 from=translated src=- shape=1ac31801 vocab=bdc0d094
-/
theorem erfExpCoeff_zero : erfExpCoeff 0 = 1 := by
  unfold erfExpCoeff
  norm_num [Nat.doubleFactorial]

/-- `c_{j+1} (2j+3) = 2 c_j`.
@isnad1 id=eq.0h1v.s6.f7f3ed6b07b6 from=translated src=- shape=edee2163 vocab=4ee03fed
-/
theorem erfExpCoeff_succ (j : ℕ) : erfExpCoeff (j + 1) * (2 * j + 3) = 2 * erfExpCoeff j := by
  unfold erfExpCoeff
  rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, Nat.doubleFactorial_add_two]
  have := Nat.doubleFactorial_pos (2 * j + 1)
  push_cast
  field_simp
  ring

/-- The term `c_j x^(2j+1)` of (4.23).-/
noncomputable def erfExpTerm (j : ℕ) (x : ℝ) : ℝ := erfExpCoeff j * x ^ (2 * j + 1)

/-- Its derivative `c_j (2j+1) x^(2j)`.-/
noncomputable def erfExpTerm' (j : ℕ) (x : ℝ) : ℝ := erfExpCoeff j * (2 * j + 1) * x ^ (2 * j)

/--
@isnad1 id=hasderiv.0h2v.s5.b11749c97595 from=translated src=- shape=f4cbe5c8 vocab=75244520
-/
theorem hasDerivAt_erfExpTerm (j : ℕ) (x : ℝ) :
    HasDerivAt (erfExpTerm j) (erfExpTerm' j x) x := by
  have h := (hasDerivAt_pow (2 * j + 1) x).const_mul (erfExpCoeff j)
  refine h.congr_deriv ?_
  unfold erfExpTerm'
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- The uniform bound on a ball of radius `R`: `|c_j (2j+1) x^(2j)| ≤ c_j (2j+1) R^(2j)`.-/
noncomputable def erfExpBound (R : ℝ) (j : ℕ) : ℝ := erfExpCoeff j * (2 * j + 1) * R ^ (2 * j)

/--
@isnad1 id=eq.0h2v.s6.bf5371640a51 from=translated src=- shape=103e9089 vocab=2a96ed68
-/
theorem erfExpBound_succ (R : ℝ) (j : ℕ) :
    erfExpBound R (j + 1) = erfExpBound R j * (2 * R ^ 2 / (2 * j + 1)) := by
  unfold erfExpBound
  have h := erfExpCoeff_succ j
  have hj : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  have e : erfExpCoeff j * (2 * j + 1) * R ^ (2 * j) * (2 * R ^ 2 / (2 * j + 1))
      = 2 * erfExpCoeff j * R ^ (2 * j) * R ^ 2 := by
    field_simp
  rw [e, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  push_cast
  linear_combination (R ^ (2 * j) * R ^ 2) * h

/--
@isnad1 id=le.0h2v.s4.bdd8fb3d9b99 from=translated src=- shape=25b8bdde vocab=e5eb8b64
-/
theorem erfExpBound_nonneg (R : ℝ) (j : ℕ) : 0 ≤ erfExpBound R j := by
  unfold erfExpBound
  have := erfExpCoeff_pos j
  exact mul_nonneg (by positivity) (Even.pow_nonneg (even_two_mul j) R)

/--
@isnad1 id=summable.0h1v.s3.cc1e2c7d4d1e from=translated src=- shape=07cc7679 vocab=b8132002
-/
theorem summable_erfExpBound (R : ℝ) : Summable (erfExpBound R) := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * R ^ 2)
  refine ⟨N, fun j hj => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (erfExpBound_nonneg R _),
    abs_of_nonneg (erfExpBound_nonneg R _), erfExpBound_succ, mul_comm (1 / 2 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (erfExpBound_nonneg R j)
  have hjN : (N : ℝ) ≤ j := by exact_mod_cast hj
  rw [div_le_iff₀ (by positivity)]
  linarith

/--
@isnad1 id=le.1h3v.s4.2dd2515eb13d from=translated src=- shape=6ff8ecba vocab=aef540dd
-/
theorem abs_erfExpTerm'_le {R x : ℝ} (hx : |x| ≤ R) (j : ℕ) :
    ‖erfExpTerm' j x‖ ≤ erfExpBound R j := by
  rw [Real.norm_eq_abs, erfExpTerm', erfExpBound, abs_mul, abs_pow,
    abs_of_pos (by have := erfExpCoeff_pos j; positivity : (0 : ℝ) < erfExpCoeff j * (2 * j + 1))]
  refine mul_le_mul_of_nonneg_left ?_ (by have := erfExpCoeff_pos j; positivity)
  exact pow_le_pow_left₀ (abs_nonneg x) hx _

/--
@isnad1 id=summable.0h1v.s4.cb8e24657c79 from=translated src=- shape=0b46e227 vocab=26d3cabf
-/
theorem summable_erfExpTerm (x : ℝ) : Summable fun j => erfExpTerm j x := by
  refine Summable.of_norm_bounded ((summable_erfExpBound (|x| + 1)).mul_left (|x| + 1)) fun j => ?_
  rw [Real.norm_eq_abs, erfExpTerm, erfExpBound, abs_mul, abs_pow,
    abs_of_pos (erfExpCoeff_pos j), pow_succ, pow_mul, pow_mul]
  have hc := erfExpCoeff_pos j
  have h1 : |x| ^ 2 ≤ (|x| + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) (by linarith) 2
  have h2 : (|x| ^ 2) ^ j ≤ ((|x| + 1) ^ 2) ^ j := pow_le_pow_left₀ (by positivity) h1 j
  have h3 : (1 : ℝ) ≤ 2 * j + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  calc erfExpCoeff j * ((|x| ^ 2) ^ j * |x|)
      ≤ erfExpCoeff j * (((|x| + 1) ^ 2) ^ j * (|x| + 1)) := by gcongr; linarith
    _ ≤ (|x| + 1) * (erfExpCoeff j * (2 * j + 1) * ((|x| + 1) ^ 2) ^ j) := by
        have : 0 ≤ erfExpCoeff j * ((|x| + 1) ^ 2) ^ j * (|x| + 1) := by positivity
        nlinarith

/-- `S(x) = ∑_{j≥0} c_j x^(2j+1)`.-/
noncomputable def erfExpSum (x : ℝ) : ℝ := ∑' j, erfExpTerm j x

/--
@isnad1 id=eq.0h0v.s3.176f644e2ba1 from=translated src=- shape=3c26ae4f vocab=e6b0d103
-/
theorem erfExpSum_zero : erfExpSum 0 = 0 := by
  simp [erfExpSum, erfExpTerm]

/--
@isnad1 id=hasderiv.0h1v.s5.9f4685fced68 from=translated src=- shape=4c625f43 vocab=5659ff7a
-/
theorem hasDerivAt_erfExpSum (x : ℝ) :
    HasDerivAt erfExpSum (∑' j, erfExpTerm' j x) x := by
  set R := |x| + 1 with hR
  have hball : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hR]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_self, hR]; positivity
  exact hasDerivAt_tsum_of_isPreconnected (summable_erfExpBound R) Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected (fun j y _ => hasDerivAt_erfExpTerm j y)
    (fun j y hy => abs_erfExpTerm'_le (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy; exact hy.le) j) h0
    (summable_erfExpTerm 0) hball

/-- The differential equation `S'(x) = 1 + 2x S(x)`.
@isnad1 id=eq.0h1v.s5.df54c78f6bd5 from=translated src=- shape=c859fa73 vocab=556eb6c8
-/
theorem tsum_erfExpTerm' (x : ℝ) : ∑' j, erfExpTerm' j x = 1 + 2 * x * erfExpSum x := by
  have hs : Summable fun j => erfExpTerm' j x :=
    Summable.of_norm_bounded (summable_erfExpBound (|x| + 1))
      fun j => abs_erfExpTerm'_le (by linarith) j
  rw [← Summable.sum_add_tsum_nat_add' (f := fun j => erfExpTerm' j x) (k := 1)
    ((summable_nat_add_iff 1).mpr hs), sum_range_one]
  have h0 : erfExpTerm' 0 x = 1 := by simp [erfExpTerm', erfExpCoeff_zero]
  rw [h0, erfExpSum, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  unfold erfExpTerm' erfExpTerm
  have h := erfExpCoeff_succ j
  push_cast
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ]
  linear_combination x ^ (2 * j + 1) * x * h

/-- (4.23) as an identity for the Gaussian integral: `∫_0^x e^(−u²) du = e^(−x²) S(x)`.
@isnad1 id=eq.0h1v.s6.d4313e0a8b67 from=translated src=- shape=57c14b4f vocab=dd0446c7
-/
theorem integral_exp_neg_sq_eq (x : ℝ) :
    ∫ u in (0 : ℝ)..x, exp (-u ^ 2) = exp (-x ^ 2) * erfExpSum x := by
  set G : ℝ → ℝ := fun y => exp (-y ^ 2) * erfExpSum y - ∫ u in (0 : ℝ)..y, exp (-u ^ 2) with hG
  have hderiv : ∀ y, HasDerivAt G 0 y := by
    intro y
    have hin : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * y)) y := by
      refine (hasDerivAt_pow 2 y).neg.congr_deriv ?_
      push_cast
      ring
    have h1 : HasDerivAt (fun y : ℝ => exp (-y ^ 2)) (exp (-y ^ 2) * (-(2 * y))) y := hin.exp
    have h2 := h1.mul (hasDerivAt_erfExpSum y)
    have h3 : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, exp (-t ^ 2)) (exp (-y ^ 2)) y :=
      ((by fun_prop : Continuous fun t : ℝ => exp (-t ^ 2)).integral_hasStrictDerivAt 0 y)
        |>.hasDerivAt
    refine (h2.sub h3).congr_deriv ?_
    rw [tsum_erfExpTerm']
    ring
  have hconst := is_const_of_deriv_eq_zero (fun y => (hderiv y).differentiableAt)
    (fun y => (hderiv y).deriv) x 0
  have hG0 : G 0 = 0 := by simp [hG, erfExpSum_zero]
  have hGx : G x = 0 := by rw [hconst, hG0]
  simp only [hG] at hGx
  linarith

/-- (4.23): `erf x = (2/√π) e^(−x²) ∑_{j≥0} 2^j x^(2j+1)/(1·3·5⋯(2j+1))`.
@isnad1 id=eq.0h1v.s5.08c8eba512bc from=translated src=- shape=560cf0e4 vocab=965141c9
-/
theorem erf_eq_exp_mul_erfExpSum (x : ℝ) :
    erf x = 2 / Real.sqrt π * exp (-x ^ 2) * erfExpSum x := by
  rw [erf_eq_integral, integral_exp_neg_sq_eq, mul_assoc]

/--
@isnad1 id=hassum.0h1v.s6.5fcb75d6d83d from=translated src=- shape=ede89b5d vocab=c1c4ac22
-/
theorem hasSum_erf_exp_series (x : ℝ) :
    HasSum (fun j : ℕ => 2 / Real.sqrt π * exp (-x ^ 2) * (erfExpCoeff j * x ^ (2 * j + 1)))
      (erf x) := by
  rw [erf_eq_exp_mul_erfExpSum]
  exact (summable_erfExpTerm x).hasSum.mul_left _

end BZ

end Azurite
