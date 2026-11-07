/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Tengoku.Sendov.Sendov.Reduction.Polar
import Tengoku.Sendov.Sendov.Common.Sinh

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The simplified polar inequality `β(1) ≤ α/(3+α)`

This is `(lt) ⟹ (beta-bound)`.  Evaluating the integral,

  `∫₀¹ exp(α(-1 + (2-B)t)) dt = e^{-u} · sinh h / h`,   `u = αB/2`,  `h = α(2-B)/2`,

so `(lt)` says `e^u ≤ sinh h / h`, and `Sendov.log_sinh_div_le` turns that into
`u ≤ √(h²+9) - 3`.  Since `h = α - u`, squaring `u + 3 ≤ √((α-u)² + 9)` gives
`u(6 + 2α) ≤ α²`, that is `B ≤ α/(3+α)`.

The constant `3` is optimal: at `B = α/(3+α)` the slack in `(lt)` is `-α⁵/540 + α⁶/648`, so
the bound is tight to three orders at `α = 0`.  This is the one link of the chain with no room
in it anywhere.

One degenerate case has to be cleared first, and `(lt)` clears it: if `B ≥ 2` then the
integrand is at most `e^{-α} < 1` throughout, so the integral is below `1`.  Hence `B < 2` and
`h > 0`, which is what the `sinh` estimate needs.

## Main statements

* `Sendov.integral_exp_eq`: the closed form of the integral in `(lt)`;
* `Sendov.beta_lt_two`: `(lt)` forces `B < 2`;
* `Sendov.beta_le`: `(lt) ⟹ B ≤ α/(3+α)`.
-/

namespace Sendov

open MeasureTheory Real

variable {α B c : ℝ}

/-- `∫ₐᵇ exp(ct) dt = (exp(cb) - exp(ca))/c`.
@isnad1 id=eq.1h3v.s6.ed7a06b2b337 from=translated src=- shape=cd2c749f vocab=d843df6c
-/
lemma integral_exp_mul (hc : c ≠ 0) (a b : ℝ) :
    (∫ t in a..b, exp (c * t)) = (exp (c * b) - exp (c * a)) / c := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := b) (fun y : ℝ => exp y) hc
  rw [h, integral_exp]
  simp only [smul_eq_mul]
  field_simp

/-- The closed form of the integral in `(lt)`.
@isnad1 id=eq.2h2v.s7.bc71c07df5d7 from=translated src=- shape=5390e178 vocab=a066b6f6
-/
lemma integral_exp_eq (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = exp (-(α * B / 2)) * (sinh (α * (2 - B) / 2) / (α * (2 - B) / 2)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hEF : exp (-(α * B / 2)) = exp (-α) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : exp (α * (2 - B) * 1) = exp (α * (2 - B) / 2) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hneg : exp (-(α * (2 - B) / 2)) = (exp (α * (2 - B) / 2))⁻¹ := Real.exp_neg _
  have hF : exp (α * (2 - B) / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.sinh_eq, hEF, hsq, hneg]
  field_simp

/-- The same integral, in the form the logarithmic half of `(beta-bound)` uses.
@isnad1 id=eq.2h2v.s7.ac9cffd464de from=translated src=- shape=a1cca03f vocab=3bd52b7c
-/
lemma integral_exp_eq' (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = (exp (α * (1 - B)) - exp (-α)) / (α * (2 - B)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hsum : exp (-α) * exp (α * (2 - B) * 1) = exp (α * (1 - B)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hsum]
  field_simp

/-- `(lt)` forces `B < 2`: otherwise the integrand never exceeds `e^{-α} < 1`.
@isnad1 id=lt.2h2v.s6.3af08203f3c6 from=translated src=- shape=55acf1de vocab=99a1af9e
-/
lemma beta_lt_two (hα : 0 < α)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B < 2 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono : (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      ≤ ∫ _t in (0 : ℝ)..1, exp (-α) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous fun t : ℝ =>
        exp (α * (-1 + (2 - B) * t))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun _ : ℝ => exp (-α)).intervalIntegrable _ _) ?_
    intro u hu
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg (mul_nonneg hα.le hu.1) (sub_nonneg.2 hcon)]
  have hval : (∫ _t in (0 : ℝ)..1, exp (-α)) = exp (-α) := by simp
  have hone : exp (-α) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  rw [hval] at hmono
  linarith

/-- **`(lt) ⟹ (beta-bound)`.**  The `α/(3+α)` of the blog post.
@isnad1 id=le.3h2v.s7.eb4ba2333f0c from=translated src=- shape=f3b19a9d vocab=3dee0294
-/
theorem beta_le (hα : 0 < α) (hB0 : 0 ≤ B)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B ≤ α / (3 + α) := by
  have hB2 : B < 2 := beta_lt_two hα hlt
  rw [integral_exp_eq hα hB2] at hlt
  set u : ℝ := α * B / 2 with hudef
  set h : ℝ := α * (2 - B) / 2 with hhdef
  have hhpos : 0 < h := by
    rw [hhdef]
    have : 0 < 2 - B := by linarith
    positivity
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  -- `1 ≤ e^{-u} sinh h / h` is `e^u ≤ sinh h / h`
  have h1 : exp u ≤ sinh h / h := by
    rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos u)] at hlt
    linarith
  have h2 : u ≤ Real.log (sinh h / h) := by
    rw [← Real.log_exp u]
    exact Real.log_le_log (Real.exp_pos u) h1
  have h3 : u ≤ Real.sqrt (h ^ 2 + 9) - 3 := h2.trans (log_sinh_div_le hhpos)
  -- square; `h = α - u`
  have hhu : h = α - u := by rw [hhdef, hudef]; ring
  have hsq : Real.sqrt (h ^ 2 + 9) ^ 2 = h ^ 2 + 9 := Real.sq_sqrt (by positivity)
  have h4 : (u + 3) ^ 2 ≤ h ^ 2 + 9 := by
    have hnn : (0 : ℝ) ≤ u + 3 := by linarith
    nlinarith [h3, hsq, Real.sqrt_nonneg (h ^ 2 + 9)]
  have h5 : u * (6 + 2 * α) ≤ α ^ 2 := by rw [hhu] at h4; nlinarith [h4]
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 + α)]
  rw [hudef] at h5
  nlinarith [h5, hα]

/-- **The logarithmic half of `(beta-bound)`:** `log α ≤ α(1 - β(1))`.  From `(lt)`,
`e^{α(1-B)} ≥ α(2-B) + e^{-α} > α`, since `B ≤ 1` makes `2 - B ≥ 1`.
@isnad1 id=le.3h2v.s7.599352d3d4b1 from=translated src=- shape=b25191cf vocab=2eb7f705
-/
theorem log_le_alpha_mul (hα : 0 < α) (hB1 : B ≤ 1)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) :
    Real.log α ≤ α * (1 - B) := by
  have hB2 : B < 2 := by linarith
  rw [integral_exp_eq' hα hB2] at hlt
  have hden : (0 : ℝ) < α * (2 - B) := by
    have : (0 : ℝ) < 2 - B := by linarith
    positivity
  rw [le_div_iff₀ hden, one_mul] at hlt
  have hge : α ≤ α * (2 - B) := by nlinarith
  have hlt' : α < exp (α * (1 - B)) := by
    have := Real.exp_pos (-α)
    linarith
  exact (Real.log_le_iff_le_exp hα).2 hlt'.le

end Sendov
