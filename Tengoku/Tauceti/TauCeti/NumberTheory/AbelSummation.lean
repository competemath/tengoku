/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
public import Tengoku

/-!
# Consequences of Abel summation for partial sums

Mathlib's `Mathlib/NumberTheory/AbelSummation.lean` proves the summation-by-parts identity
`∑_{k ≤ x} f k c k = f x ∑_{k ≤ x} c k - ∫ f' (t) ∑_{k ≤ t} c k dt` and derives convergence
criteria from it. This file draws two further consequences from a growth hypothesis on the
partial sums `∑_{1 ≤ k ≤ t} c k`.

* **A logarithmic weight.** Mathlib's `summable_mul_of_bigO_atTop'` converts a bound on the partial
  sums of a sequence into the convergence of a weighted series, provided the weight is
  differentiable and the derivative of the weight against the partial sums admits an integrable
  majorant. This file performs that conversion once, for the weight `(t (1 + log t) ^ 3)⁻¹` and
  partial sums growing like `t log t`. The weight is written with `1 + log t` rather than `log t`
  so that it stays positive and smooth at `t = 1`, where Abel summation starts. Its derivative
  against an `O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, which is integrable at
  infinity by comparison with Mathlib's log-Cauchy density
  `integrableOn_Ioi_zero_inv_mul_one_add_log_sq`.
* **A power weight.** If the partial sums grow like `κ x`, then the partial sums weighted by
  `n ^ τ`, for an exponent `τ > -1`, grow like `κ x ^ (τ + 1) / (τ + 1)`. This is the step that
  moves a Tauberian conclusion for the coefficients `a n n ^ (1 - σ)` back to the coefficients
  `a n`.

## Main declarations

* `TauCeti.summable_div_mul_one_add_log_cube`: if the partial sums `∑_{1 ≤ k ≤ t} u k` of a
  nonnegative sequence are `O(t log t)`, then `∑ u n / (n (1 + log n) ^ 3)` converges.
* `TauCeti.sum_Icc_rpow_mul_eq`: the exact Abel-summation identity for the weight `t ^ τ`.
* `TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`: if `x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then
  `(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)` for `τ > -1`.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

variable {t : ℝ}

/-! ### The comparison weight -/

/-- The weight `(t (1 + log t) ^ 3)⁻¹` against which a partial-sum bound is summed. -/
private noncomputable def decayWeight (t : ℝ) : ℝ := (t * (1 + Real.log t) ^ 3)⁻¹

/-! ### The hypotheses of Abel summation -/

/-! ### The weighted series -/

/-! ### Partial sums against a power weight -/

/-- Restricting a sequence to `n ≥ 1` does not change its sums over `Icc 0 m` against a weight,
provided the weight is read from `Icc 1 m`. -/
private lemma sum_Icc_zero_mul_ite (g c : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, g k * (if k = 0 then 0 else c k) =
      ∑ n ∈ Finset.Icc 1 m, g n * c n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  simp only [↓reduceIte, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp [hn0]

/-- The Abel-summation identity `sum_mul_eq_sub_integral_mul₀` for the weight `t ^ τ`:
`∑_{1 ≤ n ≤ x} n ^ τ c n = x ^ τ S(x) - τ ∫ t in 1..x, t ^ (τ - 1) S(t)` for `x ≥ 1`, where
`S(t) = ∑_{1 ≤ n ≤ t} c n`. -/
theorem sum_Icc_rpow_mul_eq (c : ℕ → ℝ) (τ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ τ * c n =
      x ^ τ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n -
        τ * ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n := by
  have hderiv : deriv (fun u : ℝ ↦ u ^ τ) = fun t ↦ τ * t ^ (τ - 1) :=
    funext fun t ↦ Real.deriv_rpow_const t τ
  have habel := sum_mul_eq_sub_integral_mul₀ (f := fun u : ℝ ↦ u ^ τ)
    (fun n ↦ if n = 0 then 0 else c n) (by simp) x
    (fun t ht ↦ (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt)
    (by
      refine ContinuousOn.integrableOn_Icc (fun t ht ↦ ?_)
      rw [hderiv]
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).const_mul
        τ).continuousWithinAt)
  have hsum (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else c k) =
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n := by
    simpa using sum_Icc_zero_mul_ite (fun _ ↦ 1) c ⌊t⌋₊
  simp only [sum_Icc_zero_mul_ite, hsum, hderiv] at habel
  rw [habel, intervalIntegral.integral_of_le hx, ← integral_const_mul]
  congr 2
  funext t
  ring

/-- **Partial sums weighted by a power.** If the partial sums of `c` grow like `κ x`, that is
`x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then for every exponent `τ > -1` the partial sums weighted by `n ^ τ`
grow like `κ x ^ (τ + 1) / (τ + 1)`:
`(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)`. No sign condition on `c` is needed. -/
theorem tendsto_rpow_inv_mul_sum_Icc_rpow_mul {c : ℕ → ℝ} {κ τ : ℝ} (hτ : -1 < τ)
    (h : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n) atTop (𝓝 κ)) :
    Tendsto (fun x : ℝ ↦ (x ^ (τ + 1))⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ τ * c n) atTop
      (𝓝 (κ / (τ + 1))) := by
  have hτ1 : 0 < τ + 1 := by linarith
  set S : ℝ → ℝ := fun t ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n with hS
  set E : ℝ → ℝ := fun t ↦ S t - κ * t with hE
  -- The partial sums are interval integrable above `1`, being a step function.
  have hE_int (x : ℝ) (hx : 1 ≤ x) : IntervalIntegrable E volume 1 x := by
    have hS_int : IntervalIntegrable S volume 1 x := by
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr ?_
      simpa using integrableOn_mul_sum_Icc c (m := 1) zero_le_one
        (continuous_const (y := (1 : ℝ))).integrableOn_Icc
    exact hS_int.sub ((continuous_const.mul continuous_id).intervalIntegrable 1 x)
  -- The hypothesis says `E t = o(t)`.
  have hEo : E =o[atTop] id := by
    refine (isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht h0
      exact absurd h0 ht.ne'
    · have h0 : Tendsto (fun t ↦ t⁻¹ * S t - κ) atTop (𝓝 0) := by
        simpa using h.sub_const κ
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [hE, id]
      field_simp
  have hI := (isLittleO_integral_rpow_sub_one_mul hτ hE_int hEo).tendsto_div_nhds_zero
  have hpow : Tendsto (fun x : ℝ ↦ (x ^ (τ + 1))⁻¹) atTop (𝓝 0) :=
    (tendsto_rpow_atTop hτ1).inv_tendsto_atTop
  have hlim := ((h.sub (hI.const_mul τ)).sub_const (τ * κ / (τ + 1))).add
    (hpow.const_mul (τ * κ / (τ + 1)))
  have hval : κ - τ * 0 - τ * κ / (τ + 1) + τ * κ / (τ + 1) * 0 = κ / (τ + 1) := by
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  -- In the Abel-summation identity, split `S t = E t + κ t` inside the integral.
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hcont : ContinuousOn (fun t : ℝ ↦ t ^ (τ - 1)) (uIcc 1 x) := fun t ht ↦ by
    rw [uIcc_of_le hx] at ht
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt
  have hsplit : ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * S t =
      (∫ t in (1 : ℝ)..x, t ^ (τ - 1) * E t) + κ * ((x ^ (τ + 1) - 1) / (τ + 1)) := by
    have hκ : ∫ t in (1 : ℝ)..x, t ^ τ = (x ^ (τ + 1) - 1) / (τ + 1) := by
      rw [integral_rpow (Or.inl hτ), Real.one_rpow]
    rw [← hκ, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hE_int x hx).continuousOn_mul hcont)
        ((intervalIntegral.intervalIntegrable_rpow' hτ).const_mul κ)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [hE]
    rw [Real.rpow_sub_one ht0.ne']
    field_simp
    ring
  rw [sum_Icc_rpow_mul_eq c τ hx, hsplit, Real.rpow_add_one hx0.ne']
  have hxτ : 0 < x ^ τ := Real.rpow_pos_of_pos hx0 τ
  field_simp
  ring

end TauCeti
