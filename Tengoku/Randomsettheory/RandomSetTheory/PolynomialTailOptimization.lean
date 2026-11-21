/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.MartingaleFukNagaev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit confidence parameters for the polynomial martingale tail bound

This file optimizes the three terms proved in `MartingaleFukNagaev`:

`A / y^q + exp (-t^2 / (8 V)) + r! * (8 y / t)^r`.

Splitting the error budget equally gives the explicit choices

* `y = (3 A / u)^(1/q)`;
* `g = sqrt (8 V log (3/u))`;
* `p = 8 y * (3 r! / u)^(1/r)`;
* `t = g + p`.

Thus the available Bernstein--Fuk--Nagaev theorem gives confidence `u`, but
its polynomial deviation contains the additional factor `u^(-1/r)`.  Since
`y` itself has scale `A^(1/q) u^(-1/q)`, this route yields scale
`A^(1/q) u^(-1/q-1/r)`, not Marchina's sharp
`A^(1/q) u^(-1/q)` scale for any fixed finite `r`.

The final section formalizes this obstruction: controlling the polynomial
Bernstein remainder forces
`t >= 8 y * (3 r! / u)^(1/r)`.  Removing this factor requires the missing
Rio--Pinelis integrated-quantile comparison, rather than a different algebraic
choice of `t` and `y` in the theorem currently available.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

/-! ## Deterministic allocation of the three tail terms -/

/-- A truncation level assigning at most `u/3` to the raw large-jump term.-/
def fukNagaevTruncationLevel (q : ℕ) (A u : ℝ) : ℝ :=
  (3 * A / u) ^ ((q : ℝ)⁻¹)

/-- The Gaussian part of the confidence threshold.-/
def fukNagaevGaussianDeviation (V u : ℝ) : ℝ :=
  sqrt (8 * V * log (3 / u))

/-- The deviation needed to assign at most `u/3` to the polynomial
Bernstein remainder.-/
def fukNagaevPolynomialDeviation (r : ℕ) (y u : ℝ) : ℝ :=
  8 * y * (3 * (r.factorial : ℝ) / u) ^ ((r : ℝ)⁻¹)

/-- The sum of the Gaussian and polynomial confidence thresholds.-/
def fukNagaevDeviation (r : ℕ) (V y u : ℝ) : ℝ :=
  fukNagaevGaussianDeviation V u +
    fukNagaevPolynomialDeviation r y u

theorem fukNagaevTruncationLevel_pos (q : ℕ)
    {A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    0 < fukNagaevTruncationLevel q A u := by
  unfold fukNagaevTruncationLevel
  positivity

theorem fukNagaevTruncationLevel_pow {q : ℕ} (hq : q ≠ 0)
    {A u : ℝ} (hA : 0 ≤ A) (hu : 0 < u) :
    fukNagaevTruncationLevel q A u ^ q = 3 * A / u := by
  unfold fukNagaevTruncationLevel
  exact Real.rpow_inv_natCast_pow (by positivity) hq

/-- Under the uniform moment bound `A = n * K^q`, the truncation level has
exactly the desired `n^(1/q) K u^(-1/q)` scale (up to the fixed allocation
constant `3^(1/q)`).-/
theorem fukNagaevTruncationLevel_uniformMoment_eq
    {q n : ℕ} (hq : q ≠ 0) {K u : ℝ}
    (hK : 0 ≤ K) (hu : 0 < u) :
    fukNagaevTruncationLevel q ((n : ℝ) * K ^ q) u =
      3 ^ ((q : ℝ)⁻¹) * (n : ℝ) ^ ((q : ℝ)⁻¹) * K *
        u ^ (-((q : ℝ)⁻¹)) := by
  unfold fukNagaevTruncationLevel
  rw [Real.div_rpow (by positivity) hu.le]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
    (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hK q))]
  rw [Real.mul_rpow (Nat.cast_nonneg n) (pow_nonneg hK q)]
  rw [Real.pow_rpow_inv_natCast hK hq]
  rw [Real.rpow_neg hu.le]
  ring

/-- At the optimized truncation level, the predictable moment-bias scale is
exactly `(u/3) * y`; hence it is smaller than the main polynomial scale `y`
for confidence parameters `u < 1`.-/
theorem momentBias_at_fukNagaevTruncationLevel_eq
    {q : ℕ} (hq : q ≠ 0) {A u : ℝ}
    (hA : 0 < A) (hu : 0 < u) :
    A / fukNagaevTruncationLevel q A u ^ (q - 1) =
      (u / 3) * fukNagaevTruncationLevel q A u := by
  let y := fukNagaevTruncationLevel q A u
  have hy : 0 < y := fukNagaevTruncationLevel_pos q hA hu
  have hyPow : y ^ q = 3 * A / u :=
    fukNagaevTruncationLevel_pow hq hA.le hu
  have hqOne : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
  have hpow : y ^ q = y ^ (q - 1) * y := by
    conv_lhs => rw [← Nat.sub_add_cancel hqOne]
    rw [pow_succ]
  change A / y ^ (q - 1) = (u / 3) * y
  calc
    A / y ^ (q - 1) = (A * y) / y ^ q := by
      rw [hpow]
      field_simp
    _ = (u / 3) * y := by
      rw [hyPow]
      field_simp

theorem fukNagaevPolynomialDeviation_pos (r : ℕ)
    {y u : ℝ} (hy : 0 < y) (hu : 0 < u) :
    0 < fukNagaevPolynomialDeviation r y u := by
  unfold fukNagaevPolynomialDeviation
  positivity

theorem fukNagaevPolynomialRoot_pow {r : ℕ} (hr : r ≠ 0)
    {u : ℝ} (hu : 0 < u) :
    ((3 * (r.factorial : ℝ) / u) ^ ((r : ℝ)⁻¹) : ℝ) ^ r =
      3 * (r.factorial : ℝ) / u := by
  exact Real.rpow_inv_natCast_pow (by positivity) hr

/-- The exact deterministic error-budget lemma.  It is deliberately stated
independently of probability, so all divisions and constants are visible.-/
theorem fukNagaev_three_term_le
    {A V y t u : ℝ} {q r : ℕ}
    (hy : 0 < y) (ht : 0 < t) (hV : 0 < V) (hu : 0 < u)
    (hraw : 3 * A ≤ u * y ^ q)
    (hgaussian : 8 * V * log (3 / u) ≤ t ^ 2)
    (hpolynomial :
      3 * (r.factorial : ℝ) * (8 * y) ^ r ≤ u * t ^ r) :
    A / y ^ q +
        (exp (-t ^ 2 / (8 * V)) +
          (r.factorial : ℝ) * (8 * y / t) ^ r) ≤ u := by
  have hyq : 0 < y ^ q := pow_pos hy q
  have htq : 0 < t ^ r := pow_pos ht r
  have hrawThird : A / y ^ q ≤ u / 3 := by
    rw [div_le_iff₀ hyq]
    nlinarith
  have hlogRatio : log (3 / u) ≤ t ^ 2 / (8 * V) := by
    rw [le_div_iff₀ (by positivity : 0 < 8 * V)]
    nlinarith
  have hthreeDiv : 0 < 3 / u := div_pos (by norm_num) hu
  have hgaussianThird : exp (-t ^ 2 / (8 * V)) ≤ u / 3 := by
    calc
      exp (-t ^ 2 / (8 * V)) ≤ exp (-log (3 / u)) := by
        apply exp_le_exp.mpr
        simpa only [neg_div] using neg_le_neg hlogRatio
      _ = u / 3 := by
        rw [Real.exp_neg, Real.exp_log hthreeDiv]
        field_simp
  have hpolyThird :
      (r.factorial : ℝ) * (8 * y / t) ^ r ≤ u / 3 := by
    have hdiv :
        ((r.factorial : ℝ) * (8 * y) ^ r) / t ^ r ≤ u / 3 := by
      rw [div_le_iff₀ htq]
      nlinarith
    convert hdiv using 1
    rw [div_pow]
    ring
  nlinarith

/-! ## Verification of the explicit choices -/

theorem fukNagaevGaussianDeviation_nonneg (V u : ℝ) :
    0 ≤ fukNagaevGaussianDeviation V u :=
  sqrt_nonneg _

theorem fukNagaevGaussianDeviation_sq
    {V u : ℝ} (hV : 0 ≤ V) (hu : 0 < u) (hu1 : u < 1) :
    fukNagaevGaussianDeviation V u ^ 2 =
      8 * V * log (3 / u) := by
  unfold fukNagaevGaussianDeviation
  rw [sq_sqrt]
  have hratio : 1 < 3 / u := by
    rw [lt_div_iff₀ hu]
    linarith
  exact mul_nonneg (mul_nonneg (by norm_num) hV) (Real.log_pos hratio).le

/-- The explicit Gaussian-plus-polynomial deviation allocates `u/3` to each
of the two bounded-martingale terms once the truncation level is fixed.-/
theorem fukNagaev_explicit_allocation
    {A V u : ℝ} {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hA : 0 < A) (hV : 0 < V) (hu : 0 < u) (hu1 : u < 1) :
    let y := fukNagaevTruncationLevel q A u
    let t := fukNagaevDeviation r V y u
    A / y ^ q +
        (exp (-t ^ 2 / (8 * V)) +
          (r.factorial : ℝ) * (8 * y / t) ^ r) ≤ u := by
  dsimp only
  let y := fukNagaevTruncationLevel q A u
  let g := fukNagaevGaussianDeviation V u
  let p := fukNagaevPolynomialDeviation r y u
  have hy : 0 < y := fukNagaevTruncationLevel_pos q hA hu
  have hg : 0 ≤ g := fukNagaevGaussianDeviation_nonneg V u
  have hp : 0 < p := fukNagaevPolynomialDeviation_pos r hy hu
  have ht : 0 < g + p := add_pos_of_nonneg_of_pos hg hp
  apply fukNagaev_three_term_le hy ht hV hu
  · rw [fukNagaevTruncationLevel_pow hq hA.le hu]
    field_simp
    norm_num
  · have hgSq := fukNagaevGaussianDeviation_sq hV.le hu hu1
    change 8 * V * log (3 / u) ≤ (g + p) ^ 2
    rw [← hgSq]
    nlinarith [sq_nonneg p]
  · have hroot := fukNagaevPolynomialRoot_pow hr hu
    have hpPow : p ^ r =
        (8 * y) ^ r * (3 * (r.factorial : ℝ) / u) := by
      change (8 * y *
        (3 * (r.factorial : ℝ) / u) ^ ((r : ℝ)⁻¹)) ^ r = _
      rw [mul_pow, hroot]
    have hple : p ^ r ≤ (g + p) ^ r := by
      exact pow_le_pow_left₀ hp.le (le_add_of_nonneg_left hg) r
    rw [← show fukNagaevDeviation r V y u = g + p by rfl]
    change 3 * (r.factorial : ℝ) * (8 * y) ^ r ≤
      u * (g + p) ^ r
    calc
      3 * (r.factorial : ℝ) * (8 * y) ^ r = u * p ^ r := by
        rw [hpPow]
        field_simp
      _ ≤ u * (g + p) ^ r := mul_le_mul_of_nonneg_left hple hu.le

/-! ## Probability corollary -/

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
  {mu : Measure Omega} (filtration : Filtration ℕ mOmega)

/-! ## Exact obstruction to the sharp `u^(-1/q)` scale -/

/-- Controlling the polynomial Bernstein remainder by `u/3` forces the
displayed power inequality.  This already shows that `t` cannot stay of the
same order as `y` uniformly as `u` tends to zero.-/
theorem polynomial_remainder_control_forces_power_deviation
    {r : ℕ} {y t u : ℝ} (ht : 0 < t)
    (hcontrol :
      (r.factorial : ℝ) * (8 * y / t) ^ r ≤ u / 3) :
    3 * (r.factorial : ℝ) * (8 * y) ^ r ≤ u * t ^ r := by
  have htPow : 0 < t ^ r := pow_pos ht r
  rw [div_pow] at hcontrol
  have hcontrol' :
      ((r.factorial : ℝ) * (8 * y) ^ r) / t ^ r ≤ u / 3 := by
    convert hcontrol using 1
    ring
  rw [div_le_iff₀ htPow] at hcontrol'
  nlinarith

/-- Stronger root form of the obstruction.  For every fixed positive integer
`r`, the required deviation contains exactly the extra factor
`(3 r! / u)^(1/r)`.-/
theorem polynomial_remainder_control_forces_deviation
    {r : ℕ} (hr : r ≠ 0) {y t u : ℝ}
    (ht : 0 < t) (hu : 0 < u)
    (hcontrol :
      (r.factorial : ℝ) * (8 * y / t) ^ r ≤ u / 3) :
    8 * y * (3 * (r.factorial : ℝ) / u) ^ ((r : ℝ)⁻¹) ≤ t := by
  have hpower := polynomial_remainder_control_forces_power_deviation
    ht hcontrol
  let c : ℝ := (3 * (r.factorial : ℝ) / u) ^ ((r : ℝ)⁻¹)
  have hcPow : c ^ r = 3 * (r.factorial : ℝ) / u := by
    exact fukNagaevPolynomialRoot_pow hr hu
  apply le_of_pow_le_pow_left₀ hr ht.le
  rw [mul_pow, hcPow]
  have huPower :
      (3 * (r.factorial : ℝ) / u) * (8 * y) ^ r ≤ t ^ r := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hu]
    nlinarith
  nlinarith

end ProbabilityTheory
