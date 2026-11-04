/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.Reciprocal
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.2.3: Newton's method for (reciprocal) square roots

The case `m = 2` of (4.4): the iteration

  `x_{j+1} = x_j + x_j (1 − x_j² y) / 2`                                                (4.9)

converges to `y^(−1/2)` from a good enough start, with no division except by `2`; the square
root follows with one multiplication, `y^(1/2) = y · y^(−1/2)`.  Newton's method on `x² − y`
gives instead Heron's iteration

  `x_{j+1} = (x_j + y / x_j) / 2`                                                       (4.10)

which divides by `x_j` at every step; both converge quadratically.

The error of (4.9) is analysed exactly here.  With `u = 1 − x² y` (so `u = 0` iff `x = ±y^(−1/2)`),
`u_{j+1} = u_j² (3 + u_j) / 4`, hence `|u_{j+1}| ≤ u_j²` whenever `|u_j| ≤ 1`: the basin of
attraction contains every `x_0 > 0` with `x_0² y < 2`, and there `|u_j| ≤ |u_0|^(2^j)`.  In terms of
the relative error `x = ζ (1 + ε)`, one step gives `ε' = −(3 ε² + ε³) / 2`.

* `rsqrtStep`, `rsqrtSeq` — (4.9); `rsqrtStep_eq_inverseRootStep`.
* `rsqrtError` — `u = 1 − x² y`; `rsqrtError_rsqrtStep` (`u' = u²(3 + u)/4`),
  `abs_rsqrtError_rsqrtStep_le` (`|u| ≤ 1 → |u'| ≤ u²`), `abs_rsqrtError_rsqrtSeq_le`
  (`|u_j| ≤ |u_0|^(2^j)`), `rsqrtStep_rel` (`ε' = −(3ε² + ε³)/2`).
* `rsqrtSeq_pos`, `tendsto_rsqrtSeq` — from `x_0 > 0` with `x_0² y < 2` the iterates stay
  positive and converge to `(√y)⁻¹`; `inv_sqrt_eq_rpow` relates `(√y)⁻¹` to `y^(−1/2)`.
* `sqrt_eq_mul_inv_sqrt`, `mul_inv_sqrt_rel` — `√y = y · (√y)⁻¹`, and the multiplication
  preserves the relative error exactly.
* `heronStep`, `heronSeq` — (4.10); `newtonStep_sq_sub` (Newton's step for `x² − y`),
  `heronStep_sub_sqrt` (`x' − √y = (x − √y)² / (2x)`), `sqrt_le_heronStep`, `heronStep_le`,
  `heronStep_sub_sqrt_le` (`e' ≤ e²/(2√y)` and `e' ≤ e/2` once `x ≥ √y`), `tendsto_heronSeq`
  (convergence from every `x_0 > 0`).
-/

namespace Azurite

namespace BZ

open Set Filter Topology

/-- The reciprocal square root step (4.9), `x + x (1 − x² y) / 2`.-/
noncomputable def rsqrtStep (y x : ℝ) : ℝ := x + x * (1 - x ^ 2 * y) / 2

/-- The iterates of (4.9) from `x₀`.-/
noncomputable def rsqrtSeq (y x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => rsqrtStep y (rsqrtSeq y x₀ n)

/--
@isnad1 id=eq.0h2v.s3.c85a7187e60c from=translated src=- shape=cc48e823 vocab=5edcadd3
-/
@[simp] theorem rsqrtSeq_zero (y x₀ : ℝ) : rsqrtSeq y x₀ 0 = x₀ := rfl

/--
@isnad1 id=eq.0h3v.s4.f12988f12a53 from=translated src=- shape=3524b51e vocab=7e4a916a
-/
@[simp] theorem rsqrtSeq_succ (y x₀ : ℝ) (n : ℕ) :
    rsqrtSeq y x₀ (n + 1) = rsqrtStep y (rsqrtSeq y x₀ n) := rfl

/-- (4.9) is (4.4) with `m = 2`.
@isnad1 id=eq.0h2v.s4.ee465ce06537 from=translated src=- shape=722e53ee vocab=1f0f3e8b
-/
theorem rsqrtStep_eq_inverseRootStep (y x : ℝ) : rsqrtStep y x = inverseRootStep 2 y x := by
  simp [rsqrtStep, inverseRootStep]

/-- `u = 1 − x² y`, which vanishes iff `x² = 1/y`.-/
def rsqrtError (y x : ℝ) : ℝ := 1 - x ^ 2 * y

/-- The exact error recurrence of (4.9): `u' = u² (3 + u) / 4`.
@isnad1 id=eq.0h2v.s6.a5b212acfbae from=translated src=- shape=a33eaa47 vocab=5913cf10
-/
theorem rsqrtError_rsqrtStep (y x : ℝ) :
    rsqrtError y (rsqrtStep y x) = rsqrtError y x ^ 2 * (3 + rsqrtError y x) / 4 := by
  unfold rsqrtError rsqrtStep
  ring

/-- `|u| ≤ 1` gives `|u'| ≤ u²`.
@isnad1 id=le.1h2v.s5.3ac37e4916ee from=translated src=- shape=d56a22e1 vocab=31e7f0c3
-/
theorem abs_rsqrtError_rsqrtStep_le {y x : ℝ} (h : |rsqrtError y x| ≤ 1) :
    |rsqrtError y (rsqrtStep y x)| ≤ rsqrtError y x ^ 2 := by
  rw [rsqrtError_rsqrtStep, abs_div, abs_mul, abs_pow, sq_abs, abs_of_pos (by norm_num : (0:ℝ) < 4),
    div_le_iff₀ (by norm_num)]
  have h3 : |3 + rsqrtError y x| ≤ 4 := by
    calc |3 + rsqrtError y x| ≤ |3| + |rsqrtError y x| := abs_add_le _ _
      _ ≤ 4 := by rw [abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
  exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)

/-- Bit doubling for (4.9): `|u_0| ≤ 1` gives `|u_j| ≤ |u_0|^(2^j)`.
@isnad1 id=le.1h3v.s6.632d4784a70f from=translated src=- shape=9da59642 vocab=e76650d4
-/
theorem abs_rsqrtError_rsqrtSeq_le {y x₀ : ℝ} (h : |rsqrtError y x₀| ≤ 1) (j : ℕ) :
    |rsqrtError y (rsqrtSeq y x₀ j)| ≤ |rsqrtError y x₀| ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hle : |rsqrtError y (rsqrtSeq y x₀ j)| ≤ 1 :=
      ih.trans (pow_le_one₀ (abs_nonneg _) h)
    rw [rsqrtSeq_succ, pow_succ, pow_mul]
    calc |rsqrtError y (rsqrtStep y (rsqrtSeq y x₀ j))|
        ≤ rsqrtError y (rsqrtSeq y x₀ j) ^ 2 := abs_rsqrtError_rsqrtStep_le hle
      _ = |rsqrtError y (rsqrtSeq y x₀ j)| ^ 2 := (sq_abs _).symm
      _ ≤ (|rsqrtError y x₀| ^ (2 ^ j)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ih 2

/-- The step (4.9) in terms of the relative error: if `ζ² y = 1` then `x = ζ (1 + ε)` is sent to
`ζ (1 + ε')` with `ε' = −(3 ε² + ε³) / 2`.
@isnad1 id=eq.1h3v.s7.c31ec4578513 from=translated src=- shape=ccee3d1c vocab=7270136c
-/
theorem rsqrtStep_rel {y ζ : ℝ} (hζ : ζ ^ 2 * y = 1) (ε : ℝ) :
    rsqrtStep y (ζ * (1 + ε)) = ζ * (1 + -(3 * ε ^ 2 + ε ^ 3) / 2) := by
  rw [rsqrtStep_eq_inverseRootStep, inverseRootStep_rel 2 hζ]
  push_cast
  ring

/-- A positive iterate with `|u| < 1` stays positive.
@isnad1 id=lt.2h2v.s5.209e46aad8e6 from=translated src=- shape=a612b9a4 vocab=5b8c8062
-/
theorem rsqrtStep_pos {y x : ℝ} (hx : 0 < x) (hu : |rsqrtError y x| < 1) : 0 < rsqrtStep y x := by
  have : rsqrtStep y x = x * (1 + rsqrtError y x / 2) := by unfold rsqrtStep rsqrtError; ring
  rw [this]
  rw [abs_lt] at hu
  have : 0 < 1 + rsqrtError y x / 2 := by linarith [hu.1]
  positivity

/-- `|u_0| < 1` iff `x_0² y ∈ (0, 2)`.
@isnad1 id=iff.0h2v.s6.514173790995 from=translated src=- shape=3463789c vocab=56fa0dec
-/
theorem abs_rsqrtError_lt_one_iff (y x₀ : ℝ) :
    |rsqrtError y x₀| < 1 ↔ x₀ ^ 2 * y ∈ Ioo 0 2 := by
  unfold rsqrtError
  rw [abs_lt, mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- From `x_0 > 0` with `|u_0| < 1` all iterates of (4.9) are positive.
@isnad1 id=lt.2h3v.s5.dde108955a07 from=translated src=- shape=47bdfdd0 vocab=21b31550
-/
theorem rsqrtSeq_pos {y x₀ : ℝ} (hx : 0 < x₀) (hu : |rsqrtError y x₀| < 1) (j : ℕ) :
    0 < rsqrtSeq y x₀ j := by
  induction j with
  | zero => exact hx
  | succ j ih =>
    rw [rsqrtSeq_succ]
    apply rsqrtStep_pos ih
    calc |rsqrtError y (rsqrtSeq y x₀ j)| ≤ |rsqrtError y x₀| ^ (2 ^ j) :=
          abs_rsqrtError_rsqrtSeq_le hu.le j
      _ ≤ |rsqrtError y x₀| ^ 1 :=
          pow_le_pow_of_le_one (abs_nonneg _) hu.le Nat.one_le_two_pow
      _ < 1 := by rw [pow_one]; exact hu

/-- `(√y)⁻¹ = y^(−1/2)` for `y > 0`, connecting with the inverse-root results.
@isnad1 id=eq.1h1v.s5.39ea8a1578e4 from=translated src=- shape=221fc2b5 vocab=cb115ff5
-/
theorem inv_sqrt_eq_rpow {y : ℝ} (hy : 0 < y) :
    (Real.sqrt y)⁻¹ = y ^ (-(1 / ((2 : ℕ) : ℝ))) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hy.le]
  push_cast
  rfl

/-- Convergence of (4.9): from `x_0 > 0` with `x_0² y < 2` (and `y > 0`) the iterates converge to
`(√y)⁻¹ = y^(−1/2)`, with `|u_j| ≤ |u_0|^(2^j)`.
@isnad1 id=tendsto.3h2v.s6.d3cf2cf68f94 from=translated src=- shape=b552bff2 vocab=017eab11
-/
theorem tendsto_rsqrtSeq {y x₀ : ℝ} (hy : 0 < y) (hx : 0 < x₀) (h2 : x₀ ^ 2 * y < 2) :
    Tendsto (rsqrtSeq y x₀) atTop (𝓝 (Real.sqrt y)⁻¹) := by
  have hu : |rsqrtError y x₀| < 1 := by
    rw [abs_rsqrtError_lt_one_iff]; exact ⟨by positivity, h2⟩
  -- `u_j → 0`
  have hu0 : Tendsto (fun j => rsqrtError y (rsqrtSeq y x₀ j)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun j : ℕ => |rsqrtError y x₀| ^ (2 ^ j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_abs])).comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    exact squeeze_zero_norm (fun j => by
      rw [Real.norm_eq_abs]; exact abs_rsqrtError_rsqrtSeq_le hu.le j) hlim
  -- `x_j = √((1 − u_j) / y)` since `x_j > 0`
  have hx' : ∀ j, rsqrtSeq y x₀ j = Real.sqrt ((1 - rsqrtError y (rsqrtSeq y x₀ j)) / y) := by
    intro j
    have hpos := rsqrtSeq_pos hx hu j
    have : (1 - rsqrtError y (rsqrtSeq y x₀ j)) / y = rsqrtSeq y x₀ j ^ 2 := by
      unfold rsqrtError; field_simp; ring
    rw [this, Real.sqrt_sq hpos.le]
  have hlim : Tendsto (fun j => Real.sqrt ((1 - rsqrtError y (rsqrtSeq y x₀ j)) / y)) atTop
      (𝓝 (Real.sqrt ((1 - 0) / y))) :=
    ((tendsto_const_nhds.sub hu0).div_const y).sqrt
  rw [sub_zero, one_div, Real.sqrt_inv] at hlim
  exact hlim.congr (fun j => (hx' j).symm)

/-- The square root by one multiplication: `√y = y · (√y)⁻¹`.
@isnad1 id=eq.1h1v.s4.d6ed7b5c47ad from=translated src=- shape=21f66bd4 vocab=e51f811f
-/
theorem sqrt_eq_mul_inv_sqrt {y : ℝ} (hy : 0 < y) : Real.sqrt y = y * (Real.sqrt y)⁻¹ := by
  have h : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  field_simp
  exact Real.sq_sqrt hy.le

/-- The multiplication preserves the relative error exactly: `y · (√y)⁻¹ (1 + ε) = √y (1 + ε)`.
@isnad1 id=eq.1h2v.s6.832f836f77cb from=translated src=- shape=8caa1541 vocab=26ec3772
-/
theorem mul_inv_sqrt_rel {y : ℝ} (hy : 0 < y) (ε : ℝ) :
    y * ((Real.sqrt y)⁻¹ * (1 + ε)) = Real.sqrt y * (1 + ε) := by
  rw [← mul_assoc, ← sqrt_eq_mul_inv_sqrt hy]

/-! ### Heron's iteration (4.10) -/

/-- Heron's step (4.10), `(x + y / x) / 2`.-/
noncomputable def heronStep (y x : ℝ) : ℝ := (x + y / x) / 2

/-- The iterates of (4.10) from `x₀`.-/
noncomputable def heronSeq (y x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => heronStep y (heronSeq y x₀ n)

/--
@isnad1 id=eq.0h2v.s3.df0eac555e9d from=translated src=- shape=cc48e823 vocab=281df98c
-/
@[simp] theorem heronSeq_zero (y x₀ : ℝ) : heronSeq y x₀ 0 = x₀ := rfl

/--
@isnad1 id=eq.0h3v.s4.652e52bd2b7a from=translated src=- shape=3524b51e vocab=d853d271
-/
@[simp] theorem heronSeq_succ (y x₀ : ℝ) (n : ℕ) :
    heronSeq y x₀ (n + 1) = heronStep y (heronSeq y x₀ n) := rfl

/-- (4.10) is Newton's step for `f(x) = x² − y` (with `f'(x) = 2x`) at every `x ≠ 0`.
@isnad1 id=eq.1h2v.s6.1104fc379af6 from=translated src=- shape=033531b1 vocab=44a6796e
-/
theorem newtonStep_sq_sub (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    newtonStep (fun x => x ^ 2 - y) (fun x => 2 * x) x = heronStep y x := by
  unfold newtonStep heronStep
  field_simp
  ring

/-- The exact error of Heron's step: `x' − √y = (x − √y)² / (2x)`.
@isnad1 id=eq.2h2v.s6.4a7f952df311 from=translated src=- shape=749f682b vocab=dd830498
-/
theorem heronStep_sub_sqrt {y x : ℝ} (hy : 0 ≤ y) (hx : x ≠ 0) :
    heronStep y x - Real.sqrt y = (x - Real.sqrt y) ^ 2 / (2 * x) := by
  unfold heronStep
  have h := Real.mul_self_sqrt hy
  field_simp
  linear_combination -h

/-- From a positive `x`, Heron's step lands at or above `√y`.
@isnad1 id=le.2h2v.s5.586746fcb455 from=translated src=- shape=c157fb76 vocab=8953781d
-/
theorem sqrt_le_heronStep {y x : ℝ} (hy : 0 ≤ y) (hx : 0 < x) : Real.sqrt y ≤ heronStep y x := by
  have h := heronStep_sub_sqrt hy hx.ne'
  have : 0 ≤ (x - Real.sqrt y) ^ 2 / (2 * x) := by positivity
  linarith

/-- Above `√y`, Heron's step does not increase.
@isnad1 id=le.3h2v.s5.592fd1da248d from=translated src=- shape=fb2fc4bb vocab=8953781d
-/
theorem heronStep_le {y x : ℝ} (hy : 0 ≤ y) (hx : Real.sqrt y ≤ x) (hx0 : 0 < x) :
    heronStep y x ≤ x := by
  unfold heronStep
  have hyx : y ≤ x ^ 2 := by
    calc y = Real.sqrt y ^ 2 := (Real.sq_sqrt hy).symm
      _ ≤ x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have : y / x ≤ x := by rw [div_le_iff₀ hx0]; nlinarith
  linarith

/-- Quadratic convergence of Heron's iteration above the root: for `√y ≤ x`,
`x' − √y ≤ (x − √y)² / (2√y)` and `x' − √y ≤ (x − √y) / 2`.
@isnad1 id=and.2h2v.s7.f5e67ef08582 from=translated src=- shape=0b697cc8 vocab=77d67015
-/
theorem heronStep_sub_sqrt_le {y x : ℝ} (hy : 0 < y) (hx : Real.sqrt y ≤ x) :
    heronStep y x - Real.sqrt y ≤ (x - Real.sqrt y) ^ 2 / (2 * Real.sqrt y) ∧
      heronStep y x - Real.sqrt y ≤ (x - Real.sqrt y) / 2 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hx0 : 0 < x := lt_of_lt_of_le hs hx
  rw [heronStep_sub_sqrt hy.le hx0.ne']
  constructor
  · exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sub_nonneg.mpr hx]

/-- Heron's iteration converges to `√y` from every `x_0 > 0`.
@isnad1 id=tendsto.2h2v.s5.e6be891c81d4 from=translated src=- shape=6ce7f0b6 vocab=3feee547
-/
theorem tendsto_heronSeq {y x₀ : ℝ} (hy : 0 < y) (hx : 0 < x₀) :
    Tendsto (heronSeq y x₀) atTop (𝓝 (Real.sqrt y)) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  -- after the first step every iterate is at or above `√y`, hence positive
  have hge : ∀ n, Real.sqrt y ≤ heronSeq y x₀ (n + 1) ∧ 0 < heronSeq y x₀ n := by
    intro n
    induction n with
    | zero => exact ⟨sqrt_le_heronStep hy.le hx, hx⟩
    | succ n ih =>
      have hpos : 0 < heronSeq y x₀ (n + 1) := lt_of_lt_of_le hs ih.1
      exact ⟨sqrt_le_heronStep hy.le hpos, hpos⟩
  -- the error halves at every step from the first iterate on
  have hhalf : ∀ n, heronSeq y x₀ (n + 1) - Real.sqrt y
      ≤ (heronSeq y x₀ 1 - Real.sqrt y) / 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc heronSeq y x₀ (n + 1 + 1) - Real.sqrt y
          ≤ (heronSeq y x₀ (n + 1) - Real.sqrt y) / 2 :=
            (heronStep_sub_sqrt_le hy (hge n).1).2
        _ ≤ (heronSeq y x₀ 1 - Real.sqrt y) / 2 ^ n / 2 := by gcongr
        _ = (heronSeq y x₀ 1 - Real.sqrt y) / 2 ^ (n + 1) := by rw [pow_succ]; ring
  -- squeeze the shifted sequence, then drop the shift
  have hshift : Tendsto (fun n => heronSeq y x₀ (n + 1)) atTop (𝓝 (Real.sqrt y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => (heronSeq y x₀ 1 - Real.sqrt y) * (1 / 2 : ℝ) ^ n) atTop
        (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (heronSeq y x₀ 1 - Real.sqrt y)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hge n).1), one_div, inv_pow,
      ← div_eq_mul_inv]
    exact hhalf n
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end BZ

end Azurite
