/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.InverseRoot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.2.2: Newton's method for reciprocals

The case `m = 1` of (4.4): the iteration

  `x_{j+1} = x_j + x_j (1 − x_j y)`                                                      (4.5)

converges to `1/y`.  With `u_j = 1 − x_j y`, multiplying (4.5) by `y` gives
`1 − u_{j+1} = (1 − u_j)(1 + u_j)`, i.e. `u_{j+1} = u_j²` (4.6) and `u_j = u_0^(2^j)` (4.7), so the
iteration converges iff `|u_0| < 1`, i.e. iff `x_0 y ∈ (0, 2)`; the number of correct bits
doubles at every step, so the number of iterations can be predicted in advance.

The *computational issues* paragraph: the form `x_j (2 − x_j y)` (4.8) is mathematically the same
as (4.5) but not computationally.  In (4.5) the correction term `x_j (1 − x_j y)` is
`O(2^(−n/2))` when `x_j` has `n/2` correct bits, so computing it to relative precision `2^(−n/2)`
still gives `x_{j+1}` to `n` bits; in (4.8) the factor `2 − x_j y = 1 + O(2^(−n/2))` has to be
multiplied at full precision `n`.  We record this as exact identities for a perturbed product:
`1 − x̃ y = u² − θ u (x y)` for (4.5) against `1 − x̃ y = u² − θ (1 − u²)` for (4.8), where `θ` is
the relative error of the product.  The general rule — separate the terms of different order,
do not factor common expressions — is a design rule, not a theorem.

* `reciprocalStep`, `reciprocalSeq` — (4.5); `reciprocalStep_eq_inverseRootStep`.
* `recipError` — `u = 1 − x y`; `recipError_reciprocalStep` (4.6), `recipError_reciprocalSeq`
  (4.7), `reciprocalSeq_sub_inv` (`x_j − 1/y = −u_0^(2^j) / y`).
* `abs_recipError_lt_one_iff` (`|u_0| < 1 ↔ x_0 y ∈ (0, 2)`), `tendsto_reciprocalSeq_iff`
  (convergence to `1/y` iff `|u_0| < 1`).
* `abs_recipError_reciprocalSeq_le` (`|u_0| ≤ 2^(−k)` gives `|u_j| ≤ 2^(−k 2^j)`),
  `abs_recipError_reciprocalSeq_le_of_le` (`n ≤ k 2^j` iterations suffice for `n` bits),
  `recipError_one_le_half` (for `y ∈ [1/2, 1)` the start `x_0 = 1` has `u_0 ∈ (0, 1/2]`).
* `reciprocalStep'` (4.8), `reciprocalStep'_eq`, `recipError_reciprocalStep_perturbed`,
  `recipError_reciprocalStep'_perturbed`, `abs_recipError_reciprocalStep_perturbed_le`.
-/

namespace Azurite

namespace BZ

open Set Filter Topology

/-- The reciprocal step (4.5), `x + x (1 − x y)`.-/
def reciprocalStep (y x : ℝ) : ℝ := x + x * (1 - x * y)

/-- The iterates of (4.5) from `x₀`.-/
def reciprocalSeq (y x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => reciprocalStep y (reciprocalSeq y x₀ n)

/--
@isnad1 id=eq.0h2v.s3.f73cb963b353 from=translated src=- shape=cc48e823 vocab=704ebc3a
-/
@[simp] theorem reciprocalSeq_zero (y x₀ : ℝ) : reciprocalSeq y x₀ 0 = x₀ := rfl

/--
@isnad1 id=eq.0h3v.s4.636526e319c4 from=translated src=- shape=3524b51e vocab=4fc6ebad
-/
@[simp] theorem reciprocalSeq_succ (y x₀ : ℝ) (n : ℕ) :
    reciprocalSeq y x₀ (n + 1) = reciprocalStep y (reciprocalSeq y x₀ n) := rfl

/-- (4.5) is (4.4) with `m = 1`.
@isnad1 id=eq.0h2v.s4.ff4c8fde4aa3 from=translated src=- shape=722e53ee vocab=ad57a656
-/
theorem reciprocalStep_eq_inverseRootStep (y x : ℝ) :
    reciprocalStep y x = inverseRootStep 1 y x := by
  simp [reciprocalStep, inverseRootStep]

/-- `u = 1 − x y`, which vanishes iff `x = 1/y`.-/
def recipError (y x : ℝ) : ℝ := 1 - x * y

/--
@isnad1 id=iff.1h2v.s5.b499f05e02a9 from=translated src=- shape=7d3bd6f3 vocab=cf3e0307
-/
theorem recipError_eq_zero_iff {y : ℝ} (hy : y ≠ 0) (x : ℝ) : recipError y x = 0 ↔ x = y⁻¹ := by
  unfold recipError
  rw [sub_eq_zero, eq_comm]
  exact ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, inv_mul_cancel₀ hy]⟩

/-- `x = (1 − u) / y`.-/
theorem eq_of_recipError {y : ℝ} (hy : y ≠ 0) (x : ℝ) : x = (1 - recipError y x) / y := by
  unfold recipError
  field_simp
  ring

/-- (4.6): `u_{j+1} = u_j²`.
@isnad1 id=eq.0h2v.s4.b6de2e03ddff from=translated src=- shape=9862f300 vocab=a772b8c9
-/
theorem recipError_reciprocalStep (y x : ℝ) :
    recipError y (reciprocalStep y x) = recipError y x ^ 2 := by
  unfold recipError reciprocalStep
  ring

/-- (4.7): `u_j = u_0^(2^j)`.
@isnad1 id=eq.0h3v.s5.a11cc4d8999e from=translated src=- shape=835de1ea vocab=97e07f01
-/
theorem recipError_reciprocalSeq (y x₀ : ℝ) (j : ℕ) :
    recipError y (reciprocalSeq y x₀ j) = recipError y x₀ ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [reciprocalSeq_succ, recipError_reciprocalStep, ih, ← pow_mul, pow_succ]

/-- The error of the `j`-th iterate: `x_j − 1/y = −u_0^(2^j) / y`.
@isnad1 id=eq.1h3v.s6.cf5fd7ac8ef1 from=translated src=- shape=6a7f8168 vocab=5e17f951
-/
theorem reciprocalSeq_sub_inv {y : ℝ} (hy : y ≠ 0) (x₀ : ℝ) (j : ℕ) :
    reciprocalSeq y x₀ j - y⁻¹ = -(recipError y x₀ ^ (2 ^ j)) / y := by
  have h := recipError_reciprocalSeq y x₀ j
  rw [← h]
  unfold recipError
  field_simp
  ring

/-- `|u_0| < 1` iff `x_0 y ∈ (0, 2)`.
@isnad1 id=iff.0h2v.s5.0c569c6caea2 from=translated src=- shape=ed0a5cfa vocab=6daba6e7
-/
theorem abs_recipError_lt_one_iff (y x₀ : ℝ) : |recipError y x₀| < 1 ↔ x₀ * y ∈ Ioo 0 2 := by
  unfold recipError
  rw [abs_lt, mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- `u_j → 0` iff `x_j → 1/y`.
@isnad1 id=iff.1h2v.s5.9132eaac92ac from=translated src=- shape=bb7314a7 vocab=ba1ed087
-/
theorem tendsto_recipError_iff {y : ℝ} (hy : y ≠ 0) (x : ℕ → ℝ) :
    Tendsto (fun j => recipError y (x j)) atTop (𝓝 0) ↔ Tendsto x atTop (𝓝 y⁻¹) := by
  constructor
  · intro h
    have h' : Tendsto (fun j => (1 - recipError y (x j)) / y) atTop (𝓝 ((1 - 0) / y)) :=
      (tendsto_const_nhds.sub h).div_const y
    rw [sub_zero, one_div] at h'
    exact h'.congr (fun j => (eq_of_recipError hy (x j)).symm)
  · intro h
    have h' : Tendsto (fun j => 1 - x j * y) atTop (𝓝 (1 - y⁻¹ * y)) :=
      tendsto_const_nhds.sub (h.mul_const y)
    rwa [inv_mul_cancel₀ hy, sub_self] at h'

/-- The iteration (4.5) converges to `1/y` iff `|u_0| < 1` (iff `x_0 y ∈ (0, 2)`); the
convergence is doubly exponential, (4.7).
@isnad1 id=iff.1h2v.s5.c7ece5cefab3 from=translated src=- shape=036bb3c0 vocab=63e46b3f
-/
theorem tendsto_reciprocalSeq_iff {y : ℝ} (hy : y ≠ 0) (x₀ : ℝ) :
    Tendsto (reciprocalSeq y x₀) atTop (𝓝 y⁻¹) ↔ |recipError y x₀| < 1 := by
  rw [← tendsto_recipError_iff hy]
  simp only [recipError_reciprocalSeq]
  constructor
  · intro h
    by_contra hu
    push Not at hu
    have hge : ∀ j, 1 ≤ |recipError y x₀ ^ (2 ^ j)| := fun j => by
      rw [abs_pow]; exact one_le_pow₀ hu
    have hev := h.abs.eventually (gt_mem_nhds (by simp : |(0 : ℝ)| < 1))
    obtain ⟨j, hj⟩ := hev.exists
    have := hge j
    linarith
  · intro h
    exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Bit doubling: `|u_0| ≤ 2^(−k)` gives `|u_j| ≤ 2^(−k · 2^j)`.
@isnad1 id=le.1h4v.s6.2b45b16deda4 from=translated src=- shape=37e4c48d vocab=da078e0d
-/
theorem abs_recipError_reciprocalSeq_le {y x₀ : ℝ} {k : ℕ}
    (h : |recipError y x₀| ≤ (2 : ℝ) ^ (-(k : ℤ))) (j : ℕ) :
    |recipError y (reciprocalSeq y x₀ j)| ≤ (2 : ℝ) ^ (-((k * 2 ^ j : ℕ) : ℤ)) := by
  rw [recipError_reciprocalSeq, abs_pow]
  calc |recipError y x₀| ^ (2 ^ j) ≤ ((2 : ℝ) ^ (-(k : ℤ))) ^ (2 ^ j) :=
        pow_le_pow_left₀ (abs_nonneg _) h _
    _ = (2 : ℝ) ^ (-((k * 2 ^ j : ℕ) : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring

/-- Predicting the number of iterations: `n` correct bits of `u` after `j` iterations as soon as
`n ≤ k · 2^j`, from `k` correct bits at the start.
@isnad1 id=le.2h5v.s6.01dc537c8f7d from=translated src=- shape=5321a763 vocab=da078e0d
-/
theorem abs_recipError_reciprocalSeq_le_of_le {y x₀ : ℝ} {k n j : ℕ}
    (h : |recipError y x₀| ≤ (2 : ℝ) ^ (-(k : ℤ))) (hn : n ≤ k * 2 ^ j) :
    |recipError y (reciprocalSeq y x₀ j)| ≤ (2 : ℝ) ^ (-(n : ℤ)) :=
  (abs_recipError_reciprocalSeq_le h j).trans
    (zpow_le_zpow_right₀ (by norm_num) (by omega))

/-- For a normalized `y ∈ [1/2, 1)` the trivial start `x_0 = 1` already has `u_0 ∈ (0, 1/2]`, so
(4.5) converges from it with `|u_j| ≤ 2^(−2^j)`.
@isnad1 id=and.1h1v.s6.64f6cddb0d4b from=translated src=- shape=47a7eee2 vocab=375f6a6d
-/
theorem recipError_one_le_half {y : ℝ} (hy : y ∈ Ico (1 / 2 : ℝ) 1) :
    0 < recipError y 1 ∧ recipError y 1 ≤ 1 / 2 := by
  unfold recipError
  constructor <;> linarith [hy.1, hy.2]

/-! ### Computational issues: (4.5) against (4.8) -/

/-- The factored form (4.8), `x (2 − x y)`.-/
def reciprocalStep' (y x : ℝ) : ℝ := x * (2 - x * y)

/-- (4.5) and (4.8) are mathematically equivalent.
@isnad1 id=eq.0h2v.s3.424368434101 from=translated src=- shape=6c8684e5 vocab=10865beb
-/
theorem reciprocalStep'_eq (y x : ℝ) : reciprocalStep' y x = reciprocalStep y x := by
  unfold reciprocalStep' reciprocalStep
  ring

/-- (4.5) with the correction product `x (1 − x y)` computed with relative error `θ`:
`1 − x̃ y = u² − θ u (x y)`.  The perturbation enters multiplied by `u`, so a relative error
`θ = O(2^(−n/2))` on the product still leaves `u_{j+1} = O(2^(−n))`.
@isnad1 id=eq.0h3v.s6.10e0616eeae2 from=translated src=- shape=50d93bdc vocab=02d0a8a1
-/
theorem recipError_reciprocalStep_perturbed (y x θ : ℝ) :
    recipError y (x + x * (1 - x * y) * (1 + θ))
      = recipError y x ^ 2 - θ * recipError y x * (x * y) := by
  unfold recipError
  ring

/-- (4.8) with the product computed with relative error `θ`: `1 − x̃ y = u² − θ (1 − u²)`.  The
perturbation enters at full size, so `θ` must be `O(2^(−n))` for `u_{j+1} = O(2^(−n))`.
@isnad1 id=eq.0h3v.s7.db8004e73659 from=translated src=- shape=7520bec3 vocab=02d0a8a1
-/
theorem recipError_reciprocalStep'_perturbed (y x θ : ℝ) :
    recipError y (x * (2 - x * y) * (1 + θ))
      = recipError y x ^ 2 - θ * (1 - recipError y x ^ 2) := by
  unfold recipError
  ring

/-- The quantitative form for (4.5): `|u| ≤ ε`, `|θ| ≤ ε` and `ε ≤ 1` give `|u_{j+1}| ≤ 3 ε²`, so
the correction product may be computed with the same (half) precision as the current error.
@isnad1 id=le.3h4v.s7.f4f8b96fa089 from=translated src=- shape=532f8671 vocab=2e7bc57e
-/
theorem abs_recipError_reciprocalStep_perturbed_le {y x θ ε : ℝ} (hε : ε ≤ 1)
    (hu : |recipError y x| ≤ ε) (hθ : |θ| ≤ ε) :
    |recipError y (x + x * (1 - x * y) * (1 + θ))| ≤ 3 * ε ^ 2 := by
  rw [recipError_reciprocalStep_perturbed]
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hu
  have hxy : |x * y| ≤ 1 + ε := by
    have : x * y = 1 - recipError y x := by unfold recipError; ring
    rw [this]
    calc |1 - recipError y x| ≤ |1| + |recipError y x| := abs_sub _ _
      _ ≤ 1 + ε := by rw [abs_one]; linarith
  calc |recipError y x ^ 2 - θ * recipError y x * (x * y)|
      ≤ |recipError y x ^ 2| + |θ * recipError y x * (x * y)| := abs_sub _ _
    _ = |recipError y x| ^ 2 + |θ| * |recipError y x| * |x * y| := by
        rw [abs_pow, abs_mul, abs_mul]
    _ ≤ ε ^ 2 + ε * ε * (1 + ε) := by gcongr
    _ ≤ 3 * ε ^ 2 := by nlinarith

end BZ

end Azurite
