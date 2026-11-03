/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeBounds
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvMul
import Tengoku.Seed.Algebra.Polynomial.Coeff
import Tengoku.Seed.Algebra.Polynomial.Degree.Support
import Tengoku.Seed.Algebra.Polynomial.Eval.Degree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §8.1 Algorithm 8.8: Special evaluation of a univariate polynomial

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ ℤ[X]` and `b/c ∈ ℚ` with `b, c ∈ ℤ`,
compute `cᵖ · P(b/c)` without leaving `ℤ`. The algorithm is a variant
of Horner's method (Algorithm 8.7) that keeps track of a running
power `d = cⁱ`:

  - Initialize `HorSpecial₀(P, b) := aₚ`,  `d := 1`.
  - For `i` from `1` to `p`:
    - `d := c · d`
    - `HorSpecialᵢ(P, b) := b · HorSpecialᵢ₋₁(P, b) + d · aₚ₋ᵢ`
  - Output `HorSpecialₚ(P, b) = cᵖ · P(b/c)`.

We define `Polynomial.horSpecial` (outside `Azurite.BPR`, extending
Mathlib's `Polynomial` namespace), prove the recurrence, closed form,
and the main evaluation identity over a field. The bitsize bound on
`horSpecial` over `ℤ` is recorded as `Polynomial.bitsize_horSpecial_le`.
-/

section HorSpecial

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Algorithm 8.8 (Special Horner evaluation).** Given `P ∈ R[X]`
    with `p = natDegree P`, and elements `b, c ∈ R`, computes
    `cᵖ · P(b/c)` without division:
    - `horSpecial P b c 0 = aₚ`
    - `horSpecial P b c (i+1) = b · horSpecial P b c i + c^{i+1} · aₚ₋ᵢ₋₁`-/
noncomputable def Polynomial.horSpecial (P : R[X]) (b c : R) : ℕ → R
  | 0 => P.coeff P.natDegree
  | i + 1 => b * P.horSpecial b c i + c ^ (i + 1) * P.coeff (P.natDegree - (i + 1))

/-- The base case: `horSpecial P b c 0 = leadingCoeff P`.-/
theorem Polynomial.horSpecial_zero (P : R[X]) (b c : R) :
    P.horSpecial b c 0 = P.leadingCoeff := by
  unfold Polynomial.horSpecial; rw [leadingCoeff]

/-- **Closed-form characterization.**
    `horSpecial P b c i = ∑ j ∈ range (i+1), aₚ₋ⱼ · b^{i−j} · c^j`.-/
theorem Polynomial.horSpecial_eq_sum (P : R[X]) (b c : R) (i : ℕ) :
    P.horSpecial b c i = ∑ j ∈ range (i + 1),
      P.coeff (P.natDegree - j) * b ^ (i - j) * c ^ j := by
  induction i with
  | zero => simp [Polynomial.horSpecial]
  | succ n ih =>
    rw [Polynomial.horSpecial, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one]
    congr 1
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro j hj; rw [Finset.mem_range] at hj
      rw [show n + 1 - j = (n - j) + 1 from by omega, pow_succ]; ring
    · ring

/-- **Reindexed closed form at `i = natDegree P`.**
    `horSpecial P b c p = ∑ k ∈ range (p+1), aₖ · bᵏ · c^{p−k}`.-/
theorem Polynomial.horSpecial_natDegree_eq_sum (P : R[X]) (b c : R) :
    P.horSpecial b c P.natDegree = ∑ k ∈ range (P.natDegree + 1),
      P.coeff k * b ^ k * c ^ (P.natDegree - k) := by
  rw [horSpecial_eq_sum, ← Finset.sum_flip]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finset.mem_range] at hj
  rw [show P.natDegree - (P.natDegree - j) = j from by omega]

/-- **BPR Algorithm 8.8 (main result, over a field).**
    `horSpecial P b c p = cᵖ · P.eval(b · c⁻¹)` when `c ≠ 0`.-/
theorem Polynomial.horSpecial_natDegree_eq_eval {K : Type*} [Field K]
    (P : K[X]) (b c : K) (hc : c ≠ 0) :
    P.horSpecial b c P.natDegree = c ^ P.natDegree * P.eval (b * c⁻¹) := by
  rw [horSpecial_natDegree_eq_sum, eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.mem_range] at hk
  rw [mul_pow, inv_pow]
  calc P.coeff k * b ^ k * c ^ (P.natDegree - k)
      = P.coeff k * (b ^ k * c ^ (P.natDegree - k)) := by ring
    _ = P.coeff k * (c ^ P.natDegree * (b ^ k * (c ^ k)⁻¹)) := by
        congr 1; rw [pow_sub₀ c hc (by omega : k ≤ P.natDegree)]; ring
    _ = c ^ P.natDegree * (P.coeff k * (b ^ k * (c ^ k)⁻¹)) := by ring

end HorSpecial

/-! ### Bitsize bound on HorSpecial -/

section HorSpecialBitsize

open Polynomial Finset

-- Each summand `a_{p-j} · b^{i-j} · c^j` has bitsize ≤ τ + i · τ'.
-- This is the product of one coefficient (bitsize ≤ τ) with i factors
-- (b or c, each of bitsize ≤ τ').

end HorSpecialBitsize
