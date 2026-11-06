/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Valuation.Basic
import Tengoku.Seed.Algebra.Order.GroupWithZero.Canonical

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation obstructions for powers minus the identity

If `1 < v (x ^ n - x)` and `n > 1`, the leading term determines its value,
which must be an `n`-th power. This gives an obstruction using the logarithmic
exponent of an integer-valued valuation.
-/

namespace Valuation
universe u v

/-- Above valuation one, powers minus the identity can take only power values.-/
theorem pow_sub_ne_of_one_lt_of_not_pow
    {K : Type u} [Field K] {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation K Γ) (n : ℕ) (hn : 1 < n)
    (a : K) (ha : 1 < w a) (hpow : ∀ y : K, w y ^ n ≠ w a) :
    ∀ x : K, x ^ n - x ≠ a := by
  intro x hx
  by_cases hxt : w x ≤ 1
  · have hle : w (x ^ n - x) ≤ 1 :=
      w.map_sub_le (by rw [map_pow]; exact pow_le_one₀ zero_le hxt) hxt
    rw [hx] at hle
    exact (not_le_of_gt ha) hle
  · have hx1 : 1 < w x := lt_of_not_ge hxt
    have hlt : w x < w (x ^ n) := by
      rw [map_pow]
      simpa only [pow_one] using (pow_lt_pow_right₀ hx1 hn)
    have heq := w.map_sub_eq_of_lt_left hlt
    rw [map_pow, hx] at heq
    exact hpow x heq.symm

end Valuation
