/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Tengoku

/-!
# LeanPool.RlTheoryInLean.StochasticApproximation.DiscreteGronwall
-/

@[expose] public section

open Real Finset

namespace StochasticApproximation

variable {u b c : ℕ → ℝ}

theorem discrete_gronwall_aux
  {n₀ : ℕ}
  (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (hc : ∀ n ≥ n₀, c n ≥ 0) :
  ∀ n, n₀ ≤ n → u n ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
  ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) := by
  intro n hn
  refine Nat.le_induction ?base ?succ n hn
  case base => simp
  case succ =>
    intro k hk ih
    have hck : (0 : ℝ) ≤ 1 + c k := by have := hc k (by linarith); linarith
    grw [hu k (by linarith), ih]
    rw [mul_add, mul_comm, mul_assoc, prod_Ico_mul_eq_prod_Ico_add_one hk,
      add_assoc]
    simp only [add_le_add_iff_left]
    rw [mul_sum, ← sum_Ico_add_eq_sum_Ico_add_one hk]
    simp only [Ico_self, prod_empty, mul_one, add_le_add_iff_right]
    apply sum_le_sum
    intro i hi
    simp only [mem_Ico] at hi
    rw [mul_comm, mul_assoc,
      prod_Ico_mul_eq_prod_Ico_add_one (by omega : i + 1 ≤ k)]

end StochasticApproximation
