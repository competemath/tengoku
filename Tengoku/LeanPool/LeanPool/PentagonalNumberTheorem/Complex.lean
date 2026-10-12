/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Tengoku.LeanPool.LeanPool.PentagonalNumberTheorem.Generic
public import Tengoku

/-!

# Pentagonal number theorem for real/complex numbers

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
for real/complex numbers.

-/

@[expose] public section

open Filter
variable {K : Type*} [RCLike K]

namespace Pentagonal

theorem multipliable_pentagonalLhs_complex' (k : ℕ) {x : K} (hx : ‖x‖ < 1) :
    Multipliable (fun n ↦ 1 - x ^ (n + k + 1)) := by
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_summable
  simp_rw [norm_neg, norm_pow, pow_add]
  apply ((summable_geometric_of_lt_one (by simp) hx).mul_right _).mul_right

end Pentagonal

open Pentagonal

theorem multipliable_pentagonalLhs_complex {x : K} (hx : ‖x‖ < 1) :
    Multipliable (fun n ↦ 1 - x ^ (n + 1)) := by
  simpa using multipliable_pentagonalLhs_complex' 0 hx

theorem summable_pentagonalRhs_complex {x : K} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℕ) ↦
    ((-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)))) := by
  simp_rw [mul_sub]
  refine Summable.sub ?_ ?_
  <;> rw [← summable_norm_iff]
  <;> simp_rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  <;> refine Summable.of_nonneg_of_le (by simp) ?_ (summable_geometric_of_lt_one (by simp) hx)
  <;> refine fun k ↦ pow_le_pow_of_le_one (by simp) (hx.le) ?_
  · obtain rfl | h0 := Nat.eq_zero_or_pos k
    · simp
    rw [Nat.le_div_iff_mul_le (by simp)]
    exact Nat.mul_le_mul_left _ (by linarith)
  · rw [Nat.le_div_iff_mul_le (by simp)]
    exact Nat.mul_le_mul (by simp) (by simp)

theorem summable_pentagonalRhs_intNeg_complex {x : K} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℤ) ↦ (-1) ^ k * x ^ (k * (3 * k + 1) / 2)) := by
  apply Summable.of_add_one_of_neg_add_one
  all_goals
  rw [← summable_norm_iff]
  simp_rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  refine Summable.of_nonneg_of_le (fun k ↦ by apply zpow_nonneg (by simp)) (fun k ↦ ?_)
    (summable_geometric_of_lt_one (by simp) hx)
  rw [← zpow_natCast]
  obtain h0 | h0 := eq_or_lt_of_le (norm_nonneg x)
  · simp_rw [← h0]
    obtain rfl | hk0 := eq_or_ne k 0
    · norm_num
    rw [zero_zpow _ ?_, zero_zpow _ (by simpa using hk0)]
    grind
  apply zpow_le_zpow_right_of_le_one₀ h0 hx.le
  grind

theorem summable_pentagonalRhs_intPos_complex {x : K} (hx : ‖x‖ < 1) :
    Summable (fun (k : ℤ) ↦ (-1) ^ k * x ^ (k * (3 * k - 1) / 2)) := by
  rw [← neg_injective.summable_iff (by intro x hx; contrapose! hx; use -x; simp)]
  convert summable_pentagonalRhs_intNeg_complex hx
  rw [Function.comp_apply]
  congrm ?_ * x ^ ($(by ring_nf) / 2)
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
