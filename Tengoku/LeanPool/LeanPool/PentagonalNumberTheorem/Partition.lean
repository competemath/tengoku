/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.PentagonalNumberTheorem.PowerSeries

/-!
# LeanPool.PentagonalNumberTheorem.Partition

Imported Lean Pool material for `LeanPool.PentagonalNumberTheorem.Partition`.
-/

@[expose] public section

theorem two_pentagonal (k : ℤ) : 2 * (k * (3 * k - 1) / 2) = k * (3 * k - 1) := by
  refine Int.two_mul_ediv_two_of_even ?_
  obtain h | h := Int.even_or_odd k
  · exact Even.mul_right h (3 * k - 1)
  · refine Even.mul_left ?_ _
    refine Int.even_sub_one.mpr ?_
    refine Int.not_even_iff_odd.mpr ?_
    refine Odd.mul ?_ h
    decide

theorem pentagonal_nonneg (k : ℤ) : 0 ≤ k * (3 * k - 1) / 2 := by
  suffices 0 ≤ 2 * (k * (3 * k - 1) / 2) by simpa
  rw [two_pentagonal]
  obtain h | h := lt_or_ge 0 k
  · exact mul_nonneg h.le (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)

theorem two_pentagonal_inj {x y : ℤ} (h : x * (3 * x - 1) = y * (3 * y - 1)) : x = y := by
  simp_rw [mul_sub_one] at h
  rw [sub_eq_sub_iff_sub_eq_sub, mul_left_comm x, mul_left_comm y, ← mul_sub,
    mul_self_sub_mul_self, ← mul_assoc, ← sub_eq_zero, ← sub_one_mul, mul_eq_zero] at h
  obtain h | h := h
  · obtain h' := Int.eq_of_mul_eq_one <| eq_of_sub_eq_zero h
    simp [← h'] at h
  · exact eq_of_sub_eq_zero h

namespace Nat.Partition

variable (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R]
open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

/-- The finite set of integers `k` for which the pentagonal number `k * (3 * k - 1) / 2` is
at most `n`. Used to express the pentagonal recurrence for the partition function. -/
noncomputable def kSet (n : ℤ) : Finset ℤ :=
  Finset.Icc (-(((1 + 24 * n).sqrt - 1) / 6)) (((1 + 24 * n).sqrt + 1) / 6)

end Nat.Partition
