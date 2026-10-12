/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Defs

/-!
# Signs of the edge and vertex entropy costs

The logarithmic inequalities used here reduce to small integer comparisons.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

/-- The quarter-biased entropy expanded into logarithms of integers.
@isnad1 id=eq.0h0v.s6.11dd4590e4ef from=translated src=- shape=c01dd95f vocab=6b19beec
-/
theorem binEntropy_quarter :
    Real.binEntropy (1 / 4) = 2 * Real.log 2 - 3 / 4 * Real.log 3 := by
  have four : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [Real.negMulLog_def, Real.log_div]
  rw [four]
  ring

/-- The per-edge cost is nonnegative.
@isnad1 id=le.0h0v.s3.db17f4309ee4 from=translated src=- shape=ff3a10fc vocab=cdac6da7
-/
theorem edgeCost_nonneg : 0 ≤ edgeCost := by
  have bound := Real.binEntropy_le_log_two (p := (1 / 4 : ℝ))
  have positive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold edgeCost
  linarith

/-- The per-vertex cost is nonnegative because `3 ^ 3 ≤ 2 ^ 5`.
@isnad1 id=le.0h0v.s3.94a2ed3b6e6d from=translated src=- shape=ff3a10fc vocab=d4b95582
-/
theorem vertexCost_nonneg : 0 ≤ vertexCost := by
  have logs : 3 * Real.log 3 ≤ 5 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 3)
      (by norm_num : (3 : ℝ) ^ 3 ≤ 2 ^ 5)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  rw [vertexCost, binEntropy_quarter]
  linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
