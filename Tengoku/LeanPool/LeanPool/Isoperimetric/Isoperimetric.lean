/-
Copyright (c) 2026 Jonathan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Ho
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.Isoperimetric.BrunnMinkowski

/-!
# The isoperimetric inequality

A direct application of the Brunn–Minkowski inequality to a measurable set `A`
and an `ε`-ball yields the standard form of the isoperimetric inequality
relating `volume A`, the volume of the unit ball, and the volume of the
`ε`-thickening of `A`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

/-- The volume of a Euclidean ball of radius `ε` raised to the `1/(d+1)`-th power equals the
corresponding power for the unit ball times `ε`. -/
lemma volume_ball_relation {d : ℕ} {ε : ℝ} :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) ε) ^ ((d:ℝ)+1)⁻¹
    = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ^ ((d:ℝ)+1)⁻¹
      * ENNReal.ofReal ε := by
  simp only [EuclideanSpace.volume_ball, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr (by linarith)), mul_comm]
  congr
  rw [show (d : ℝ) + 1 = (↑(d + 1) : ℝ) by simp]
  exact ENNReal.pow_rpow_inv_natCast (by linarith) (ENNReal.ofReal ε)
