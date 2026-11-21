/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The extremal constant `ρ* = 2/(2√2 - 1)`

Basic facts about `ρ* = 2/(2√2 - 1) = (4√2 + 2)/7 ≈ 1.0938363`, the exact
extremal cost ratio of the Rybin digraph `H*` (Theorem A of the paper).
The only irrational ingredient of the whole development is
`ρ* · (2√2 - 1) = 2`.
-/

namespace Goemans

noncomputable section

open Real

/-- The extremal ratio `ρ* = 2/(2√2 - 1)` of Theorem A.-/
def rhoStar : ℝ := 2 / (2 * Real.sqrt 2 - 1)

theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem sqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2

theorem sqrt2_lt_bound : Real.sqrt 2 < 1.4142136 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

theorem sqrt2_gt_bound : 1.4142135 < Real.sqrt 2 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

theorem sqrt2_lt_tight_bound : Real.sqrt 2 < 1.414213562374 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

theorem sqrt2_gt_tight_bound : 1.414213562373 < Real.sqrt 2 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

theorem one_lt_sqrt2 : 1 < Real.sqrt 2 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

theorem rhoStar_denom_pos : 0 < 2 * Real.sqrt 2 - 1 := by linarith [one_lt_sqrt2]

/-- The defining identity `ρ* (2√2 - 1) = 2`: the only fact about `ρ*` the
weight inequality needs.-/
theorem rhoStar_mul_denom : rhoStar * (2 * Real.sqrt 2 - 1) = 2 :=
  div_mul_cancel₀ 2 (ne_of_gt rhoStar_denom_pos)

/-- The rationalized closed form advertised in the paper.-/
theorem rhoStar_eq_rationalized :
    rhoStar = (4 * Real.sqrt 2 + 2) / 7 := by
  rw [rhoStar]
  field_simp [rhoStar_denom_pos.ne']
  nlinarith [sqrt2_mul_self]

theorem rhoStar_pos : 0 < rhoStar := div_pos (by norm_num) rhoStar_denom_pos

theorem one_lt_rhoStar : 1 < rhoStar := by
  rw [rhoStar, lt_div_iff₀ rhoStar_denom_pos]
  nlinarith [sqrt2_lt_bound]

theorem one_le_rhoStar : 1 ≤ rhoStar := le_of_lt one_lt_rhoStar

/-- Decimal bracketing: `1.09383 < ρ* < 1.09384`.-/
theorem rhoStar_bounds : 1.09383 < rhoStar ∧ rhoStar < 1.09384 := by
  constructor
  · rw [rhoStar, lt_div_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_lt_bound]
  · rw [rhoStar, div_lt_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_gt_bound]

/-- Ten-decimal bracketing of the exact constant.-/
theorem rhoStar_tight_bounds :
    1.09383632135 < rhoStar ∧ rhoStar < 1.09383632136 := by
  constructor
  · rw [rhoStar, lt_div_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_lt_tight_bound]
  · rw [rhoStar, div_lt_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_gt_tight_bound]

end

end Goemans
