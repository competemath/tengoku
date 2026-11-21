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

/--
@isnad1 id=eq.0h0v.s5.3c2ae9b2f8d6 from=translated src=- shape=e70fad26 vocab=733e2c61
-/
theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

/--
@isnad1 id=le.0h0v.s4.f53032241cfe from=translated src=- shape=cf0a9d99 vocab=75e1f5d6
-/
theorem sqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2

/--
@isnad1 id=lt.0h0v.s4.5a2fc6175798 from=translated src=- shape=339e478a vocab=18350630
-/
theorem sqrt2_lt_bound : Real.sqrt 2 < 1.4142136 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

/--
@isnad1 id=lt.0h0v.s4.77fdfb323f0a from=translated src=- shape=8905eb1d vocab=18350630
-/
theorem sqrt2_gt_bound : 1.4142135 < Real.sqrt 2 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

/--
@isnad1 id=lt.0h0v.s4.b3ff49853193 from=translated src=- shape=339e478a vocab=18350630
-/
theorem sqrt2_lt_tight_bound : Real.sqrt 2 < 1.414213562374 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

/--
@isnad1 id=lt.0h0v.s4.19c50cfe85e0 from=translated src=- shape=8905eb1d vocab=18350630
-/
theorem sqrt2_gt_tight_bound : 1.414213562373 < Real.sqrt 2 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

/--
@isnad1 id=lt.0h0v.s4.e588007e385d from=translated src=- shape=cf0a9d99 vocab=a8bb4d87
-/
theorem one_lt_sqrt2 : 1 < Real.sqrt 2 := by
  nlinarith [sqrt2_mul_self, sqrt2_nonneg]

/--
@isnad1 id=lt.0h0v.s5.0fe7c50414ad from=translated src=- shape=dbe7e8c0 vocab=760a98d0
-/
theorem rhoStar_denom_pos : 0 < 2 * Real.sqrt 2 - 1 := by linarith [one_lt_sqrt2]

/-- The defining identity `ρ* (2√2 - 1) = 2`: the only fact about `ρ*` the
weight inequality needs.
@isnad1 id=eq.0h0v.s5.65f32d12184d from=translated src=- shape=ffd48753 vocab=5372f629
-/
theorem rhoStar_mul_denom : rhoStar * (2 * Real.sqrt 2 - 1) = 2 :=
  div_mul_cancel₀ 2 (ne_of_gt rhoStar_denom_pos)

/-- The rationalized closed form advertised in the paper.
@isnad1 id=eq.0h0v.s5.1eb58b5ad9d5 from=translated src=- shape=3ec94b26 vocab=1f6b2089
-/
theorem rhoStar_eq_rationalized :
    rhoStar = (4 * Real.sqrt 2 + 2) / 7 := by
  rw [rhoStar]
  field_simp [rhoStar_denom_pos.ne']
  nlinarith [sqrt2_mul_self]

/--
@isnad1 id=lt.0h0v.s3.e6973432e3b6 from=translated src=- shape=ff3a10fc vocab=eb6fb4eb
-/
theorem rhoStar_pos : 0 < rhoStar := div_pos (by norm_num) rhoStar_denom_pos

/--
@isnad1 id=lt.0h0v.s3.c1b3c9ad2d2c from=translated src=- shape=ff3a10fc vocab=eb6fb4eb
-/
theorem one_lt_rhoStar : 1 < rhoStar := by
  rw [rhoStar, lt_div_iff₀ rhoStar_denom_pos]
  nlinarith [sqrt2_lt_bound]

/--
@isnad1 id=le.0h0v.s3.3d955dee1b28 from=translated src=- shape=ff3a10fc vocab=0d2c9929
-/
theorem one_le_rhoStar : 1 ≤ rhoStar := le_of_lt one_lt_rhoStar

/-- Decimal bracketing: `1.09383 < ρ* < 1.09384`.
@isnad1 id=and.0h0v.s4.296c35694e42 from=translated src=- shape=fc8ed4a3 vocab=1cee843d
-/
theorem rhoStar_bounds : 1.09383 < rhoStar ∧ rhoStar < 1.09384 := by
  constructor
  · rw [rhoStar, lt_div_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_lt_bound]
  · rw [rhoStar, div_lt_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_gt_bound]

/-- Ten-decimal bracketing of the exact constant.
@isnad1 id=and.0h0v.s4.d424df8d4b66 from=translated src=- shape=fc8ed4a3 vocab=1cee843d
-/
theorem rhoStar_tight_bounds :
    1.09383632135 < rhoStar ∧ rhoStar < 1.09383632136 := by
  constructor
  · rw [rhoStar, lt_div_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_lt_tight_bound]
  · rw [rhoStar, div_lt_iff₀ rhoStar_denom_pos]
    nlinarith [sqrt2_gt_tight_bound]

end

end Goemans
