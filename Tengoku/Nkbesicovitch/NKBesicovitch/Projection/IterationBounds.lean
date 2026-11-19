/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Iteration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict decrease of the corner update above the critical exponent

The projection exponent lies above `3/2`. Above that root, the defining
cubic is positive, so the corner update strictly decreases the exponent.
The update is continuous throughout the range where input estimates are
used. These facts justify approximation to the critical exponent.
-/

public section

namespace NKBesicovitch.Projection

/--
@isnad1 id=lt.0h0v.s4.90f22a2be6d1 from=translated src=- shape=5ccaf027 vocab=5fa2cff6
-/
theorem three_halves_lt_projectionExponent : (3 : ℝ) / 2 < projectionExponent := by
  unfold projectionExponent
  have hd : 0 < criticalExponent - 1 := by linarith [criticalExponent_bounds.1]
  apply (lt_div_iff₀ hd).mpr
  linarith [criticalExponent_bounds.2]

/--
@isnad1 id=lt.1h1v.s3.7e0b589bf0a0 from=translated src=- shape=284c73b4 vocab=71a46dc1
-/
theorem cornerUpdate_lt_self_of_gt {β : ℝ} (hβ : projectionExponent < β) :
    cornerUpdate β < β := by
  apply cornerUpdate_lt_self (projectionExponent_mem.1.trans hβ)
  have hα := three_halves_lt_projectionExponent
  have hq : 0 < β ^ 2 + β * projectionExponent + projectionExponent ^ 2 - 4 := by
    nlinarith [sq_nonneg β, mul_pos (sub_pos.mpr hβ)
      (zero_lt_one.trans projectionExponent_mem.1)]
  nlinarith [projectionExponent_cubic, mul_pos (sub_pos.mpr hβ) hq]

/--
@isnad1 id=continuo.1h1v.s4.28fa824f2680 from=translated src=- shape=4d60c403 vocab=2416d73c
-/
theorem continuousAt_cornerUpdate {β : ℝ} (hβ : 1 < β) : ContinuousAt cornerUpdate β := by
  have hd : β ^ 2 + 3 * β - 2 ≠ 0 := by nlinarith [sq_nonneg β]
  unfold cornerUpdate
  fun_prop

end NKBesicovitch.Projection
