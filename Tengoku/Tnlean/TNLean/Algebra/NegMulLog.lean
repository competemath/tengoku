/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Log.NegMulLog

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An identity for the negated multiplication by logarithm

This file supplies a generic identity for `Real.negMulLog` that is useful when
computing the entropy of a uniform distribution.
-/

namespace Real

/-- For `d ≠ 0`, `d * Real.negMulLog d⁻¹ = Real.log d`.

Upstreamable to Mathlib's `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`,
which has no lemma of this shape.
@isnad1 id=eq.1h1v.s4.21f361878a2f from=translated src=- shape=6935551d vocab=ec614cda
-/
theorem mul_negMulLog_inv (d : ℝ) (hd : d ≠ 0) :
    d * Real.negMulLog d⁻¹ = Real.log d := by
  rw [Real.negMulLog]
  calc
    d * (-(d⁻¹) * Real.log (d⁻¹)) = -(d * d⁻¹ * Real.log (d⁻¹)) := by ring
    _ = -(1 * Real.log (d⁻¹)) := by field_simp [hd]
    _ = -Real.log (d⁻¹) := by simp
    _ = Real.log d := by rw [Real.log_inv, neg_neg]

end Real
