/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Exponents
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arithmetic of the corner iteration

This is the rational update from Sections 2.4 and 13 of the supplied projection
manuscript. Its algebra does not itself prove the geometric corner estimate.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- The ideal projection exponent after a corner improvement.-/
noncomputable def cornerUpdate (β : ℝ) : ℝ := (3 * β ^ 2 + 2 * β - 2) / (β ^ 2 + 3 * β - 2)

private lemma denominator_pos_aux {β : ℝ} (hβ : 1 < β) : 0 < β ^ 2 + 3 * β - 2 := by
  nlinarith [sq_nonneg β]

/--
@isnad1 id=eq.1h1v.s7.1d8d2c7670c4 from=translated src=- shape=445d6104 vocab=4f3ca7d5
-/
theorem cornerUpdate_sub {β : ℝ} (hβ : 1 < β) :
    cornerUpdate β - β = -(β ^ 3 - 4 * β + 2) / (β ^ 2 + 3 * β - 2) := by
  unfold cornerUpdate
  apply (eq_div_iff (denominator_pos_aux hβ).ne').2
  rw [sub_mul, div_mul_cancel₀ _ (denominator_pos_aux hβ).ne']
  ring

/--
@isnad1 id=eq.0h0v.s2.6f2dc8c2a742 from=translated src=- shape=4b736592 vocab=37f17f26
-/
theorem cornerUpdate_projectionExponent : cornerUpdate projectionExponent = projectionExponent := by
  have h := cornerUpdate_sub projectionExponent_mem.1
  rw [projectionExponent_cubic, neg_zero, zero_div, sub_eq_zero] at h
  exact h

/--
@isnad1 id=lt.2h1v.s6.dfe6285f9ed8 from=translated src=- shape=54c0d436 vocab=8b795db0
-/
theorem cornerUpdate_lt_self {β : ℝ} (hβ : 1 < β) (h : 0 < β ^ 3 - 4 * β + 2) :
    cornerUpdate β < β := by
  rw [← sub_neg, cornerUpdate_sub hβ]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos h) (denominator_pos_aux hβ)

end NKBesicovitch.Projection
