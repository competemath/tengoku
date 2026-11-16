/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Tengoku.Seed.Dynamics.FixedPoints.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Idempotent functions

This file relates the range and fixed points of an idempotent function.
-/

public section

open Set

namespace Function

/-- The range of an idempotent function is its set of fixed points.
@isnad1 id=eq.1h2v.s4.935759672c82 from=translated src=- shape=ecee2a4c vocab=d2374e2f
-/
theorem range_eq_fixedPoints_of_idempotent {α : Type*} {f : α → α}
    (hf : ∀ x, f (f x) = f x) : range f = fixedPoints f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact hf y
  · intro hx
    exact ⟨x, mem_fixedPoints_iff.mp hx⟩

end Function
