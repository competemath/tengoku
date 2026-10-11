/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Mathlib.Optimization.Affine.SignCell.Closure
public import Tengoku.Causalean.Causalean.Mathlib.Optimization.Affine.SignCell.CommonSlack

/-! # Mixed strict/weak sign-cell example

This module instantiates the API with the interval cut out by the strict inequality `0 < x`
and the weak inequality `x ≤ 1`.
-/

@[expose] public section

open Set

namespace Causalean.Mathlib.Optimization.Affine.SignCell

/-- The [mixed one-dimensional example system](goal) is given by [the strict lower inequality
`-x < 0` and the weak upper inequality `x - 1 ≤ 0`](step:1). -/
def mixedExample : AffineSystem 1 :=
  [ { fn := { coeff := fun _ => -1, constant := 0 }, kind := .strict },
    { fn := { coeff := fun _ => 1, constant := -1 }, kind := .weak } ]

/-- Given [a one-dimensional coordinate vector](hyp:x), [it belongs to the example's strict
cell exactly when its coordinate lies above zero and at most one](goal).
@isnad1 id=iff.0h1v.s6.6df6d3d20893 from=translated src=- shape=2700e843 vocab=9c04b83d
-/
theorem mem_strictCell_mixedExample (x : Fin 1 → ℝ) :
    x ∈ strictCell mixedExample ↔ 0 < x 0 ∧ x 0 ≤ 1 := by
  simp [strictCell, mixedExample, Constraint.strictHolds, AffineFn.eval]

/-- Given [a one-dimensional coordinate vector](hyp:x), [it belongs to the example's weak
cell exactly when its coordinate lies between zero and one inclusively](goal).
@isnad1 id=iff.0h1v.s6.72638700acda from=translated src=- shape=2700e843 vocab=9b2e37be
-/
theorem mem_weakCell_mixedExample (x : Fin 1 → ℝ) :
    x ∈ weakCell mixedExample ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  simp [weakCell, mixedExample, Constraint.weakHolds, AffineFn.eval]

/-- [The constant one-half coordinate vector belongs to the example's strict cell](goal).
@isnad1 id=mem.0h0v.s6.8e47926e551f from=translated src=- shape=0073fd52 vocab=a543455e
-/
theorem half_mem_strictCell_mixedExample :
    (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ strictCell mixedExample := by
  rw [mem_strictCell_mixedExample]
  norm_num

/-- [The closure of the example's half-open strict interval equals its closed weak interval](goal).
@isnad1 id=eq.0h0v.s5.0293be5b15d1 from=translated src=- shape=fdeef8e7 vocab=5ab03e33
-/
theorem closure_strictCell_mixedExample :
    closure (strictCell mixedExample) = weakCell mixedExample := by
  apply closure_strictCell_eq_weakCell
  exact ⟨_, half_mem_strictCell_mixedExample⟩

end Causalean.Mathlib.Optimization.Affine.SignCell
