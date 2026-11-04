/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The underlying matrix of a positive-determinant invertible matrix

`Matrix.GLPos n R` is a subgroup of `GL n R`, which is a group of units, so
reading off the matrix takes two coercions. `toMat` is that composite, together
with the two lemmas saying it is a monoid map.

Neutral general-linear-group API: it mentions no cover, no phase and no
stability condition, and it is consumed independently by the universal cover of
`GL⁺(2, ℝ)` under `UniversalCover/`, by the complex-coordinate adapter in
`LinearAlgebra/Complex/Coordinates.lean`, and by the stability action under
`CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Action/`.
Extracted by MO1.12 (#1323) from the cover's `Basic.lean`, where it was
declared; the fully qualified names are unchanged, per the cutover ledger's
first standing decision.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

/-- The matrix underlying an element of `GL⁺(2, ℝ)`.-/
def toMat (T : Matrix.GLPos (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((T : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)

/--
@isnad1 id=eq.0h2v.s11.274a186e420b from=translated src=- shape=0d0a69b1 vocab=88257bf9
-/
@[simp]
theorem toMat_mul (T U : Matrix.GLPos (Fin 2) ℝ) :
    toMat (T * U) = toMat T * toMat U := rfl

/--
@isnad1 id=eq.0h0v.s9.25d76e3ec6d8 from=translated src=- shape=b2e0f11e vocab=c4d5d2e2
-/
@[simp]
theorem toMat_one : toMat 1 = 1 := rfl

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
