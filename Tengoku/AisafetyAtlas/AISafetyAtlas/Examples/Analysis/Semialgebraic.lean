module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Analysis.Semialgebraic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked semialgebraic sets

`AISafetyAtlas.Analysis.Semialgebraic` supplies the notion MAIS-A2 `prob:exact`
names and Mathlib does not have. This module runs it on concrete sets, so the
definition is checked against examples rather than only asserted to be the
standard one.

The pairing that matters for `prob:exact` is **compact and semialgebraic at
once**: the unit square below is both, which is what makes print's hypothesis
non-vacuous as a shape. A half-plane is semialgebraic and not compact, which is
what makes the compactness half of the hypothesis do work.
-/

namespace AISafetyAtlas.Examples.Analysis.Semialgebraic

open AISafetyAtlas.Analysis
open MvPolynomial

/-! ## The unit square is compact semialgebraic -/

/-- The unit square in `ℝ²`, as a closed box.-/
public noncomputable def unitSquare : Set (Fin 2 → ℝ) := ClosedBox (fun _ ↦ 0) 1

/-! ## A set cut out by one sign condition -/

/-- The closed half-plane `x₀ ≥ 0`, given by a single sign condition.-/
public noncomputable def halfPlane : Set (Fin 2 → ℝ) :=
  BasicSemialgebraic {(X 0, PolySign.nonneg)}

/-! ## Unions stay semialgebraic -/

/-! ## The rest of the Boolean algebra

Closure under union is the one third of BCR §2.1's closure statement that
`prob:exact` exercises for free, because a class is presented as a union of
boxes. These run the other two thirds — intersection, complement, and the
difference they combine into — on sets the reader can see.
-/

/-! ## The case that forces the two-piece split -/

/-- The line `x₀ = 0` in `ℝ²`, cut out by a single `zero` condition.-/
public noncomputable def axis : Set (Fin 2 → ℝ) :=
  BasicSemialgebraic {(X 0, PolySign.zero)}

/-! ## Cutting one set down by another -/

end AISafetyAtlas.Examples.Analysis.Semialgebraic
