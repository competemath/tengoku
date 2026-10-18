/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.BoundaryMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# M2: consequences of double ergodicity

For a countable `Γ ≤ SL(2, ℝ)` acting doubly ergodically on the boundary:

* `IsDoublyErgodic.null_or_conull`: almost invariant measurable subsets of `B × B` are null or
  conull;
* `IsDoublyErgodic.ae_const`: almost invariant measurable maps from `B × B` to a countably
  separated space are almost everywhere constant;
* the same on `B` itself (`null_or_conull_single`, `ae_const_single`).
-/

open MeasureTheory Filter Set
open scoped MatrixGroups

namespace OrbicurveCores.M2

/-- The diagonal action on pairs of boundary points. -/
noncomputable def dact (γ : SL(2, ℝ)) (p : OnePoint ℝ × OnePoint ℝ) : OnePoint ℝ × OnePoint ℝ :=
  (γ • p.1, γ • p.2)

lemma bdry_ne_zero : bdry ≠ 0 := by
  intro h
  have : bdry univ = 0 := by rw [h]; rfl
  rw [bdry, Measure.map_apply OnePoint.continuous_coe.measurable MeasurableSet.univ,
    preimage_univ, Real.volume_univ] at this
  exact ENNReal.top_ne_zero this

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ]

end OrbicurveCores.M2
