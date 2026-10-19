/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Topology.JacobsonSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed points of Jacobson spaces are very dense

In a Jacobson space every nonempty locally closed subset contains a closed point
(`nonempty_inter_closedPoints`). In particular an open subset containing all closed points is the
whole space, and a closed subset containing no closed point is empty.

## Main results

- `JacobsonSpace.eq_empty_of_isClosed_of_disjoint_closedPoints`: a closed subset without closed
  points is empty.
- `JacobsonSpace.eq_univ_of_isOpen_of_closedPoints_subset`: an open subset containing all closed
  points is everything.
-/

variable {X : Type*} [TopologicalSpace X] [JacobsonSpace X]

/-- In a Jacobson space, a closed subset containing no closed point is empty. -/
theorem JacobsonSpace.eq_empty_of_isClosed_of_disjoint_closedPoints {Z : Set X}
    (hZ : IsClosed Z) (h : Disjoint Z (closedPoints X)) : Z = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.2 hne)
    hZ.isLocallyClosed
  exact Set.disjoint_left.1 h hx.1 hx.2

/-- **In a Jacobson space, an open subset containing all closed points is everything.** -/
theorem JacobsonSpace.eq_univ_of_isOpen_of_closedPoints_subset {U : Set X} (hU : IsOpen U)
    (h : closedPoints X ⊆ U) : U = Set.univ := by
  have := eq_empty_of_isClosed_of_disjoint_closedPoints hU.isClosed_compl
    (Set.disjoint_compl_left_iff_subset.2 h)
  simpa using this
