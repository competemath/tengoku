/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Scheme.IdealSheaf.Order.Along

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# The generic points of a closed set: a restatement

`mem_genericPoints_iff`: the generic points of a closed set are the points whose closure is a
maximal irreducible subset of it; this restates `Closeds.mem_genericPoints_iff` of
`Hironaka/Scheme/IdealSheaf/Order/Along.lean` and has no user.

The mathematics of the order function at a point, along a closed subset and under isomorphisms,
open immersions and completion is in `Hironaka/Scheme/IdealSheaf/Order/Basic.lean`,
`Hironaka/Scheme/IdealSheaf/Order/Along.lean` and
`Hironaka/Scheme/IdealSheaf/Order/Invariance.lean`.
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- The generic points of a closed set are the points whose closure is a maximal irreducible
subset of it; restates `Closeds.mem_genericPoints_iff`.-/
theorem mem_genericPoints_iff (Z : Closeds X) (η : X) :
    η ∈ Z.genericPoints ↔ Maximal (fun T : Set X => T ⊆ Z ∧ IsIrreducible T) (closure {η}) :=
  Closeds.mem_genericPoints_iff Z η

end AlgebraicGeometry
