/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Tengoku.Tauceti.TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import Tengoku
public import Tengoku.Tauceti.TauCeti.Geometry.Manifold.LocalDiffeomorph
/-!
# Local inverse of the Lie-group exponential

The smooth coordinate exponential has derivative the identity at zero, so the inverse function
theorem supplies a chosen smooth local logarithm in model-space identity coordinates.

Transporting that logarithm through the identity chart gives a group-level local inverse for the
tangent-space exponential.

## Main results

* `mulInvariantLog`: a local logarithm from the group to its tangent Lie algebra.
* `lieLog`: the same chosen local logarithm, valued in left-invariant derivations.
* `hasFDerivAt_mulInvariantLogChart_one`: the coordinate logarithm has derivative the identity
  at the identity coordinate.
* `eventually_mulInvariantExp_log`: exponential followed after logarithm is locally the identity.
* `eventually_mulInvariantLog_exp`: logarithm followed after exponential is locally the identity.
* `isLocalDiffeomorphAt_lieExp_zero`: the canonical Lie-group exponential is a local
  `C∞` local diffeomorphism at zero.
* `isLocalDiffeomorphAt_mulInvariantExpChart_zero`: the fully charted exponential is a local
  `C∞` local diffeomorphism at zero.
* `exists_injOn_mulInvariantExp_modelSpace`: exponential is injective near zero.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/
public section
open Filter Function Manifold
open scoped ContDiff Manifold Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]
attribute [local instance] LieGroup.minSmoothnessThree

/-- The tangent-space exponential with both domain and codomain expressed in identity-chart
coordinates. -/
noncomputable def mulInvariantExpChart [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) : E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))

/-- The fully charted exponential is the identity chart applied to the tangent-space
exponential. -/
theorem mulInvariantExpChart_apply [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) :
    mulInvariantExpChart (I := I) (G := G) v =
      extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) := by
  rfl

/-- The coordinate exponential sends zero to the identity coordinate. -/
@[simp]
theorem mulInvariantExpChart_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantExpChart (I := I) (G := G) 0 =
      extChartAt I (1 : G) (1 : G) := by
  rw [mulInvariantExpChart_apply]
  -- `GroupLieAlgebra I G` is definitionally the model space `E`.
  change extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (0 : GroupLieAlgebra I G)) = _
  rw [mulInvariantExp_zero]
