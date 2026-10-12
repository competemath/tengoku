/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.ODE.SmoothParameter
public import Tengoku.Tauceti.TauCeti.Geometry.Lie.Exponential.ParameterDependence

/-!
# Smoothness of the Lie-group exponential

This file upgrades the continuous local invariant flow to smooth parameter dependence, proves that
the Lie-group exponential is smooth at the zero vector, and globalizes that result using its
one-parameter-subgroup law.

## Main results

* `contMDiffAt_mulInvariantExp_modelSpace_zero`: the tangent-space exponential is smooth at zero.
* `contMDiff_mulInvariantExp`: the tangent-space exponential is smooth everywhere.
* `contMDiff_lieExp`: the derivation-based Lie-group exponential is smooth everywhere.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

attribute [local instance] LieGroup.minSmoothnessThree
