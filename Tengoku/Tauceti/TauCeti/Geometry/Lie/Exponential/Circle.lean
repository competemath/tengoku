/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Geometry.Lie.Exponential.Classification
public import Tengoku

/-!
# Compatibility with the circle exponential

Mathlib's `Circle.exp` is a continuous one-parameter subgroup of the analytic Lie group `Circle`.
The classification of continuous one-parameter subgroups therefore supplies its unique abstract
Lie-algebra generator. We normalize the one-dimensional Lie algebra identification by sending this
generator to `1`; under that identification, the abstract Lie-group exponential is exactly
`Circle.exp`.

## Main results

* `circleExpHom`: `Circle.exp`, bundled as a continuous multiplicative homomorphism.
* `circleExpGenerator`: its unique left-invariant infinitesimal generator.
* `circleLieAlgebraEquiv`: the identification `Lie(Circle) ≃ₗ[ℝ] ℝ` normalized by that generator.
* `lieExp_circle`: under this identification, the abstract exponential is `Circle.exp`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The matrix and circle shadows".
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

/-- Mathlib's circle exponential, bundled as a continuous homomorphism from the additive real line
written multiplicatively. -/
noncomputable def circleExpHom : ContinuousMonoidHom (Multiplicative ℝ) Circle where
  toMonoidHom := Circle.expHom.toMultiplicativeLeft
  continuous_toFun := Circle.exp.continuous.comp continuous_toAdd

/-- The bundled circle exponential evaluates to Mathlib's `Circle.exp`. -/
@[simp]
theorem circleExpHom_apply (t : ℝ) :
    circleExpHom (Multiplicative.ofAdd t) = Circle.exp t := (rfl)

/-- A preliminary linear identification of the circle Lie algebra with the reals, obtained from
evaluation at the identity and the one-dimensional Euclidean model. -/
private noncomputable def circleLieAlgebraEquivModel :
    LeftInvariantDerivation (𝓡 1) Circle ≃ₗ[ℝ] ℝ :=
  (leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓡 1) (G := Circle)
      BoundarylessManifold.isInteriorPoint).trans
    ((EuclideanSpace.equiv (Fin 1) ℝ).toLinearEquiv.trans
      (LinearEquiv.funUnique (Fin 1) ℝ ℝ))
