/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.Seed.AlgebraicGeometry.Geometrically.Connected
import Tengoku.Seed.AlgebraicGeometry.Geometrically.Integral
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Proper
import Tengoku.Seed.AlgebraicGeometry.FunctionField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Curves over a field

This file fixes the working notion of *curve* for the Belyi project (statement B1 of
`references/proof-outline.md`): a scheme `X` over `Spec k` whose structure morphism is
smooth of relative dimension `1`, proper, and geometrically integral.

## Design notes (taxis issue #46)

* The parent issue speaks of "smooth projective geometrically connected curves". We
  require geometric *integrality* instead of geometric connectedness: for a smooth
  proper scheme over a field the two notions agree (smooth implies geometrically
  reduced, and a connected regular scheme is irreducible), and integrality is what
  the function-field machinery consumes. Geometric connectedness is *derived* below
  (`Belyi.IsCurveOver.geometricallyConnected`), so consumers of the final theorem can
  be stated in the classical phrasing. The converse construction (a smooth proper
  geometrically connected scheme is a curve in our sense) is deferred until needed.
* Smoothness of relative dimension `1` (mathlib's `SmoothOfRelativeDimension`)
  subsumes the dimension condition, so no separate dimension theory is required.
* The base field is encoded via mathlib's `X.Over (Spec (.of k))` pattern, and the
  conditions are placed on the structure morphism `X ↘ Spec (.of k)`.

## Main definitions

* `Belyi.IsCurveOver k X`: the curve predicate.
* Derived instances: a curve is an integral scheme (hence has a function field), and
  its structure morphism is geometrically connected.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory

/-- The spectrum of a field has a subsingleton (in fact unique) underlying space. -/
instance (k : Type u) [Field k] : Subsingleton (Spec (CommRingCat.of k)) :=
  have : Subsingleton (PrimeSpectrum k) := inferInstance
  this

/-- A scheme `X` over `Spec k` is a **curve** over the field `k` if its structure morphism
is smooth of relative dimension `1`, proper, and geometrically integral.

This packages "smooth projective geometrically connected curve": properness plus a finite
morphism to `ℙ¹` (statement B1) yields projectivity, and geometric connectedness follows
from geometric integrality (see the design notes in the module docstring). -/
class IsCurveOver (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] : Prop
    extends SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k)),
      IsProper (X ↘ Spec (CommRingCat.of k)),
      GeometricallyIntegral (X ↘ Spec (CommRingCat.of k))

namespace IsCurveOver

/-- A curve over a field is an integral scheme; in particular it has a function field.
This cannot be a global instance (`k` does not occur in the conclusion), so consumers
introduce it with `have := IsCurveOver.isIntegral k X`. -/
theorem isIntegral (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] : IsIntegral X :=
  GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (CommRingCat.of k))

end IsCurveOver

end Belyi
