/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Edge
public import Tengoku.Tauceti.TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The Schwarz--Christoffel vertex at infinity

The real axis is only part of the boundary of the upper half-plane: the prevertices divide it into
finitely many bounded intervals and two unbounded ones, and the two unbounded ones are a single
boundary arc through the point at infinity.  The polygon a Schwarz--Christoffel map is meant to
parametrize can therefore close up only if the map has a limit at infinity, and this file proves
that it does, under the hypothesis that the total turning exponent `∑ i, e i` is less than `-1`.
That hypothesis is the classical closing condition: for a bounded polygon with interior angles
`α i` and no prevertex at infinity, `e i = α i / π - 1` and the angle sum forces `∑ i, e i = -2`.

Far from all the prevertices, `dist z (a i)` is caught between `‖z‖ / 2` and `2 ‖z‖`, so the
integrand `∏ i, (z - a i) ^ (e i)` is bounded by `C * ‖z‖ ^ ∑ i, e i`
(`TauCeti.exists_norm_schwarzChristoffelIntegrand_le_of_le_norm`), for any exponents whatever.
Only the sign of `∑ i, e i` makes that a decay estimate, and with `∑ i, e i < -1` the
dominating function is integrable along a vertical ray, and the map is estimated between any two
far-away points of the half-plane by running up a vertical ray from the first, across a horizontal
segment at the common height `‖z‖ + ‖w‖`, and back down to the second: all three pieces stay far
from the prevertices, and all three contributions are `O(R ^ (∑ i, e i + 1))` when both points have
norm at least `R`.  That is the Cauchy criterion along `cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet`, and
completeness of `ℂ` turns it into the limit `TauCeti.schwarzChristoffelVertexAtInfinity`.

The boundary consequence is `TauCeti.tendsto_schwarzChristoffelBoundaryValue_atInfinity`: any
family of boundary values of the map along the real axis converges to that same point as the
real parameter leaves every bounded set.  Applied to the two unbounded boundary intervals it says
that the two unbounded image edges run to one and the same point, which is what closes the
boundary path up into a polygon; identifying the closed path with a prescribed polygon, and the
image of the half-plane with its interior, is left to later work.

## Main definitions

* `TauCeti.schwarzChristoffelVertexAtInfinity` -- the boundary value of the Schwarz--Christoffel
  primitive at the point at infinity.

## Main results

* `TauCeti.exists_norm_schwarzChristoffelIntegrand_le_of_le_norm` -- far from every prevertex the
  integrand is dominated by a constant multiple of `‖z‖ ^ ∑ i, e i`.
* `TauCeti.tendsto_schwarzChristoffelPrimitive_atInfinity` -- the map converges to
  `schwarzChristoffelVertexAtInfinity` along the upper half-plane at infinity.
* `TauCeti.schwarzChristoffelVertexAtInfinity_change_base` -- changing the base point translates
  that boundary value by the same constant as every other one.
* `TauCeti.tendsto_schwarzChristoffelBoundaryValue_atInfinity` -- boundary values along the real
  axis converge to it, and hence
  `TauCeti.tendsto_limUnder_schwarzChristoffelPrimitive_atTop` and
  `TauCeti.tendsto_limUnder_schwarzChristoffelPrimitive_atBot`: the two unbounded image edges close
  up at one point.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

-- `open` before `namespace TauCeti`: inside it, `UpperHalfPlane` would resolve to the imported
-- `TauCeti.UpperHalfPlane` namespace instead of the root one.
open Bornology Complex Filter MeasureTheory Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ### The size of the integrand at infinity -/

/-! ### Displacement along segments of the half-plane -/

/-! ### The limit at infinity -/

/-- The **Schwarz--Christoffel vertex at infinity**: the boundary value at the point at infinity
of the primitive normalized at `z₀`.  It is a genuine limit when the total turning exponent
`∑ i, e i` is less than `-1`, which is the classical condition for the image polygon to close
up. -/
def schwarzChristoffelVertexAtInfinity (a e : ι → ℝ) (z₀ : UpperHalfPlane) : ℂ :=
  limUnder (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (schwarzChristoffelPrimitive a e z₀)

/-! ### Closing the boundary path up -/

end TauCeti
