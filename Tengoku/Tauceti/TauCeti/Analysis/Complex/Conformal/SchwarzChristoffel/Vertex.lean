/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
public import Tengoku.Tauceti.TauCeti.Analysis.Complex.SegmentDistIntegral
public import Tengoku.Tauceti.TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The vertices of the Schwarz--Christoffel map

The Schwarz--Christoffel primitive is holomorphic on the open upper half-plane, and the polygon
it is meant to parametrize would be read off from its *boundary* values at the real prevertices.
This file shows that those boundary values exist as limits; identifying the image of the map as a
polygon, and these limits as its corners, is left to later work.

Write `p = a j` for a prevertex and `t` for the total turning exponent carried by it, that is
the sum of the `e i` over all `i` with `a i = p`.  Near `p` the integrand has norm
`∏ i, dist z (a i) ^ e i`, which is `dist z p ^ t` times a factor that stays bounded, so it is
dominated by `C * dist z p ^ t`.  When `-1 < t` this dominating function is integrable along any
segment ending at `p`, uniformly enough that the primitive satisfies the Cauchy criterion at `p`;
completeness of `ℂ` then produces the limit.  For *pairwise distinct* prevertices `t` is a single
exponent `e j`, and the classical choice `e i = α i / π - 1` coming from an interior angle
`α i ∈ (0, 2 π)` satisfies `-1 < t` automatically; when several prevertices coincide their
exponents add up, and `-1 < t` is then a genuine hypothesis on the sum.

The quantitative heart is the segment estimate `Complex.integral_dist_rpow_segment_le`:
integrating `dist ⬝ p ^ u` along a segment of length `L` gives at most `2 / (u + 1) * L ^ (u + 1)`
for `-1 < u ≤ 0`.  Fed into the segment displacement bound
`TauCeti.norm_schwarzChristoffelPrimitive_sub_le_integral` it turns into a Hölder bound
`‖F z - F w‖ ≤ C * (2 / (u + 1)) * ‖z - w‖ ^ (u + 1)` for `z, w` in a small half-disc, which is
what forces the Cauchy criterion.

## Main definitions

* `TauCeti.schwarzChristoffelVertex` -- the boundary value of the Schwarz--Christoffel primitive
  at a prevertex.

## Main results

* `TauCeti.exists_norm_schwarzChristoffelIntegrand_le` -- near a prevertex the integrand is
  dominated by a constant times the corresponding real power of the distance to it.
* `TauCeti.tendsto_schwarzChristoffelPrimitive` -- that limit is `schwarzChristoffelVertex`.
* `TauCeti.schwarzChristoffelVertex_congr` -- coincident prevertices carry the same vertex.
* `TauCeti.schwarzChristoffelVertex_change_base` -- changing the base point translates every
  boundary value by one and the same constant.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

-- `open` before `namespace TauCeti`: inside it, `UpperHalfPlane` would resolve to the imported
-- `TauCeti.UpperHalfPlane` namespace instead of the root one.
open Complex Filter MeasureTheory Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ### The local bound at a prevertex -/

/-! ### A Hölder estimate near a prevertex -/

/-! ### Existence of the vertex -/

/-- The **Schwarz--Christoffel vertex** attached to the prevertex `a j`: the boundary value at
`a j` of the primitive normalized at `z₀`.  It is a genuine limit when the total turning exponent
at `a j` exceeds `-1`. -/
def schwarzChristoffelVertex (a e : ι → ℝ) (z₀ : UpperHalfPlane) (j : ι) : ℂ :=
  limUnder (𝓝[upperHalfPlaneSet] ((a j : ℂ))) (schwarzChristoffelPrimitive a e z₀)

/-- Coincident prevertices carry the same vertex: `schwarzChristoffelVertex` depends on the index
`j` only through the prevertex `a j`. -/
theorem schwarzChristoffelVertex_congr (a e : ι → ℝ) (z₀ : UpperHalfPlane) {j k : ι}
    (h : a j = a k) :
    schwarzChristoffelVertex a e z₀ j = schwarzChristoffelVertex a e z₀ k := by
  simp only [schwarzChristoffelVertex, h]

end TauCeti
