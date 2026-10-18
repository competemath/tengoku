/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.FormalGroupTangent
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ChordAffineBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The affine↔formal tangent line bridge (issue #367, doubling case)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  This file is the **doubling (tangent) analog** of
`Reduction/ChordAffineBridge.lean`: it transports the diagonal formal chord line to the affine
`(x, y)`-plane in the doubling case `z₁ = z₂ = z` (the point `P = Q`), where the chord line is the
**tangent** to the `(z, w)`-curve at the double point.

On the diagonal the formal chord data specialise to `λ = chordSlope ![z, z]` (which equals the
formal derivative `w′(z)`, `chordSlope_diag`) and `ν = chordIntercept ![z, z]`, and the tangent
line `w = λ z + ν` transports (under `x = z / w`, `y = -1 / w`) to the affine tangent line through
the single recovered point `(xParam z, yParam z)`.

* `WeierstrassCurve.slope_xParam_tangent` — **the affine tangent slope is `λ / ν`**: Mathlib's
  doubling slope `W.slope x x y y` (the tangent of `W` at the recovered point) equals
  `chordSlope / chordIntercept`, exactly as in the secant case (`slope_xParam_secant`).  The proof
  is the doubling analog: in place of the secant's two collinearity relations it combines the single
  collinearity `wParam_eq_chordLine₀`, the tangency relation `wParamDeriv_tangency` (with
  `λ = chordSlope`, via `chordSlope_diag`), and the value equation `wParam_functional_eq`.

This is the load-bearing bridge identity the doubling affine-matching rung of issue #367 consumes
(the tangent analog of the merged `localParam_add_secant`), carrying the non-vanishing side
conditions `ν ≠ 0` and `y ≠ negY x y` (i.e. `2P ≠ O`) as hypotheses, mirroring how the secant chain
carried its side conditions before discharging them.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z : R}

end WeierstrassCurve
