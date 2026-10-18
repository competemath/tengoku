/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.AdditivityValuation
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.TangentThirdChordAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Non-vanishing of the doubling third chord point (`w₃ ≠ 0`, issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  This file is the **doubling (tangent) analog** of
`Reduction/ThirdChordNonvanishing.lean`: for a single parameter `z ∈ 𝔪` (the point `P = Q`, tangent
case, diagonal family `![z, z]`) the formal-side addition law produces the third tangent point
`(t, w₃)` in the `(z, w)`-plane, with `t = thirdRootNum` the Vieta double-root third point and
`w₃ = thirdChordW = λ t + ν`.

The doubling coordinate identity `localParam_add_diag` / the point-level `localParam_add_of_X_eq`
(`Reduction/TangentThirdChordAffine.lean`) carry a hypothesis `hw : w₃ ≠ 0` (geometrically: the
third tangent point is not at infinity, i.e. `2P ≠ O`).  This file **discharges** it in the doubling
case, alongside the intercept non-vanishing `ν ≠ 0` (`chordIntercept_ne_zero_diag`).

The argument mirrors the secant one: `(t, w₃)` solves the same numeric Weierstrass functional
equation as the coordinate expansion `wParam`, and both `t, w₃` lie in `𝔪`; by uniqueness of the
small solution (`wFunctionalEq_unique`) one has `w₃ = wParam t`.  This turns `w₃ ≠ 0` into `t ≠ 0`
(as `wParam z = z³ · unit`).  Finally `t = 0` would force `w₃ = ν = 0`, contradicting
`chordIntercept_ne_zero_diag`.  The intercept non-vanishing itself uses the tangency: if `ν = 0`
then the collinearity `w = λ z + ν` forces `λ x = 1` (so `λ ≠ 0`), and the cross-identity
`P_num · ν = λ · w · P_den` (the numerator of the tangent-slope identity, `slope_xParam_tangent`)
forces `P_den = a₁ z + a₃ w - 2 = 0`; but `P_den = w · (y - negY x y) ≠ 0` when `2P ≠ O`.

## Main results

* `WeierstrassCurve.chordIntercept_ne_zero_diag` — **`ν ≠ 0`** in the doubling case (from `2P ≠ O`).
* `WeierstrassCurve.thirdChordW_eq_wParam_diag` — `w₃ = wParam t` (diagonal).
* `WeierstrassCurve.thirdRootNum_ne_zero_diag` — `t ≠ 0` in the doubling case.
* `WeierstrassCurve.thirdChordW_ne_zero_diag` — **`w₃ ≠ 0`** in the doubling case (discharges `hw`).

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
