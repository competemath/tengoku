/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ThirdChordAffine
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.TangentAffineBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The third tangent point on the affine curve and the doubling coordinate identity (issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  This file is the **doubling (tangent) analog** of
`Reduction/ThirdChordAffine.lean` (its `section Secant` and the point-level
`localParam_add_of_X_ne`): the doubling case `z₁ = z₂ = z` (the point `P = Q`) of issue #367's
affine-matching additivity.

On the diagonal the formal chord line is the **tangent** to the `(z, w)`-curve at the double point,
and the formal-side addition law produces the **third tangent point** `(t, w₃)` with
`t = thirdRootNum` the Vieta double-root complement and `w₃ = λ t + ν = thirdChordW` the value of
the tangent line there (all data at the diagonal family `![z, z]`,
`ha := PowerSeries.diag_mem _ hz`).
This file transports that point to the **affine** `(x, y)`-plane and identifies it with Mathlib's
affine third-intersection point `addX`/`addY`, closing the coordinate-level doubling additivity of
the local parameter.

Writing `X₃ = t / w₃`, `Y₃ = -1 / w₃` for the affine image (via `x = z/w`, `y = -1/w`):

* `WeierstrassCurve.thirdChord_functional_eq_diag` — the third tangent point `(t, w₃)` lies on the
  `(z, w)`-curve (diagonal restatement of `thirdChordPoint_functional_eq_diag` in terms of
  `thirdChordW`, mirroring `thirdChord_functional_eq`).
* `WeierstrassCurve.equation_thirdChordPoint_diag` — `(X₃, Y₃)` lies on the affine curve (numeric
  transport, mirroring `equation_thirdChordPoint`; no `z₁ ≠ z₂` hypothesis is needed here).
* `WeierstrassCurve.thirdChord_on_tangentLine` — `(X₃, Y₃)` lies on the affine tangent line through
  the single recovered point `(xParam z, yParam z)`, i.e. `Y₃ = ℓ (X₃ - x) + y` with
  `ℓ = W.slope x x y y` the affine doubling slope (`= λ / ν`, `slope_xParam_tangent`).
* `WeierstrassCurve.addX_eq_thirdChordX_diag` — **the coordinate identity `addX = X₃`**: Mathlib's
  affine doubling `addX` of the recovered point equals the transported third-root `x`-coordinate
  `X₃ = t / w₃` (in the case `X₃ ≠ x`).
* `WeierstrassCurve.localParam_add_diag` — **the coordinate-level doubling additivity**:
  `-addX / addY = z ⊕ z` in `K`, where `z ⊕ z = adicEvalMv 𝔪 ![z, z] formalGroupZW` is the formal
  group law of the parameter.
* `WeierstrassCurve.localParam_add_of_X_eq` — the point-level doubling: for a point `P` reducing to
  the origin with `2P ≠ O` (`y ≠ negY x y`) and `P + P` also reducing to the origin,
  `z(P + P) = z(P) ⊕ z(P)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries Polynomial

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z : R}

end WeierstrassCurve
