/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.TangentAdditivityClean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Doubling closure of the reduction kernel `E₁(K)` (issue #367, partial)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  Working towards the fact that
the reduction kernel `E₁(K) = {P // ReducesToZero R W P}` is closed under addition (issue #367),
this file discharges the **non-degenerate doubling case**: for `P = (x, y) ∈ E₁(K)` with
`2P ≠ O` (`y ≠ negY x y`, the tangent/doubling case) and honestly-geometric distinctness
`X₃ ≠ x`, the affine double `P + P` again reduces to the origin.

This is the doubling analog of the merged secant closure
`reducesToZero_add_of_X_ne_of_distinct` (`Reduction/SecantClosure.lean`).  The merged doubling
additivity `localParam_add_of_X_eq_clean` (`Reduction/TangentAdditivityClean.lean`) takes
`ReducesToZero R W (P + P)` as a *hypothesis* (`hred`); here we **prove** that hypothesis in the
doubling case, so the additivity identity holds without assuming closure a priori.

## The closure argument

Mathlib's affine double in the tangent case is `P + P = some (addX x x ℓ) (addY …)`
(`add_self_of_Y_ne`), so `ReducesToZero R W (P + P)` unfolds to `1 < v(addX x x ℓ)`.  Now, exactly
as in the secant case but with the diagonal (`z₁ = z₂ = z`) bricks:

* `addX x x ℓ = X₃` — Mathlib's affine third-intersection `x`-coordinate is the transported Vieta
  third tangent point (`addX_eq_thirdChordX_diag`, needing the distinctness `X₃ ≠ x`, together with
  the unconditional doubling side conditions `w₃ ≠ 0`, `ν ≠ 0`);
* `X₃ = t / w₃ = t / wParam t = xParam t` where `t = thirdRootNum` — the third chord `w`-value is
  the coordinate expansion `wParam t` (`thirdChordW_eq_wParam_diag`);
* `1 < v(xParam t)` for `t ≠ 0` (`one_lt_valuation_xParam`, with `t ≠ 0` from
  `thirdRootNum_ne_zero_diag`), i.e. the recovered third tangent point has a pole.

Hence `1 < v(addX)`, so `P + P ∈ E₁(K)`.  **No new analytic machinery is needed** — the valuation
control comes entirely from the merged coordinate-recovery bricks; in particular the closure does
*not* pass through the cancellation-sensitive direct slope-valuation route (Silverman AEC VII.2).

## Main results

* `WeierstrassCurve.reducesToZero_add_of_X_eq_of_distinct` — `P = (x, y) ∈ E₁(K)`, `2P ≠ O`,
  `X₃ ≠ x` ⇒ `P + P ∈ E₁(K)` (the doubling add-closure).
* `WeierstrassCurve.localParam_add_doubling_of_distinct` — the doubling additivity of the local
  parameter `localParam (P + P) = z(P) ⊕ z(P)` **without** the `hred` hypothesis, obtained by
  feeding the closure lemma into `localParam_add_of_X_eq_clean`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W]

end WeierstrassCurve
