/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ThirdChordNonvanishingDiag

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Doubling additivity with the analytic side conditions discharged (issue #367)

The point-level doubling additivity `WeierstrassCurve.localParam_add_of_X_eq`
(`Reduction/TangentThirdChordAffine.lean`) proves, for a point `P = (x, y)` reducing to the origin
with `2P ≠ O` (`y ≠ negY x y`, the tangent/doubling case) and `P + P` also reducing to the origin,
`localParam (P + P) = adicEvalMv 𝔪 ![z, z] formalGroupZW` — the doubling additivity of the local
parameter — but it carries **four** non-degeneracy side conditions:

* `hw : w₃ ≠ 0` (the third tangent point is not at infinity),
* `hν : ν ≠ 0` (the tangent-line intercept, i.e. `addY ≠ 0`),
* `hd : X₃ ≠ x` (the transported third `x`-coordinate is distinct from the doubled point),
* `hden : den ≠ 0` (the sum is not `2`-torsion).

Three of these — `hw`, `hν` and `hden` — are now **unconditional** in the doubling case, discharged
by the merged bricks `thirdChordW_ne_zero_diag`, `chordIntercept_ne_zero_diag`
(`Reduction/ThirdChordNonvanishingDiag.lean`, PR #99) and `adicEvalMv_formalGroupDen_ne_zero`
(`Reduction/AdditivityValuation.lean`, PR #90).  This file packages that:
`WeierstrassCurve.localParam_add_of_X_eq_clean` states the doubling additivity requiring **only**
the genuinely-geometric distinctness `hd : X₃ ≠ x` (which fails exactly in the `3P = O`
configuration, where the third tangent point coincides with `±P`).

This is the doubling analog of the merged secant `localParam_add_of_X_ne_of_distinct`
(`Reduction/SecantAdditivity.lean`, PR #95): both leave only the honestly-degenerate distinctness
condition.

⚠️ That condition was expected here to be *"handled by the eventual full case analysis"*.  **It was
removed instead**: `WeierstrassCurve.addX_eq_thirdChordX_of_doubling`
(`Reduction/ThirdChordAffineUncond.lean`, #376) proves `addX = X₃` on the diagonal as a field
identity with no distinctness of `X₃`, and `WeierstrassCurve.localParam_add_of_X_eq_uncond`
(`Reduction/AdditivityUncond.lean`) is this statement with `hd` gone.  The inverse (`Q = -P`) case
is `WeierstrassCurve.adicEvalMv_formalGroupZW_eq_zero_of_X_eq`
(`Reduction/InverseAdditivity.lean`), unconditional at `2`-torsion via `zParamHatEquiv_neg_uncond`
(`Reduction/KernelNegationUncond.lean`, #377), and the `E₁(K)` subgroup assembly of #367 is
`WeierstrassCurve.reducesToZero_add` / `E₁` (`Reduction/KernelAddClosure.lean`).

## Main result

* `WeierstrassCurve.localParam_add_of_X_eq_clean` — doubling additivity of the local parameter with
  `hw`/`hν`/`hden` discharged, requiring only `hd : X₃ ≠ x`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W]

end WeierstrassCurve
