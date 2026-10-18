/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantGoodReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `j`-invariant commutes with good reduction (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` have good reduction over `R` (`HasGoodReduction R W`). The good-reduction
brick `isIntegral_j_of_hasGoodReduction` (`JInvariantGoodReduction.lean`, #483) shows that `W.j` is
*integral*, i.e. it is the image `algebraMap R K r` of some `r : R`. This file pins that witness
down canonically and records the compatibility of the `j`-invariant with the reduction map: the
`j`-invariant of the reduced curve `W.reduction R` (a curve over the residue field `ResidueField R`)
is the **reduction of the `j`-invariant** of the minimal integral model.

## Key point

Under good reduction the integral minimal model `integralModel R W` has a **unit** discriminant
(`isUnit_Δ_integralModel_of_hasGoodReduction`), so it is itself an elliptic curve over `R` and its
`j`-invariant `(integralModel R W).j : R` is defined. Two applications of Mathlib's `map_j`
(functoriality of `j` under a ring map of elliptic curves) then give the two faces of the same
element `(integralModel R W).j ∈ R`:

* pushing along `algebraMap R K` recovers `W.j` (because `(integralModel R W)⁄K = W`), and
* pushing along the residue map `residue R` gives `(W.reduction R).j` (because
  `W.reduction R = (integralModel R W).map (residue R)`).

Together these say the square `R → K`, `R → ResidueField R`, `j ↦ j` commutes: *the `j`-invariant
of the good reduction is the reduction of the `j`-invariant*. This is the natural refinement of
`isIntegral_j_of_hasGoodReduction` and a foundational compatibility for the reduction theory of the
`j`-invariant (Silverman AEC VII.5).

## Main results

* `WeierstrassCurve.isElliptic_integralModel_of_hasGoodReduction` — the integral minimal model of a
  curve with good reduction is elliptic (its discriminant is a unit in `R`).
* `WeierstrassCurve.algebraMap_j_integralModel_eq` — the canonical integral witness for `W.j`:
  `algebraMap R K (integralModel R W).j = W.j` (a sharpening of `isIntegral_j_of_hasGoodReduction`).
* `WeierstrassCurve.reduction_j_eq` — the `j`-invariant of the reduction is the residue of the
  integral model's `j`-invariant: `(W.reduction R).j = residue R (integralModel R W).j`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- The integral minimal model of a curve with good reduction is itself elliptic: its discriminant
is a unit in `R` (`isUnit_Δ_integralModel_of_hasGoodReduction`). -/
instance isElliptic_integralModel_of_hasGoodReduction (W : WeierstrassCurve K)
    [HasGoodReduction R W] : (integralModel R W).IsElliptic :=
  ⟨isUnit_Δ_integralModel_of_hasGoodReduction R W⟩

/-- The reduction of a curve with good reduction is elliptic
(`hasGoodReduction_iff_isElliptic_reduction`). -/
instance isElliptic_reduction_of_hasGoodReduction (W : WeierstrassCurve K)
    [HasGoodReduction R W] : (W.reduction R).IsElliptic :=
  (hasGoodReduction_iff_isElliptic_reduction R).mp ‹_›

variable (R) in
/-- **The canonical integral witness for the `j`-invariant of a good-reduction curve.** Since
`(integralModel R W)⁄K = W` and the integral model is elliptic, `map_j` gives
`algebraMap R K (integralModel R W).j = W.j`; this sharpens `isIntegral_j_of_hasGoodReduction` by
naming the witness `(integralModel R W).j`. -/
theorem algebraMap_j_integralModel_eq (W : WeierstrassCurve K) [HasGoodReduction R W]
    [W.IsElliptic] :
    algebraMap R K (integralModel R W).j = W.j := by
  have hb : (integralModel R W).map (algebraMap R K) = W := baseChange_integralModel_eq R W
  have h := map_j (W := integralModel R W) (algebraMap R K)
  rw [← h]
  simp_rw [hb]

variable (R) in
/-- **The `j`-invariant commutes with good reduction.** The reduced curve `W.reduction R` (over the
residue field `ResidueField R`) has `j`-invariant equal to the reduction of the integral model's
`j`-invariant: `(W.reduction R).j = residue R (integralModel R W).j`. Both sides are images of the
single element `(integralModel R W).j : R` — see also `algebraMap_j_integralModel_eq` for its image
in `K`. -/
theorem reduction_j_eq (W : WeierstrassCurve K) [HasGoodReduction R W] :
    (W.reduction R).j = residue R (integralModel R W).j :=
  map_j (W := integralModel R W) (residue R)

end WeierstrassCurve
