/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.GoodReductionBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Good reduction makes the curve elliptic and its `j`-invariant integral (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` have good reduction over `R` (`HasGoodReduction R W`). This file records
two elementary but foundational consequences that open the `j`-invariant / reduction-type theory
of an elliptic curve — the first bricks toward the **potential good reduction** criterion
(Silverman AEC VII.5): a curve with good reduction is elliptic, and its `j`-invariant is *integral*,
i.e. `j ∈ R`
(equivalently `v(j) ≥ 0`).

## Key point

`HasGoodReduction R W` unfolds to `IsMinimal R W` together with
`valuation K (maximalIdeal R) W.Δ = 1`, i.e. the discriminant of the integral minimal model
`integralModel R W` is a **unit** in `R` (this is `isUnit_Δ_integralModel_of_hasGoodReduction`, from
`GoodReductionBaseChange.lean`). A ring homomorphism sends units to units, so `W.Δ` is a unit in the
field `K` and `W` is elliptic. Moreover, writing `j = Δ'⁻¹ · c₄³`, both `Δ` and `c₄` come from the
integral model, so `j` is the image of `↑u⁻¹ · c₄³ ∈ R` under `algebraMap R K` (`u` the unit
discriminant of the integral model). This is the easy `⇐`-adjacent half of the classical statement
that a curve has good reduction only if its `j`-invariant is integral; the converse (integral `j`
implies *potential* good reduction, VII.5.5) needs base-change / valuation-extension infrastructure
and is left to a follow-on.

## Main results

* `WeierstrassCurve.isElliptic_of_hasGoodReduction` — good reduction implies `W.IsElliptic`.
* `WeierstrassCurve.isIntegral_j_of_hasGoodReduction` — the `j`-invariant of a curve with good
  reduction is integral: `∃ r : R, algebraMap R K r = W.j` (i.e. `v(j) ≥ 0`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

variable (R) in
/-- A Weierstrass curve with good reduction over a discrete valuation ring `R` is elliptic: its
discriminant `Δ` is a unit in the fraction field `K`, because the discriminant of its integral
minimal model is a unit in `R`. -/
theorem isElliptic_of_hasGoodReduction (W : WeierstrassCurve K) [HasGoodReduction R W] :
    W.IsElliptic := by
  refine ⟨?_⟩
  have h := (isUnit_Δ_integralModel_of_hasGoodReduction R W).map (algebraMap R K)
  rwa [integralModel_Δ_eq R W] at h

variable (R) in
/-- **The `j`-invariant of a curve with good reduction is integral** (`v(j) ≥ 0`): there is `r : R`
with `algebraMap R K r = W.j`. Since `j = Δ'⁻¹ · c₄³` and both the discriminant (a unit `u : Rˣ`)
and `c₄` of the integral minimal model lie in `R`, the witness is `↑u⁻¹ · c₄³ ∈ R`. -/
theorem isIntegral_j_of_hasGoodReduction (W : WeierstrassCurve K)
    [HasGoodReduction R W] [W.IsElliptic] :
    ∃ r : R, algebraMap R K r = W.j := by
  obtain ⟨u, hu⟩ := isUnit_Δ_integralModel_of_hasGoodReduction R W
  refine ⟨↑u⁻¹ * (integralModel R W).c₄ ^ 3, ?_⟩
  rw [map_mul, map_pow, integralModel_c₄_eq R W, map_units_inv, hu, integralModel_Δ_eq R W]
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ']

end WeierstrassCurve
