/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.SlopeReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `redPt` additivity on the good-secant locus (issue #380)

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field
`k = ResidueField R`, and let `W : WeierstrassCurve K` have good reduction.  This file proves the
**secant case** of the point-reduction homomorphism property (parent #360):
```
redPt R W (P + Q) = redPt R W P + redPt R W Q
```
whenever `P = (x₁, y₁)` and `Q = (x₂, y₂)` are integral points whose reductions have **distinct
`x`-coordinates** (`residue x̄₁ ≠ residue x̄₂`).  In that configuration `P + Q` is computed by the
secant addition formula, and — crucially — the difference of the reduced `x`-coordinates is a unit,
so the `K`-slope is *integral* and its residue is the slope on the reduced curve
(`exists_lift_slope_of_reduced_X_ne`, issue #379).

The proof is a pure assembly of the ring-hom-commuting coordinate formulas
`WeierstrassCurve.Affine.map_addX` / `map_addY` (which hold for *any* ring homomorphism, no
injectivity required) applied to both `algebraMap R K` (to lift the sum's coordinates to `R`) and
`residue R` (to identify their residues with the reduced-curve `addX`/`addY`).  It mirrors the
structure of `redPt_neg` (`PointReduction.lean`).

## Main results

* `WeierstrassCurve.redPt_add_of_reduced_X_ne` — the secant case of `redPt`-additivity.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2 Prop 2.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open Classical in
/-- **`redPt` additivity, good-secant case.**  For integral points `P = (x₁, y₁)`, `Q = (x₂, y₂)`
of `W` whose reductions have distinct `x`-coordinates (`residue x₀₁ ≠ residue x₀₂`), the reduction
of the secant sum is the sum of the reductions:
`redPt (P + Q) = redPt P + redPt Q`.

Because `residue x₀₁ ≠ residue x₀₂`, the difference `x₀₁ - x₀₂` is a unit, so the secant `K`-slope
is integral with residue the reduced-curve slope (`exists_lift_slope_of_reduced_X_ne`, #379).
Lifting through `algebraMap R K` and reducing through `residue R` the same integral-model
`addX`/`addY` polynomials — both of which commute with any ring homomorphism
(`Affine.map_addX`/`map_addY`) — identifies the reduced coordinates of `P + Q` with the coordinates
of `redPt P + redPt Q`. -/
theorem redPt_add_of_reduced_X_ne (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ x₂ y₂ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    {x₀₁ y₀₁ x₀₂ y₀₂ : R}
    (hx₁ : algebraMap R K x₀₁ = x₁) (hy₁ : algebraMap R K y₀₁ = y₁)
    (hx₂ : algebraMap R K x₀₂ = x₂) (hy₂ : algebraMap R K y₀₂ = y₂)
    (hne : residue R x₀₁ ≠ residue R x₀₂) :
    redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redPt R W (.some x₁ y₁ h₁) + redPt R W (.some x₂ y₂ h₂) := by
  -- the `x`-coordinates differ over `K` (else their lifts, hence residues, would coincide).
  have hx12 : x₁ ≠ x₂ := fun h =>
    hne (congrArg (residue R) (IsFractionRing.injective R K (hx₁.trans (h.trans hx₂.symm))))
  haveI : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  -- the integral model base-changes to `W`; used to lift `addX`/`addY` from `R` to `K`.
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  -- integral lift `s : R` of the secant slope, with residue the reduced-curve slope (#379).
  obtain ⟨s, hs, hs_res⟩ :=
    exists_lift_slope_of_reduced_X_ne R W hx₁ hy₁ hx₂ hy₂ hne
  -- nonsingularity of the reduced coordinates of `P` and `Q` (Equation transfers K → R → k).
  have hEqP : (integralModel R W).toAffine.Equation x₀₁ y₀₁ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine)
      (IsFractionRing.injective R K) x₀₁ y₀₁, hx₁, hy₁, hcurve]; exact h₁.1
  have hEqQ : (integralModel R W).toAffine.Equation x₀₂ y₀₂ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine)
      (IsFractionRing.injective R K) x₀₂ y₀₂, hx₂, hy₂, hcurve]; exact h₂.1
  have hnsP : (reduction R W).toAffine.Nonsingular (residue R x₀₁) (residue R y₀₁) :=
    (Affine.equation_iff_nonsingular).mp (hEqP.map (residue R))
  have hnsQ : (reduction R W).toAffine.Nonsingular (residue R x₀₂) (residue R y₀₂) :=
    (Affine.equation_iff_nonsingular).mp (hEqQ.map (residue R))
  -- lifts through `algebraMap R K`: the integral-model `addX`/`addY` of the lifts + `s` project to
  -- the `K`-side `addX`/`addY` of `x₁,x₂,y₁` at the secant slope.
  have haddX : algebraMap R K ((integralModel R W).toAffine.addX x₀₁ x₀₂ s)
      = W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [← Affine.map_addX (algebraMap R K), hcurve, hx₁, hx₂, hs]
  have haddY : algebraMap R K ((integralModel R W).toAffine.addY x₀₁ x₀₂ y₀₁ s)
      = W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [← Affine.map_addY (algebraMap R K), hcurve, hx₁, hx₂, hy₁, hs]
  -- residues through `residue R`: the same integral-model `addX`/`addY` project to the *reduced*
  -- curve's `addX`/`addY` at the residue `residue R s` of the slope lift (`hs_res` identifies that
  -- residue with the reduced-curve slope).  `map_addX`/`map_addY` supply these for the ring hom
  -- `residue R`; `reduction R W` is `(integralModel R W).map (residue R)` by definition, so the
  -- ascription is accepted by a cheap defeq (note `map_addY`'s argument order is `x₁ y₁ x₂ ℓ`).
  have hredX : residue R ((integralModel R W).toAffine.addX x₀₁ x₀₂ s)
      = (reduction R W).toAffine.addX (residue R x₀₁) (residue R x₀₂) (residue R s) :=
    (Affine.map_addX (residue R) x₀₁ x₀₂ s).symm
  have hredY : residue R ((integralModel R W).toAffine.addY x₀₁ x₀₂ y₀₁ s)
      = (reduction R W).toAffine.addY (residue R x₀₁) (residue R x₀₂) (residue R y₀₁)
          (residue R s) :=
    (Affine.map_addY (residue R) x₀₁ y₀₁ x₀₂ s).symm
  -- nonsingularity of the reduced sum's coordinates, matched to the residues of the integral lifts.
  have hns_sum : (reduction R W).toAffine.Nonsingular
      (residue R ((integralModel R W).toAffine.addX x₀₁ x₀₂ s))
      (residue R ((integralModel R W).toAffine.addY x₀₁ x₀₂ y₀₁ s)) := by
    rw [hredX, hredY, hs_res]
    exact Affine.nonsingular_add hnsP hnsQ (fun hxy => hne hxy.left)
  -- compute both sides: `add_of_X_ne` opens the secant addition (over `K` on the left, over `k`
  -- on the right, using `hx12` / `hne`), `redPt_some_eq` reduces each integral point to the
  -- residues of its lifts, and the coordinates then match via `hredX`/`hredY`
  -- (`map_addX`/`map_addY`) and `hs_res` (`residue R s = reduced slope`).
  rw [Affine.Point.add_of_X_ne hx12, redPt_some_eq R W haddX haddY hns_sum,
    redPt_some_eq R W hx₁ hy₁ hnsP, redPt_some_eq R W hx₂ hy₂ hnsQ,
    Affine.Point.add_of_X_ne hne]
  simp only [hredX, hredY, hs_res]

end WeierstrassCurve
