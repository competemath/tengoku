/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.PointReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral-slope reduction compatibility on the good-secant locus (issue #379)

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field
`k = ResidueField R`, and let `W : WeierstrassCurve K` have good reduction.  This file supplies the
**foundational slope lemma** for the point-reduction homomorphism (`redPt` additivity, parent #360):
on the *good-secant* locus — two integral points whose reductions have **distinct `x`-coordinates**
— the secant slope over `K` is integral and its residue equals the slope on the reduced curve.

## Why this is the crux to isolate

Mathlib's functorial `WeierstrassCurve.Affine.map_slope` (`Affine/Formula.lean`) requires the ring
homomorphism to be **injective**; the reduction map `residue R : R → k` is not injective, so the
general lemma does not apply.  The obstruction is genuine only where reduction collapses distinct
`K`-points.  On the good-secant locus, however, the slope is the difference quotient
`(y₁ - y₂) / (x₁ - x₂)` (`Affine.slope_of_X_ne`), and its denominator `x₀₁ - x₀₂` is a **unit** of
the local ring `R` (its residue is nonzero), so the quotient is integral and `residue R` — a genuine
ring homomorphism — commutes with it directly.  No injectivity is needed.  This makes the secant
case elementary and self-contained; it is the piece the secant `redPt`-additivity rung consumes.

## Main results

* `WeierstrassCurve.exists_lift_slope_of_reduced_X_ne` — an integral lift `s : R` of the `K`-secant
  slope whose residue is the reduced-curve slope.
* `WeierstrassCurve.valuation_slope_le_one_of_reduced_X_ne` — the secant slope is integral
  (`v (slope) ≤ 1`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2 Prop 2.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open Classical in
/-- **Integral-slope reduction compatibility (good-secant case).**  Let `P = (x₁, y₁)` and
`Q = (x₂, y₂)` be points of `W` with integral lifts `x₀ᵢ, y₀ᵢ : R` of their coordinates, and suppose
their reductions have distinct `x`-coordinates (`residue x₀₁ ≠ residue x₀₂`).  Then the secant slope
`W.slope x₁ x₂ y₁ y₂ = (y₁ - y₂)/(x₁ - x₂)` is **integral**: it has a lift `s : R` whose residue is
exactly the slope of the reduced curve at the reduced points.

This is the residue-side slope compatibility the secant reduction-additivity rung consumes; because
`x₀₁ - x₀₂` is a unit of the local ring `R`, the difference quotient stays in `R` and the ring
homomorphism `residue R` commutes with it — no injectivity of `residue R` is required. -/
theorem exists_lift_slope_of_reduced_X_ne (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ x₂ y₁ y₂ : K} {x₀₁ y₀₁ x₀₂ y₀₂ : R}
    (hx₁ : algebraMap R K x₀₁ = x₁) (hy₁ : algebraMap R K y₀₁ = y₁)
    (hx₂ : algebraMap R K x₀₂ = x₂) (hy₂ : algebraMap R K y₀₂ = y₂)
    (hne : residue R x₀₁ ≠ residue R x₀₂) :
    ∃ s : R, algebraMap R K s = W.toAffine.slope x₁ x₂ y₁ y₂ ∧
      residue R s = (reduction R W).toAffine.slope
        (residue R x₀₁) (residue R x₀₂) (residue R y₀₁) (residue R y₀₂) := by
  -- `x₀₁ - x₀₂` is a unit of the local ring `R`: its residue is nonzero.
  have hb : IsUnit (x₀₁ - x₀₂) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hne
  obtain ⟨u, hu⟩ := hb
  -- the coordinates differ over `K` (else their integral lifts, hence residues, would agree).
  have hx12 : x₁ ≠ x₂ := by
    intro h
    exact hne (congrArg (residue R) (IsFractionRing.injective R K (hx₁.trans (h.trans hx₂.symm))))
  -- `↑u = x₀₁ - x₀₂` lifts `x₁ - x₂` (over `K`) and `residue x₀₁ - residue x₀₂` (over `k`).
  have hunit : algebraMap R K (u : R) = x₁ - x₂ := by rw [hu, map_sub, hx₁, hx₂]
  have hunit_res : residue R (u : R) = residue R x₀₁ - residue R x₀₂ := by rw [hu, map_sub]
  refine ⟨(y₀₁ - y₀₂) * (u⁻¹ : Rˣ), ?_, ?_⟩
  · -- over `K`: the difference quotient equals the secant slope.
    rw [Affine.slope_of_X_ne hx12, eq_div_iff (sub_ne_zero.mpr hx12), ← hunit, ← map_mul,
      mul_assoc, Units.inv_mul, mul_one, map_sub, hy₁, hy₂]
  · -- over `k`: the same computation with `residue R`, giving the reduced-curve slope.
    rw [Affine.slope_of_X_ne hne, eq_div_iff (sub_ne_zero.mpr hne), ← hunit_res, ← map_mul,
      mul_assoc, Units.inv_mul, mul_one, map_sub]

open Classical in
/-- On the good-secant locus the secant slope is **integral** (`v (slope) ≤ 1`), a corollary of the
integral lift `exists_lift_slope_of_reduced_X_ne`. -/
theorem valuation_slope_le_one_of_reduced_X_ne (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ x₂ y₁ y₂ : K} {x₀₁ y₀₁ x₀₂ y₀₂ : R}
    (hx₁ : algebraMap R K x₀₁ = x₁) (hy₁ : algebraMap R K y₀₁ = y₁)
    (hx₂ : algebraMap R K x₀₂ = x₂) (hy₂ : algebraMap R K y₀₂ = y₂)
    (hne : residue R x₀₁ ≠ residue R x₀₂) :
    valuation K (maximalIdeal R) (W.toAffine.slope x₁ x₂ y₁ y₂) ≤ 1 := by
  obtain ⟨s, hs, -⟩ :=
    exists_lift_slope_of_reduced_X_ne R W hx₁ hy₁ hx₂ hy₂ hne
  exact hs ▸ valuation_le_one (maximalIdeal R) s

end WeierstrassCurve
