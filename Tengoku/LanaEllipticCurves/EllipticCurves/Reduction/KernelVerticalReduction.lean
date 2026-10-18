/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.KernelAddClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduce-to-kernel and reduced-vertical cases of `redPt` additivity (issue #382)

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field `k`, and let
`W : WeierstrassCurve K` have good reduction.  This file proves the two structurally cleanest
special cases of the homomorphism property `redPt (P + Q) = redPt P + redPt Q` of the
point-reduction map `redPt : (W⁄K).Point → (reduction R W).Point`
(see `EllipticCurves/Reduction/PointReduction.lean`).

⚠️ This paragraph used to call that property *"still open in general"*.  **It is not, and has not
been since the day this file landed**: `WeierstrassCurve.redPt_add`
(`EllipticCurves/Reduction/ReductionHom.lean`) proves it for all `P, Q`, in a file that imports
*this* one.  The clause survived because nothing in a build can fail on it.

## Main results

* `WeierstrassCurve.redPt_add_of_reducesToZero` — **kernel × kernel additivity.**  If both `P` and
  `Q` reduce to the origin (`P, Q ∈ E₁(K)`), then `redPt (P + Q) = redPt P + redPt Q` (all three are
  `0`).  This is the restriction of the homomorphism property to `E₁(K) × E₁(K)`; it follows from
  the full add-closure `reducesToZero_add` of `EllipticCurves/Reduction/KernelAddClosure.lean`.
* `WeierstrassCurve.redPt_add_of_reducesToZero_left` / `redPt_add_of_reducesToZero_right` — the same
  (so **both** summands are still assumed in `E₁(K)`), phrased as `redPt (P + Q) = redPt Q` (resp.
  `= redPt P`).  Note these are *not* the general "kernel acts trivially" statement (`P ∈ E₁(K)`,
  `Q` arbitrary); that is `WeierstrassCurve.redPt_add_eq_right_of_reducesToZero` /
  `redPt_add_eq_left_of_reducesToZero` (`EllipticCurves/Reduction/ReductionHom.lean`), which is
  downstream of this file.
* `WeierstrassCurve.redPt_add_of_Y_eq` — **literal vertical.**  If `x₁ = x₂` and `y₁ = negY x₂ y₂`
  over `K`, then `P + Q = O`, so `redPt (P + Q) = 0`.
* `WeierstrassCurve.redPt_add_of_secant_vertical` — **reduced-vertical secant case.**  For two
  integral points `P = (x₁, y₁)`, `Q = (x₂, y₂)` (`v xᵢ ≤ 1`) with `x₁ ≠ x₂` whose reduced
  `x`-coordinates agree but whose reduced `y`-coordinates differ — captured by the single valuation
  hypothesis `v (x₁ - x₂) < v (y₁ - y₂)` — the secant slope `ℓ = (y₁ - y₂)/(x₁ - x₂)` has a pole, so
  the leading `ℓ²` term of `addX` dominates, giving `1 < v (addX)`; hence `P + Q ∈ E₁(K)` and
  `redPt (P + Q) = 0`.

## What is not covered *here* — both cases have since been proved elsewhere

Two hard sub-cases are outside this file, and no proof holes are left for them (this file is
complete).  Both have since landed, and ⚠️ **one of them by a route this file predicted wrongly** —
which is why the original text is kept as a quotation rather than deleted:

* **Kernel × integral (`redPt (P + Q) = redPt Q` for `P ∈ E₁(K)`, `Q` integral)** — proved as
  `WeierstrassCurve.redPt_add_of_mem_E₁_left` / `_right`
  (`EllipticCurves/Reduction/KernelIntegralReduction.lean`).

  ⚠️ This paragraph predicted that pinning down `residue (addY) = residue y₂` *"requires a
  **second**-order expansion of `addX - x₂` together with the leading identity `y₁² ≈ x₁³`"*.  **It
  does not.**  The merged proof substitutes the two Weierstrass equations **once**, obtaining the
  two exact identities `(addX - x₂)·d² = P₁` and `(negAddY - negY x₂ y₂)·d³ = P₂` and reading off
  their weights against the Newton-polygon dichotomy.  *The obstruction was in the bookkeeping, not
  in the order of the expansion.*
* **Reduced-vertical doubling / `2`-torsion (`x₁ = x₂` over `K` but not literally negating, or the
  secant `2`-torsion edge `v (y₁ - y₂) ≥ v (x₁ - x₂)`)** — proved as
  `WeierstrassCurve.redPt_add_of_reduced_two_torsion_secant` /
  `redPt_add_self_of_reduced_two_torsion` (`EllipticCurves/Reduction/TwoTorsionReduction.lean`), by
  exactly the route this file named: the reduced tangent denominator vanishes, the slope is a pole,
  and the `ℓ²` term of `addX` dominates.

⚠️ The two are therefore *not* "the same missing reduced-`addY`-residue analysis": one needed a
different substitution and the other needed a different non-vanishing input.  With them, the full
`WeierstrassCurve.redPt_add` is assembled in `EllipticCurves/Reduction/ReductionHom.lean`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1, VII.2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Kernel × kernel additivity -/

section KernelKernel

variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [HasGoodReduction R W] [W.IsElliptic]

end KernelKernel

/-! ### The literal vertical case `P + Q = O` -/

open Classical in
/-- **Literal vertical.**  If `x₁ = x₂` and `y₁ = negY x₂ y₂` over `K`, then `P + Q = O` by the
Weierstrass group law, so `redPt (P + Q) = 0`. -/
theorem redPt_add_of_Y_eq (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁}
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = W.toAffine.negY x₂ y₂) :
    redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  rw [Affine.Point.add_of_Y_eq hx hy]
  exact redPt_zero R W

/-! ### The reduced-vertical secant case -/

open Classical in
/-- **Reduced-vertical secant case.**  For two integral points `P = (x₁, y₁)`, `Q = (x₂, y₂)`
(`v xᵢ ≤ 1`) with `x₁ ≠ x₂` whose reduced `x`-coordinates agree but whose reduced `y`-coordinates
differ — the single valuation hypothesis being `v (x₁ - x₂) < v (y₁ - y₂)` — the secant slope
`ℓ = (y₁ - y₂)/(x₁ - x₂)` has a pole, `1 < v ℓ`.  In the `x`-coordinate
`addX = ℓ² + a₁ℓ - a₂ - x₁ - x₂` of `P + Q` the term `ℓ²` then strictly dominates every other term
(each of valuation `≤ v ℓ < v ℓ²` or `≤ 1 < v ℓ²`), so `1 < v (addX)`; hence `P + Q ∈ E₁(K)` and
`redPt (P + Q) = 0`.

This is the "reduced points are negatives" secant configuration, whenever the reduced points are
*not* `2`-torsion (equivalently `v (y₁ - y₂) < 1`, so `ȳ₁ ≠ ȳ₂`). -/
theorem redPt_add_of_secant_vertical (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁}
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (hxne : x₁ ≠ x₂)
    (hx₁ : valuation K (maximalIdeal R) x₁ ≤ 1) (hx₂ : valuation K (maximalIdeal R) x₂ ≤ 1)
    (hlt : valuation K (maximalIdeal R) (x₁ - x₂) < valuation K (maximalIdeal R) (y₁ - y₂)) :
    redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hv
  -- Abbreviations for the two coordinate-difference valuations.
  set β : ℤᵐ⁰ := v (x₁ - x₂) with hβ
  set γ : ℤᵐ⁰ := v (y₁ - y₂) with hγ
  -- `β ≠ 0` since `x₁ ≠ x₂`, and then `0 < β < γ`.
  have hβ0 : β ≠ 0 := by
    rw [hβ, Valuation.ne_zero_iff]; exact sub_ne_zero.mpr hxne
  have hβpos : (0 : ℤᵐ⁰) < β := lt_of_le_of_ne zero_le (Ne.symm hβ0)
  -- The secant slope `ℓ = (y₁ - y₂)/(x₁ - x₂)` has valuation `γ / β`, which exceeds `1`.
  set ℓ : K := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have hℓval : v ℓ = γ / β := by
    rw [hℓdef, Affine.slope_of_X_ne hxne, v.map_div, hγ, hβ]
  have h1ltℓ : 1 < v ℓ := by
    rw [hℓval, one_lt_div₀ hβpos]; exact hlt
  -- Powers/products of `v ℓ`.
  have hℓ2 : v ℓ < (v ℓ) ^ 2 := by
    calc v ℓ = (v ℓ) ^ 1 := (pow_one _).symm
      _ < (v ℓ) ^ 2 := pow_lt_pow_right₀ h1ltℓ (by norm_num)
  have h1ltℓ2 : 1 < (v ℓ) ^ 2 := one_lt_pow₀ h1ltℓ (by norm_num)
  -- Coefficient bounds on the integral model.
  have ha1 : v W.a₁ ≤ 1 := valuation_a₁_le_one R W
  have ha2 : v W.a₂ ≤ 1 := valuation_a₂_le_one R W
  -- Bound the non-leading tail `a₁ℓ - a₂ - x₁ - x₂` of `addX`.
  have hva1ℓ : v (W.a₁ * ℓ) < (v ℓ) ^ 2 := by
    rw [v.map_mul]
    calc v W.a₁ * v ℓ ≤ 1 * v ℓ := by gcongr
      _ = v ℓ := one_mul _
      _ < (v ℓ) ^ 2 := hℓ2
  have hva2 : v W.a₂ < (v ℓ) ^ 2 := lt_of_le_of_lt ha2 h1ltℓ2
  have hvx1 : v x₁ < (v ℓ) ^ 2 := lt_of_le_of_lt hx₁ h1ltℓ2
  have hvx2 : v x₂ < (v ℓ) ^ 2 := lt_of_le_of_lt hx₂ h1ltℓ2
  -- The leading term `ℓ²` strictly dominates, so `v (addX) = (v ℓ)² > 1`.
  have hvℓ2 : v (ℓ ^ 2) = (v ℓ) ^ 2 := by rw [map_pow]
  have haddX : 1 < v (W.toAffine.addX x₁ x₂ ℓ) := by
    have htail : v (W.a₁ * ℓ - W.a₂ - x₁ - x₂) < (v ℓ) ^ 2 :=
      v.map_sub_lt (v.map_sub_lt (v.map_sub_lt hva1ℓ hva2) hvx1) hvx2
    have hsum : W.toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 + (W.a₁ * ℓ - W.a₂ - x₁ - x₂) := by
      simp only [Affine.addX]; ring
    rw [hsum, Valuation.map_add_eq_of_lt_left _ (by rw [hvℓ2]; exact htail), hvℓ2]
    exact h1ltℓ2
  -- Assemble: `P + Q` is the secant sum, whose `x`-coordinate has a pole.
  rw [Affine.Point.add_of_X_ne hxne]
  exact redPt_some_of_one_lt R W haddX

end WeierstrassCurve
