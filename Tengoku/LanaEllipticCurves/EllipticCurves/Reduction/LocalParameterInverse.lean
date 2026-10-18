/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.LocalParameter
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.CoordinateSeries
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.AdicEval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The inverse of the local parameter: the coordinate expansion `z ↦ (x(z), y(z))`

Let `R` be a **complete** discrete valuation ring (`IsAdicComplete (maximalIdeal R).asIdeal R`) with
fraction field `K = Frac R`, and let `W : WeierstrassCurve K` have an integral model
(`IsIntegral R W`).  The sibling file `Reduction/LocalParameter.lean` builds the local parameter
`z(P) = -x(P)/y(P) : E₁(K) → 𝔪`.  This file supplies the **inverse direction** at the level of
coordinates: given a parameter `z ∈ 𝔪`, the Weierstrass coordinate expansion recovers a point of the
curve.

Following Silverman (AEC VII.2, IV.1) the parametrisation near the origin is `x = z/w`, `y = -1/w`,
where `w = w(z)` is the fixed point of the Weierstrass functional equation
`w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`.  Over a complete DVR this fixed point is obtained by
evaluating the formal solution `W.formalW ∈ R⟦X⟧` (`EllipticCurves/FormalGroup/Expansion.lean`) at
`z ∈ 𝔪` through the `I`-adic evaluation ring homomorphism `PowerSeries.adicEval`
(`EllipticCurves/FormalGroup/AdicEval.lean`).  This is the first bridge in the project between the
formal-series side (`FormalGroup/`) and the affine points of the reduction theory (`Reduction/`).

## Main definitions

* `WeierstrassCurve.wParam` — `w(z) = adicEval z W.formalW ∈ R`, the Weierstrass expansion evaluated
  at the parameter `z ∈ 𝔪`.
* `WeierstrassCurve.xParam`, `WeierstrassCurve.yParam` — the recovered affine coordinates
  `x(z) = z/w(z)`, `y(z) = -1/w(z) ∈ K`.

## Main results

* `WeierstrassCurve.wParam_functional_eq` — `w(z)` satisfies the numeric Weierstrass functional
  equation (the `adicEval`-image of `formalW_eq`).
* `WeierstrassCurve.wParam_ne_zero` — `w(z) ≠ 0` for `z ≠ 0` (it factors as `z³ · unit`).
* `WeierstrassCurve.equation_xParam_yParam` — **the recovered point lies on the curve**:
  `W.toAffine.Equation (x(z)) (y(z))`, the numeric form of `formalX_formalY_weierstrass`.
* `WeierstrassCurve.localParam_xParam_yParam` — **the local parameter recovers `z`**:
  `-x(z)/y(z) = z`, so `z ↦ (x(z), y(z))` is a section of `P ↦ z(P)`.

These deliver the set-level inverse half of the identification `E₁(K) ≅ Ê(𝔪)` (issue #361).  ⚠️
This paragraph used to end *"the addition-law compatibility `z(P + Q) = F_E(z P, z Q)` remains"*;
it does not — it is `WeierstrassCurve.zParamHatEquiv_map_add`, and the identification is closed by
`WeierstrassCurve.E₁AddEquiv` (`EllipticCurves/Reduction/KernelFormalGroupIso.lean`).

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]

/-! ### The Weierstrass expansion evaluated at a parameter -/

/-- The Weierstrass coordinate expansion `w(z)` evaluated at a parameter `z ∈ 𝔪`: the `I`-adic
evaluation of the formal solution `W.formalW ∈ R⟦X⟧` at `z`, where `I = 𝔪`.  It is the numeric fixed
point of the Weierstrass functional equation (`wParam_functional_eq`). -/
noncomputable def wParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) : R :=
  adicEval (maximalIdeal R).asIdeal hz (integralModel R W).formalW

omit [IsFractionRing R K] in
/-- `w(z)` is the `adicEval`-image of the fixed-point equation `formalW = wOp formalW`, hence
satisfies the **numeric Weierstrass functional equation**
`w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`, with the integral-model coefficients. -/
theorem wParam_functional_eq (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) :
    wParam R W hz = z ^ 3
      + ((integralModel R W).a₁ * z + (integralModel R W).a₂ * z ^ 2) * wParam R W hz
      + ((integralModel R W).a₃ + (integralModel R W).a₄ * z) * wParam R W hz ^ 2
      + (integralModel R W).a₆ * wParam R W hz ^ 3 := by
  conv_lhs => rw [wParam, (integralModel R W).formalW_eq]
  simp only [WeierstrassCurve.wOp, map_add, map_mul, map_pow, adicEval_X, adicEval_C]
  rw [← wParam]

omit [IsFractionRing R K] in
/-- `w(z)` factors as `z³ · u(z)` where `u(z) = adicEval z (wCofactor)`. -/
theorem wParam_eq_cube_mul (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) :
    wParam R W hz = z ^ 3 * adicEval (maximalIdeal R).asIdeal hz (integralModel R W).wCofactor := by
  rw [wParam, (integralModel R W).formalW_eq_X_pow_mul_wCofactor, map_mul, map_pow, adicEval_X]

omit [IsFractionRing R K] in
/-- The cofactor value `u(z) = adicEval z (wCofactor)` is a **unit**: its reduction mod `𝔪` is
`constantCoeff wCofactor = 1`, which is a unit in the local ring `R`. -/
theorem isUnit_adicEval_wCofactor (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) :
    IsUnit (adicEval (maximalIdeal R).asIdeal hz (integralModel R W).wCofactor) := by
  set u := adicEval (maximalIdeal R).asIdeal hz (integralModel R W).wCofactor with hu
  have h1 : u - 1 ∈ (maximalIdeal R).asIdeal := by
    have he : u - 1 = adicEval (maximalIdeal R).asIdeal hz ((integralModel R W).wCofactor - 1) := by
      rw [hu, map_sub, adicEval_one]
    rw [he]
    refine adicEval_mem hz ?_
    rw [map_sub, (integralModel R W).constantCoeff_wCofactor, map_one, sub_self]
  by_contra hnu
  have hmem : u ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal u).mpr (mem_nonunits_iff.mpr hnu)
  have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have h2 := (IsLocalRing.maximalIdeal R).sub_mem hmem h1
    rwa [sub_sub_cancel] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_iff_one _ |>.mpr hone)

omit [IsFractionRing R K] in
/-- `w(z) ≠ 0` when `z ≠ 0`: it factors as `z³ · unit` in the domain `R`. -/
theorem wParam_ne_zero (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) : wParam R W hz ≠ 0 := by
  rw [wParam_eq_cube_mul]
  exact mul_ne_zero (pow_ne_zero _ hz0) (isUnit_adicEval_wCofactor R W hz).ne_zero

/-! ### The recovered affine coordinates -/

/-- The recovered `x`-coordinate `x(z) = z / w(z) ∈ K`. -/
noncomputable def xParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) : K :=
  algebraMap R K z / algebraMap R K (wParam R W hz)

/-- The recovered `y`-coordinate `y(z) = -1 / w(z) ∈ K`. -/
noncomputable def yParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) : K :=
  -1 / algebraMap R K (wParam R W hz)

omit [IsFractionRing R K] in
/-- The `K`-image of the numeric functional equation for `w(z)`, in the curve's own coefficients
`W.aᵢ = algebraMap R K (integralModel R W).aᵢ`. -/
private theorem algebraMap_wParam_functional_eq (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) :
    algebraMap R K (wParam R W hz) = algebraMap R K z ^ 3
      + (W.a₁ * algebraMap R K z + W.a₂ * algebraMap R K z ^ 2) * algebraMap R K (wParam R W hz)
      + (W.a₃ + W.a₄ * algebraMap R K z) * algebraMap R K (wParam R W hz) ^ 2
      + W.a₆ * algebraMap R K (wParam R W hz) ^ 3 := by
  have h := congrArg (algebraMap R K) (wParam_functional_eq R W hz)
  simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
    integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at h
  exact h

/-- **The recovered point lies on the curve.** The coordinates `(x(z), y(z)) = (z/w, -1/w)` satisfy
the Weierstrass equation of `W`.  This is the numeric form of the formal identity
`formalX_formalY_weierstrass`, obtained from the functional equation for `w(z)`. -/
theorem equation_xParam_yParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    W.toAffine.Equation (xParam R W hz) (yParam R W hz) := by
  have hwne : algebraMap R K (wParam R W hz) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz hz0)
  have hfe := algebraMap_wParam_functional_eq R W hz
  rw [Affine.equation_iff]
  change yParam R W hz ^ 2 + W.a₁ * xParam R W hz * yParam R W hz + W.a₃ * yParam R W hz
      = xParam R W hz ^ 3 + W.a₂ * xParam R W hz ^ 2 + W.a₄ * xParam R W hz + W.a₆
  rw [xParam, yParam]
  field_simp
  linear_combination hfe

/-- **The local parameter recovers `z`.** For the recovered coordinates,
`-x(z)/y(z) = z`, so `z ↦ (x(z), y(z))` is a section of the local parameter `P ↦ z(P) = -x/y`. -/
theorem localParam_xParam_yParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    -xParam R W hz / yParam R W hz = algebraMap R K z := by
  have hwne : algebraMap R K (wParam R W hz) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz hz0)
  rw [xParam, yParam]
  field_simp

end WeierstrassCurve
