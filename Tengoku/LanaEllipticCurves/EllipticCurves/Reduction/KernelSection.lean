/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.LocalParameter
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.LocalParameterInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The section of the local parameter: `𝔪 → E₁(K)` and surjectivity of `z = -x/y`

Let `R` be a **complete** discrete valuation ring (`IsAdicComplete (maximalIdeal R).asIdeal R`) with
fraction field `K = Frac R`, and let `W : WeierstrassCurve K` be an elliptic curve (`W.IsElliptic`)
with an integral model (`IsIntegral R W`).  The sibling files build the forward local parameter
`zParam : E₁(K) → 𝔪` (`Reduction/LocalParameter.lean`) and the coordinate expansion
`z ↦ (x(z), y(z))` (`Reduction/LocalParameterInverse.lean`).  This file assembles the **section**:
for a nonzero parameter `z ∈ 𝔪` the recovered coordinates `(x(z), y(z)) = (z/w(z), -1/w(z))`
constitute a genuine nonsingular point `pointOfParam z` of `W` which

* **reduces to the origin** (`reducesToZero_pointOfParam`), so it lies in `E₁(K)`, and
* **has local parameter `z`** (`zParam_pointOfParam`): `zParam (pointOfParam z) = z`.

Hence `pointOfParam` is a right inverse of `zParam` on `𝔪 ∖ {0}`, and together with the
normalisation `z(O) = 0` this shows the local-parameter map is **surjective**
(`zParam_surjective`).  This is the set-level *inverse-half* rung of the identification
`E₁(K) ≅ Ê(𝔪)` (issue #361).  ⚠️ The two things this paragraph used to call *"the remaining
content"* are both merged: the injectivity of `zParam` (equivalently
`pointOfParam (zParam P) = P` on `E₁`) is `WeierstrassCurve.zParam_injective`, in the sibling
file `EllipticCurves/Reduction/KernelBijection.lean`, and the addition-law
compatibility `z(P + Q) = F_E(z P, z Q)` is `WeierstrassCurve.zParamHatEquiv_map_add`; together
they package `zParam` into the group isomorphism `WeierstrassCurve.E₁AddEquiv`
(`EllipticCurves/Reduction/KernelFormalGroupIso.lean`).

## Main definitions

* `WeierstrassCurve.pointOfParam` — the nonsingular point `(x(z), y(z))` recovered from a nonzero
  parameter `z ∈ 𝔪`.

## Main results

* `WeierstrassCurve.valuation_algebraMap_wParam` — `v(w(z)) = v(z)³` (the `y`-pole order).
* `WeierstrassCurve.one_lt_valuation_xParam` — `1 < v(x(z))` for `z ≠ 0`: the recovered point has a
  pole, hence reduces to the origin.
* `WeierstrassCurve.reducesToZero_pointOfParam` — `pointOfParam z ∈ E₁(K)`.
* `WeierstrassCurve.zParam_pointOfParam` — `zParam (pointOfParam z) = z` (the section identity).
* `WeierstrassCurve.zParam_surjective` — the local-parameter map `zParam : E₁(K) → 𝔪` is surjective.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]

/-! ### Valuation of the recovered coordinates -/

/-- The pole order of the recovered `y`-coordinate: `v(w(z)) = v(z)³`.  Indeed `w(z) = z³ · u(z)`
with `u(z)` a unit of `R` (`wParam_eq_cube_mul`, `isUnit_adicEval_wCofactor`), and a unit has
valuation `1` (it lies outside the maximal ideal). -/
theorem valuation_algebraMap_wParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) :
    valuation K (maximalIdeal R) (algebraMap R K (wParam R W hz))
      = valuation K (maximalIdeal R) (algebraMap R K z) ^ 3 := by
  have hu : valuation K (maximalIdeal R)
      (algebraMap R K
        (adicEval (maximalIdeal R).asIdeal hz (integralModel R W).wCofactor)) = 1 := by
    rw [valuation_eq_one_iff_notMem]
    exact fun hmem => (maximalIdeal R).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem (isUnit_adicEval_wCofactor R W hz))
  rw [wParam_eq_cube_mul, map_mul, map_pow, map_mul, map_pow, hu, mul_one]

/-- For a nonzero parameter `z ∈ 𝔪`, the recovered `x`-coordinate has a pole: `1 < v(x(z))`.
Indeed `v(x(z)) = v(z) / v(z)³ = v(z)⁻²` and `0 < v(z) < 1`, so `v(z)⁻² > 1`.  This is exactly the
`ReducesToZero` condition, so the recovered point lies in `E₁(K)`. -/
theorem one_lt_valuation_xParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    1 < valuation K (maximalIdeal R) (xParam R W hz) := by
  have hne : algebraMap R K z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hz0
  have hvz_pos : 0 < valuation K (maximalIdeal R) (algebraMap R K z) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hne)
  have hvz_lt : valuation K (maximalIdeal R) (algebraMap R K z) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) z).mpr hz
  set a := valuation K (maximalIdeal R) (algebraMap R K z) with ha
  rw [xParam, Valuation.map_div, valuation_algebraMap_wParam, ← ha, one_lt_div₀ (pow_pos hvz_pos 3)]
  -- Goal: `a ^ 3 < a`.
  have ha2_lt : a ^ 2 < 1 := by
    calc a ^ 2 < 1 ^ 2 := pow_lt_pow_left₀ hvz_lt (le_of_lt hvz_pos) (by norm_num)
      _ = 1 := one_pow 2
  calc a ^ 3 = a ^ 2 * a := pow_succ a 2
    _ < 1 * a := mul_lt_mul_of_pos_right ha2_lt hvz_pos
    _ = a := one_mul a

/-! ### The recovered point and the section identity -/

/-- The **nonsingular point recovered from a nonzero parameter** `z ∈ 𝔪`: the coordinates
`(x(z), y(z)) = (z/w(z), -1/w(z))` satisfy the Weierstrass equation (`equation_xParam_yParam`), and
on an elliptic curve every solution is nonsingular (`equation_iff_nonsingular`). -/
noncomputable def pointOfParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) : W.toAffine.Point :=
  .some (xParam R W hz) (yParam R W hz)
    (W.toAffine.equation_iff_nonsingular.mp (equation_xParam_yParam R W hz hz0))

/-- The recovered point **reduces to the origin**, i.e. lies in `E₁(K)`. -/
theorem reducesToZero_pointOfParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    ReducesToZero R W (pointOfParam R W hz hz0) := by
  rw [pointOfParam, reducesToZero_some_iff]
  exact one_lt_valuation_xParam R W hz hz0

/-- The **local parameter of the recovered point is `z`**: `-x(z)/y(z) = z`.  Because the recovered
point has a pole (`one_lt_valuation_xParam`), `localParam` takes its genuine `-x/y` branch, which is
`z` by `localParam_xParam_yParam`. -/
theorem localParam_pointOfParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    localParam R W (pointOfParam R W hz hz0) = algebraMap R K z := by
  rw [pointOfParam, localParam_some, ite_eq_left (one_lt_valuation_xParam R W hz hz0)]
  exact localParam_xParam_yParam R W hz hz0

/-- **The section identity.** For a nonzero `z ∈ 𝔪`, the local-parameter map returns `z` on the
recovered point: `zParam (pointOfParam z) = z`.  Hence `pointOfParam` is a right inverse of `zParam`
on `𝔪 ∖ {0}`. -/
theorem zParam_pointOfParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    zParam R W ⟨pointOfParam R W hz hz0, reducesToZero_pointOfParam R W hz hz0⟩ = ⟨z, hz⟩ := by
  refine Subtype.ext ?_
  refine IsFractionRing.injective R K ?_
  rw [zParam_coe, algebraMap_localParamR, localParam_pointOfParam]

/-- **Surjectivity of the local parameter.** Every `t ∈ 𝔪` is `z(P)` for some `P ∈ E₁(K)`: the
origin covers `t = 0`, and `pointOfParam t` covers `t ≠ 0`.  Combined with the injectivity of
`zParam` (the remaining rung), this gives the set bijection `E₁(K) ≃ 𝔪`. -/
theorem zParam_surjective (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] :
    Function.Surjective (zParam R W) := by
  intro t
  by_cases ht : (t : R) = 0
  · exact ⟨⟨.zero, reducesToZero_zero R W⟩, by rw [zParam_zero]; exact Subtype.ext ht.symm⟩
  · exact ⟨⟨pointOfParam R W t.2 ht, reducesToZero_pointOfParam R W t.2 ht⟩,
      by rw [zParam_pointOfParam]⟩

end WeierstrassCurve
