/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.KernelSection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Injectivity of the local parameter and the set bijection `E₁(K) ≃ 𝔪`

Let `R` be a **complete** discrete valuation ring (`IsAdicComplete (maximalIdeal R).asIdeal R`) with
fraction field `K = Frac R`, and let `W : WeierstrassCurve K` be an elliptic curve (`W.IsElliptic`)
with an integral model (`IsIntegral R W`).  The sibling file `Reduction/KernelSection.lean` proved
the **surjectivity** of the local parameter `zParam : E₁(K) → 𝔪` (via the section
`pointOfParam : 𝔪 ∖ {0} → E₁(K)`).  This file completes the *set-level* half of the identification
`E₁(K) ≅ Ê(𝔪)` (issue #361) by proving **injectivity**: the coordinate expansion recovers a point
from its local parameter.

The heart is the numeric **uniqueness of the Weierstrass `w`-functional equation** among elements of
valuation `< 1` (`wFunctionalEq_unique`): if `W₁` and `W₂` both satisfy
`W = Z³ + (a₁Z + a₂Z²)W + (a₃ + a₄Z)W² + a₆W³` with `v Z, v W₁, v W₂ < 1`, then `W₁ = W₂` (standard
non-archimedean contraction argument).  For a point `P = (x, y)` reducing to the origin both
`w(z(P))` (via `wParam_functional_eq`) and `-1/y` (via the Weierstrass equation of `P`) satisfy this
equation, so `w(z(P)) = -1/y`, hence `(x(z(P)), y(z(P))) = (x, y)`: the coordinate expansion
recovers `P` (`pointOfParam_localParamR`).  Assembling with the surjectivity gives the bijection.

## Main results

* `WeierstrassCurve.pointOfParam_localParamR` — `pointOfParam (z P) = P` for a nonzero `P ∈ E₁(K)`.
* `WeierstrassCurve.zParam_injective` — `zParam : E₁(K) → 𝔪` is injective.
* `WeierstrassCurve.zParam_bijective` — `zParam` is bijective.
* `WeierstrassCurve.zParamEquiv` — the set bijection `E₁(K) ≃ 𝔪`.

What #361 still wanted when this file landed was the addition-law compatibility
`z(P + Q) = F_E(z P, z Q)` (AEC IV.1 / VII.2.2), which upgrades this set bijection to a group
isomorphism `E₁(K) ≃+ Ê(𝔪)`.  ⚠️ **It is merged**: `WeierstrassCurve.zParamHatEquiv_map_add` and
`WeierstrassCurve.E₁AddEquiv` (`EllipticCurves/Reduction/KernelFormalGroupIso.lean`).

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1/2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]

/-! ### Numeric uniqueness of the Weierstrass functional equation -/

omit [IsAdicComplete (maximalIdeal R).asIdeal R] in
/-- **Uniqueness of the small solution of the Weierstrass `w`-functional equation.** If `W₁` and
`W₂` both satisfy `W = Z³ + (a₁Z + a₂Z²)W + (a₃ + a₄Z)W² + a₆W³` and all of `Z, W₁, W₂` have
valuation `< 1`, then `W₁ = W₂`.  The difference `d = W₁ - W₂` factors as `d = d · B` with `v B < 1`
(each coefficient is integral and every monomial has a factor of valuation `< 1`), so `d = 0`.

Exposed (was `private`) so the numeric formal-group evaluation (`Reduction/FormalGroupEval.lean`)
can identify the `(z, w)`-plane chord line values with the coordinate expansion `wParam`. -/
theorem wFunctionalEq_unique (W : WeierstrassCurve K) [IsIntegral R W]
    {Z W₁ W₂ : K}
    (hZ : valuation K (maximalIdeal R) Z < 1)
    (hW₁ : valuation K (maximalIdeal R) W₁ < 1)
    (hW₂ : valuation K (maximalIdeal R) W₂ < 1)
    (h₁ : W₁ = Z ^ 3 + (W.a₁ * Z + W.a₂ * Z ^ 2) * W₁ + (W.a₃ + W.a₄ * Z) * W₁ ^ 2
      + W.a₆ * W₁ ^ 3)
    (h₂ : W₂ = Z ^ 3 + (W.a₁ * Z + W.a₂ * Z ^ 2) * W₂ + (W.a₃ + W.a₄ * Z) * W₂ ^ 2
      + W.a₆ * W₂ ^ 3) :
    W₁ = W₂ := by
  set v := valuation K (maximalIdeal R) with hv
  have vmul_lt : ∀ {a b : K}, v a ≤ 1 → v b < 1 → v (a * b) < 1 := by
    intro a b ha hb
    rw [v.map_mul]
    calc v a * v b ≤ 1 * v b := mul_le_mul' ha le_rfl
      _ = v b := one_mul _
      _ < 1 := hb
  have vadd_lt : ∀ {a b : K}, v a < 1 → v b < 1 → v (a + b) < 1 := fun ha hb =>
    lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
  have vsq_lt : ∀ {a : K}, v a < 1 → v (a ^ 2) < 1 := by
    intro a ha
    rw [map_pow]
    calc v a ^ 2 = v a * v a := sq (v a)
      _ ≤ 1 * v a := mul_le_mul' (le_of_lt ha) le_rfl
      _ = v a := one_mul _
      _ < 1 := ha
  have ha₁ : v W.a₁ ≤ 1 := by rw [hv]; exact valuation_a₁_le_one R W
  have ha₂ : v W.a₂ ≤ 1 := by rw [hv]; exact valuation_a₂_le_one R W
  have ha₃ : v W.a₃ ≤ 1 := by rw [hv]; exact valuation_a₃_le_one R W
  have ha₄ : v W.a₄ ≤ 1 := by rw [hv]; exact valuation_a₄_le_one R W
  have ha₆ : v W.a₆ ≤ 1 := by rw [hv]; exact valuation_a₆_le_one R W
  have hT1 : v (W.a₁ * Z + W.a₂ * Z ^ 2) < 1 :=
    vadd_lt (vmul_lt ha₁ hZ) (vmul_lt ha₂ (vsq_lt hZ))
  have hcoef3 : v (W.a₃ + W.a₄ * Z) ≤ 1 := by
    refine le_trans (v.map_add _ _) (max_le ha₃ ?_)
    rw [v.map_mul]; exact mul_le_one' ha₄ (le_of_lt hZ)
  have hT2 : v ((W.a₃ + W.a₄ * Z) * (W₁ + W₂)) < 1 := vmul_lt hcoef3 (vadd_lt hW₁ hW₂)
  have hquad : v (W₁ ^ 2 + W₁ * W₂ + W₂ ^ 2) < 1 :=
    vadd_lt (vadd_lt (vsq_lt hW₁) (vmul_lt (le_of_lt hW₁) hW₂)) (vsq_lt hW₂)
  have hT3 : v (W.a₆ * (W₁ ^ 2 + W₁ * W₂ + W₂ ^ 2)) < 1 := vmul_lt ha₆ hquad
  have hB : v (W.a₁ * Z + W.a₂ * Z ^ 2 + (W.a₃ + W.a₄ * Z) * (W₁ + W₂)
      + W.a₆ * (W₁ ^ 2 + W₁ * W₂ + W₂ ^ 2)) < 1 := vadd_lt (vadd_lt hT1 hT2) hT3
  have hfactor : (W₁ - W₂) * (1 - (W.a₁ * Z + W.a₂ * Z ^ 2 + (W.a₃ + W.a₄ * Z) * (W₁ + W₂)
      + W.a₆ * (W₁ ^ 2 + W₁ * W₂ + W₂ ^ 2))) = 0 := by
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · rw [sub_eq_zero] at h
    rw [← h, v.map_one] at hB
    exact absurd hB (lt_irrefl 1)

/-! ### The coordinate expansion recovers the point -/

/-- **The coordinate expansion recovers the point.** For a point `P = (x, y)` reducing to the origin
(`1 < v x`) with nonzero local parameter, the recovered point `pointOfParam (z P)` equals `P`.  The
key step is `w(z P) = -1/y` (numeric uniqueness of the functional equation), which gives back the
coordinates `x(z P) = x` and `y(z P) = y`. -/
theorem pointOfParam_localParamR (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hx : 1 < valuation K (maximalIdeal R) x)
    (hz0 : localParamR R W (.some x y h) ≠ 0) :
    pointOfParam R W (localParamR_mem R W (P := .some x y h) hx) hz0 = .some x y h := by
  have hz : localParamR R W (.some x y h) ∈ (maximalIdeal R).asIdeal :=
    localParamR_mem R W (P := .some x y h) hx
  have hZK : algebraMap R K (localParamR R W (.some x y h)) = -x / y := by
    rw [algebraMap_localParamR, localParam_some, ite_eq_left hx]
  obtain ⟨hvy1, _⟩ := valuation_pow_two_eq_pow_three_of_one_lt R W h.1 hx
  have hvy_pos : 0 < valuation K (maximalIdeal R) y := lt_trans zero_lt_one hvy1
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [Valuation.map_zero] at hvy1; exact absurd hvy1 (not_lt.mpr zero_le)
  have hvxy : valuation K (maximalIdeal R) (-x / y) < 1 :=
    valuation_neg_x_div_y_lt_one R W h.1 hx
  have hvw : algebraMap R K (wParam R W hz) = -1 / y := by
    refine wFunctionalEq_unique R W (Z := -x / y)
      (W₁ := algebraMap R K (wParam R W hz)) (W₂ := -1 / y) hvxy ?_ ?_ ?_ ?_
    · rw [valuation_algebraMap_wParam, hZK]
      calc valuation K (maximalIdeal R) (-x / y) ^ 3
            < 1 ^ 3 := pow_lt_pow_left₀ hvxy zero_le (by norm_num)
        _ = 1 := one_pow 3
    · rw [neg_div, Valuation.map_neg, Valuation.map_div, Valuation.map_one]
      exact (div_lt_one₀ hvy_pos).mpr hvy1
    · have hfe := congrArg (algebraMap R K) (wParam_functional_eq R W hz)
      simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
        integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at hfe
      rw [hZK] at hfe
      exact hfe
    · have heqn : y ^ 2 + W.a₁ * x * y + W.a₃ * y
          = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
        have h1 := h.1; rw [Affine.equation_iff] at h1; exact h1
      field_simp
      linear_combination -heqn
  have hxP : xParam R W hz = x := by rw [xParam, hZK, hvw]; field_simp
  have hyP : yParam R W hz = y := by rw [yParam, hvw]; field_simp
  rw [pointOfParam, WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxP, hyP⟩

omit [IsAdicComplete (maximalIdeal R).asIdeal R] in
/-- The local parameter of a nonzero point reducing to the origin is nonzero: `z(P) ≠ 0`. -/
theorem localParamR_ne_zero_of_reduces (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hx : 1 < valuation K (maximalIdeal R) x) :
    localParamR R W (.some x y h) ≠ 0 := by
  intro h0
  have hzero : localParam R W (.some x y h) = 0 := by
    rw [← algebraMap_localParamR, h0, map_zero]
  rw [localParam_some, ite_eq_left hx] at hzero
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [Valuation.map_zero] at hx; exact absurd hx (not_lt.mpr zero_le)
  obtain ⟨hvy1, _⟩ := valuation_pow_two_eq_pow_three_of_one_lt R W h.1 hx
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [Valuation.map_zero] at hvy1; exact absurd hvy1 (not_lt.mpr zero_le)
  rw [div_eq_zero_iff] at hzero
  rcases hzero with hxx | hyy
  · exact hx0 (neg_eq_zero.mp hxx)
  · exact hy0 hyy

/-! ### Injectivity and the set bijection -/

open Classical in
/-- The recovery map `𝔪 → E₁(K)`: the origin for `0`, and `pointOfParam t` otherwise.  It is a
left inverse of `zParam` (`paramRecover_zParam`). -/
noncomputable def paramRecover (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    (t : (maximalIdeal R).asIdeal) : {P : W.toAffine.Point // ReducesToZero R W P} :=
  if h : (t : R) = 0 then ⟨.zero, reducesToZero_zero R W⟩
  else ⟨pointOfParam R W t.2 h, reducesToZero_pointOfParam R W t.2 h⟩

/-- `paramRecover` is a left inverse of `zParam`: recovering the point from its local parameter
returns the original point. -/
theorem paramRecover_zParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] :
    Function.LeftInverse (paramRecover R W) (zParam R W) := by
  rintro ⟨p, hp⟩
  cases p with
  | zero =>
    have h0 : ((zParam R W ⟨.zero, hp⟩ : (maximalIdeal R).asIdeal) : R) = 0 := by
      rw [zParam_coe]; exact localParamR_zero R W
    unfold paramRecover
    rw [dite_eq_left h0]
  | some x y h =>
    have hx : 1 < valuation K (maximalIdeal R) x := hp
    have hne : ((zParam R W ⟨.some x y h, hp⟩ : (maximalIdeal R).asIdeal) : R) ≠ 0 := by
      rw [zParam_coe]; exact localParamR_ne_zero_of_reduces R W hx
    unfold paramRecover
    rw [dite_eq_right hne]
    exact Subtype.ext (pointOfParam_localParamR R W hx hne)

/-- **Injectivity of the local parameter** `zParam : E₁(K) → 𝔪`. -/
theorem zParam_injective (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] :
    Function.Injective (zParam R W) :=
  (paramRecover_zParam R W).injective

/-- **The local parameter is bijective**: together with `zParam_surjective` this closes the
set-level bijection `E₁(K) ≃ 𝔪`. -/
theorem zParam_bijective (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] :
    Function.Bijective (zParam R W) :=
  ⟨zParam_injective R W, zParam_surjective R W⟩

/-- **The set bijection `E₁(K) ≃ 𝔪`** of the kernel of reduction with the maximal ideal, via the
local parameter `z = -x/y`.  The remaining step of the identification `E₁(K) ≅ Ê(𝔪)` (issue #361) is
to upgrade this to a group isomorphism using the addition-law compatibility
`z(P + Q) = F_E(z P, z Q)`. -/
noncomputable def zParamEquiv (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] :
    {P : W.toAffine.Point // ReducesToZero R W P} ≃ (maximalIdeal R).asIdeal :=
  Equiv.ofBijective (zParam R W) (zParam_bijective R W)

end WeierstrassCurve
