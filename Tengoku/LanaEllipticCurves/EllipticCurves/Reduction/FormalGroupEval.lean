/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.KernelBijection
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numeric evaluation of the Weierstrass formal group law `formalGroupZW`

The genuine, pole-free Weierstrass formal group law `W.formalGroupZW : MvPowerSeries (Fin 2) R`
(`EllipticCurves/FormalGroup/GenuineLaw.lean`) is precisely the object designed to be evaluated
`I`-adically: `x ⊕ y = adicEvalMv I ![x, y] W.formalGroupZW` is the group operation of `Ê(𝔪)`
(`FormalGroup/PointsOnIdeal.lean`).  This file supplies the **numeric evaluation** of that law over
a complete discrete valuation ring, the formal-side input to the additivity crux
`z(P + Q) = F_E(z P, z Q)` of the reduction-kernel isomorphism `E₁(K) ≅ Ê(𝔪)` (issue #361).

The law is built by the chord process in the `(z, w)`-plane
(`formalGroupZW = -z₃' · (formalGroupDen)⁻¹` with `z₃' = -B·A⁻¹ - z₁ - z₂` the Vieta third root,
`A = formalGroupLead`, `B = formalGroupSub`, `formalGroupDen` the negation denominator).  Since
`adicEvalMv` is a ring homomorphism, its value on `formalGroupZW` is obtained by pushing it through
this definition; the only content is that the two `invOfUnit` factors (`A⁻¹`, `formalGroupDen⁻¹`)
map to genuine inverses, which holds since `A` and `formalGroupDen` have constant coefficient `1`.

## Main results

* `WeierstrassCurve.ringHom_formalGroupZW` — the closed form of `φ W.formalGroupZW` for **any** ring
  homomorphism `φ : MvPowerSeries (Fin 2) R →+* R`, in terms of the images of the chord data.
* `WeierstrassCurve.ringHom_formalGroupLead_mul_inv`, `ringHom_formalGroupDen_mul_inv` — the two
  unit factors `φ (invOfUnit …)` are genuine inverses of `φ formalGroupLead` / `φ formalGroupDen`.
* `WeierstrassCurve.wLineZero_eq_wParam`, `wLineOne_eq_wParam` — the `(z, w)`-plane chord line
  values coincide with the coordinate expansions `wParam z₁`, `wParam z₂`.
* `WeierstrassCurve.adicEvalMv_formalGroupZW_mem` — the numeric value
  `adicEvalMv 𝔪 ![z₁, z₂] (integralModel R W).formalGroupZW` lies in `𝔪` (it is the local parameter
  of the formal sum, `∈ Ê(𝔪)`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open MvPowerSeries

namespace WeierstrassCurve

/-! ### Constant coefficients of the chord data

The building blocks of `formalGroupZW` all have vanishing constant coefficient except the two
denominators `formalGroupLead` and `formalGroupDen`, whose constant coefficient is `1`.  These facts
are proved privately in `FormalGroup/GenuineLaw.lean`; we re-derive the ones we need here from the
public order bound `two_le_order_formalWDividedDiff` so this file stays self-contained. -/

section Formal

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private lemma cc_formalWDividedDiff : MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
    (le_trans (by exact_mod_cast one_le_two) W.two_le_order_formalWDividedDiff)

private lemma cc_formalGroupNu : MvPowerSeries.constantCoeff W.formalGroupNu = 0 := by
  rw [formalGroupNu, map_sub, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, sub_zero,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := PowerSeries.coeff_toMvPowerSeries_single W.formalW (0 : Fin 2) 0
  rw [Finsupp.single_zero] at h
  rw [h]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)

private lemma cc_formalGroupLead : MvPowerSeries.constantCoeff W.formalGroupLead = 1 := by
  rw [formalGroupLead]
  simp only [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, map_one,
    W.cc_formalWDividedDiff]
  ring

private lemma cc_formalGroupSub : MvPowerSeries.constantCoeff W.formalGroupSub = 0 := by
  rw [formalGroupSub]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPowerSeries.constantCoeff_C,
    W.cc_formalWDividedDiff, W.cc_formalGroupNu]
  ring

private lemma cc_formalThirdRoot : MvPowerSeries.constantCoeff W.formalThirdRoot = 0 := by
  rw [formalThirdRoot]
  simp only [map_sub, map_neg, map_mul, MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_invOfUnit, W.cc_formalGroupSub]
  ring

private lemma cc_formalGroupDen : MvPowerSeries.constantCoeff W.formalGroupDen = 1 := by
  rw [formalGroupDen]
  simp only [map_sub, map_add, map_mul, MvPowerSeries.constantCoeff_C, map_one,
    W.cc_formalThirdRoot, W.cc_formalWDividedDiff, W.cc_formalGroupNu]
  ring

/-! ### The `invOfUnit` factors are genuine inverses -/

/-- `formalGroupLead · (formalGroupLead)⁻¹ = 1` (the leading cubic coefficient is a unit, with
constant coefficient `1`). -/
theorem formalGroupLead_mul_invOfUnit :
    W.formalGroupLead * invOfUnit W.formalGroupLead 1 = 1 :=
  MvPowerSeries.mul_invOfUnit _ 1 (by rw [W.cc_formalGroupLead, Units.val_one])

/-- `formalGroupDen · (formalGroupDen)⁻¹ = 1` (the negation denominator is a unit, with constant
coefficient `1`). -/
theorem formalGroupDen_mul_invOfUnit :
    W.formalGroupDen * invOfUnit W.formalGroupDen 1 = 1 :=
  MvPowerSeries.mul_invOfUnit _ 1 (by rw [W.cc_formalGroupDen, Units.val_one])

/-! ### The closed form under a ring homomorphism -/

/-- **Closed form of the formal group law under any ring homomorphism.** For any
`φ : MvPowerSeries (Fin 2) R →+* R`, pushing `φ` through the chord construction
`formalGroupZW = -z₃' · (formalGroupDen)⁻¹`, `z₃' = -B·A⁻¹ - z₁ - z₂`, gives

`φ formalGroupZW = (φ B · φ A⁻¹ + φ z₁ + φ z₂) · φ (formalGroupDen)⁻¹`. -/
theorem ringHom_formalGroupZW (φ : MvPowerSeries (Fin 2) R →+* R) :
    φ W.formalGroupZW =
      (φ W.formalGroupSub * φ (invOfUnit W.formalGroupLead 1) + φ (X 0) + φ (X 1))
        * φ (invOfUnit W.formalGroupDen 1) := by
  rw [formalGroupZW, formalThirdRoot]
  simp only [map_mul, map_neg, map_sub]
  ring

/-- Under any ring homomorphism `φ`, the image of `(formalGroupLead)⁻¹` is a genuine inverse of
`φ formalGroupLead`. -/
theorem ringHom_formalGroupLead_mul_inv (φ : MvPowerSeries (Fin 2) R →+* R) :
    φ W.formalGroupLead * φ (invOfUnit W.formalGroupLead 1) = 1 := by
  rw [← map_mul, W.formalGroupLead_mul_invOfUnit, map_one]

/-- Under any ring homomorphism `φ`, the image of `(formalGroupDen)⁻¹` is a genuine inverse of
`φ formalGroupDen`. -/
theorem ringHom_formalGroupDen_mul_inv (φ : MvPowerSeries (Fin 2) R →+* R) :
    φ W.formalGroupDen * φ (invOfUnit W.formalGroupDen 1) = 1 := by
  rw [← map_mul, W.formalGroupDen_mul_invOfUnit, map_one]

end Formal

/-! ### Numeric evaluation over a complete DVR -/

section Numeric

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]

omit [IsFractionRing R K] in
/-- **The formal group law evaluates into `𝔪`.** For `z₁, z₂ ∈ 𝔪`, the numeric value
`adicEvalMv 𝔪 ![z₁, z₂] (integralModel R W).formalGroupZW` — the local parameter of the formal sum
`z₁ ⊕ z₂` in `Ê(𝔪)` — lies in the maximal ideal, since `formalGroupZW` has zero constant
coefficient. -/
theorem adicEvalMv_formalGroupZW_mem (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal) :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW
      ∈ (maximalIdeal R).asIdeal :=
  adicEvalMv_mem _ ha (integralModel R W).constantCoeff_formalGroupZW

/-! ### The `(z, w)`-plane line values and the numeric collinearity

The two formal points of the chord are `(z₁, w(z₁))`, `(z₂, w(z₂))`, whose second coordinate is the
value of the line `w = λ z + ν` at `zᵢ`, i.e. `adicEvalMv 𝔪 ![z₁,z₂] (formalWDividedDiff · Xᵢ +
formalGroupNu)`.  Pushing the collinearity `formalCubicResidual_root_zero/one` through the ring
homomorphism `adicEvalMv` shows these line values solve the **numeric Weierstrass functional
equation** with parameter `z₁` resp. `z₂` — the same equation the coordinate expansion `wParam`
satisfies (`wParam_functional_eq`).  Together with the uniqueness of the small solution
(`Reduction/KernelBijection.wFunctionalEq_unique`) this identifies the line values with
`wParam z₁`, `wParam z₂`, connecting the formal chord data to the coordinate expansions — the input
the affine-matching rung (issue #367) consumes. -/

/-- The `(z, w)`-plane value of the chord line at `z₁`: `w(z₁) = λ·z₁ + ν`, as the numeric
evaluation of `formalWDividedDiff · X 0 + formalGroupNu`. -/
noncomputable def wLineZero (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal) : R :=
  adicEvalMv (maximalIdeal R).asIdeal ha
    ((integralModel R W).formalWDividedDiff * MvPowerSeries.X 0 + (integralModel R W).formalGroupNu)

/-- The `(z, w)`-plane value of the chord line at `z₂`: `w(z₂) = λ·z₂ + ν`. -/
noncomputable def wLineOne (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal) : R :=
  adicEvalMv (maximalIdeal R).asIdeal ha
    ((integralModel R W).formalWDividedDiff * MvPowerSeries.X 1 + (integralModel R W).formalGroupNu)

omit [IsFractionRing R K] in
/-- **Numeric collinearity at `z₁`.** The line value `w(z₁)` solves the Weierstrass functional
equation `w = z₁³ + (a₁z₁ + a₂z₁²)w + (a₃ + a₄z₁)w² + a₆w³` with the integral-model coefficients —
the `adicEvalMv`-image of `formalCubicResidual_root_zero`. -/
theorem wLineZero_functional_eq (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal) :
    wLineZero R W ha = z₁ ^ 3
      + ((integralModel R W).a₁ * z₁ + (integralModel R W).a₂ * z₁ ^ 2) * wLineZero R W ha
      + ((integralModel R W).a₃ + (integralModel R W).a₄ * z₁) * wLineZero R W ha ^ 2
      + (integralModel R W).a₆ * wLineZero R W ha ^ 3 := by
  have hz1 : adicEvalMv (maximalIdeal R).asIdeal ha (X (0 : Fin 2)) = z₁ := by
    rw [adicEvalMv_X]; rfl
  have key := congrArg (adicEvalMv (maximalIdeal R).asIdeal ha)
    (integralModel R W).formalCubicResidual_root_zero
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, adicEvalMv_C, hz1] at key
  simp only [wLineZero, map_add, map_mul, hz1]
  linear_combination -key

omit [IsFractionRing R K] in
/-- **Numeric collinearity at `z₂`.** The line value `w(z₂)` solves the Weierstrass functional
equation with parameter `z₂` — the `adicEvalMv`-image of `formalCubicResidual_root_one`. -/
theorem wLineOne_functional_eq (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal) :
    wLineOne R W ha = z₂ ^ 3
      + ((integralModel R W).a₁ * z₂ + (integralModel R W).a₂ * z₂ ^ 2) * wLineOne R W ha
      + ((integralModel R W).a₃ + (integralModel R W).a₄ * z₂) * wLineOne R W ha ^ 2
      + (integralModel R W).a₆ * wLineOne R W ha ^ 3 := by
  have hz2 : adicEvalMv (maximalIdeal R).asIdeal ha (X (1 : Fin 2)) = z₂ := by
    rw [adicEvalMv_X]; rfl
  have key := congrArg (adicEvalMv (maximalIdeal R).asIdeal ha)
    (integralModel R W).formalCubicResidual_root_one
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, adicEvalMv_C, hz2] at key
  simp only [wLineOne, map_add, map_mul, hz2]
  linear_combination -key

omit [IsFractionRing R K] in
/-- The line value `w(z₁)` lies in `𝔪`: `formalWDividedDiff · X 0 + formalGroupNu` has zero constant
coefficient (both summands have positive order). -/
theorem wLineZero_mem (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal) :
    wLineZero R W ha ∈ (maximalIdeal R).asIdeal := by
  refine adicEvalMv_mem _ ha ?_
  rw [map_add, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, zero_add,
    (integralModel R W).cc_formalGroupNu]

omit [IsFractionRing R K] in
/-- The line value `w(z₂)` lies in `𝔪`. -/
theorem wLineOne_mem (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal) :
    wLineOne R W ha ∈ (maximalIdeal R).asIdeal := by
  refine adicEvalMv_mem _ ha ?_
  rw [map_add, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, zero_add,
    (integralModel R W).cc_formalGroupNu]

omit [IsFractionRing R K] in
/-- `wParam z` lies in `𝔪` for `z ∈ 𝔪`: it factors as `z³ · u(z)` with `z³ ∈ 𝔪`. -/
private theorem wParam_mem (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) : wParam R W hz ∈ (maximalIdeal R).asIdeal := by
  rw [wParam_eq_cube_mul]
  exact Ideal.mul_mem_right _ _ (by rw [pow_succ, pow_two]; exact Ideal.mul_mem_left _ _ hz)

/-! ### Identification of the line values with the coordinate expansion `wParam` -/

/-- **The chord line value at `z₁` is the coordinate expansion `wParam z₁`.**  Both
`wLineZero` (the `(z, w)`-plane value of the chord line at `z₁`) and `wParam z₁` solve the numeric
Weierstrass functional equation with parameter `z₁` and lie in `𝔪`; by uniqueness of the small
solution (`wFunctionalEq_unique`) they coincide.  This connects the formal chord data of
`formalGroupZW` to the coordinate expansions `xParam`/`yParam` of the reduction theory. -/
theorem wLineZero_eq_wParam (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)
    (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal) :
    wLineZero R W ha = wParam R W hz₁ := by
  refine IsFractionRing.injective R K ?_
  have hZlt : valuation K (maximalIdeal R) (algebraMap R K z₁) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) z₁).mpr hz₁
  have hW1lt : valuation K (maximalIdeal R) (algebraMap R K (wLineZero R W ha)) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr (wLineZero_mem R W ha)
  have hW2lt : valuation K (maximalIdeal R) (algebraMap R K (wParam R W hz₁)) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr (wParam_mem R W hz₁)
  refine wFunctionalEq_unique R W hZlt hW1lt hW2lt ?_ ?_
  · have h := congrArg (algebraMap R K) (wLineZero_functional_eq R W ha)
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h
  · have h := congrArg (algebraMap R K) (wParam_functional_eq R W hz₁)
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h

/-- **The chord line value at `z₂` is the coordinate expansion `wParam z₂`.** -/
theorem wLineOne_eq_wParam (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)
    (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal) :
    wLineOne R W ha = wParam R W hz₂ := by
  refine IsFractionRing.injective R K ?_
  have hZlt : valuation K (maximalIdeal R) (algebraMap R K z₂) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) z₂).mpr hz₂
  have hW1lt : valuation K (maximalIdeal R) (algebraMap R K (wLineOne R W ha)) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr (wLineOne_mem R W ha)
  have hW2lt : valuation K (maximalIdeal R) (algebraMap R K (wParam R W hz₂)) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr (wParam_mem R W hz₂)
  refine wFunctionalEq_unique R W hZlt hW1lt hW2lt ?_ ?_
  · have h := congrArg (algebraMap R K) (wLineOne_functional_eq R W ha)
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h
  · have h := congrArg (algebraMap R K) (wParam_functional_eq R W hz₂)
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h

end Numeric

end WeierstrassCurve
