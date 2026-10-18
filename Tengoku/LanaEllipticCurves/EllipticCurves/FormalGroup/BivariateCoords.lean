/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.CoordinateSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The bivariate coordinate series in the iterated Laurent ring `R⸨z₁⸩⸨z₂⸩`

Building on the single-variable coordinate Laurent series `x(z), y(z) ∈ R⸨X⸩` of
`EllipticCurves.FormalGroup.CoordinateSeries`, this file sets up the two-variable infrastructure
underlying the Weierstrass formal group law, working in the **iterated Laurent ring**
`R⸨z₁⸩⸨z₂⸩ := LaurentSeries (LaurentSeries R) = HahnSeries ℤ (HahnSeries ℤ R)` (Silverman,
*The Arithmetic of Elliptic Curves*, IV.1).

Two copies of the single-variable coordinate ring `R⸨X⸩` are embedded:

* the **`z₁`-embedding** `ι₁ := HahnSeries.C`, sending `R⸨X⸩` into the coefficient ring, i.e. a
  series that is *constant in `z₂`* — the inner variable `z₁`;
* the **`z₂`-embedding** `ι₂ := WeierstrassCurve.cLaurentRingHom`, applying `HahnSeries.C`
  coefficientwise — the outer variable `z₂`.

Under these the single-variable identities (`x·w = z`, `y·w = -1`, `z·y = -x`, and the
point-on-curve equation) transport to the two points `P₁ = (x₁, y₁)` and `P₂ = (x₂, y₂)`.
Finally the analytic key fact `IsUnit (x₂ - x₁)` is proved: its lowest `z₂`-term is `z₂⁻²` with the
unit leading coefficient `1`, so the divided difference `λ = (y₂-y₁)/(x₂-x₁)` of the sibling issue
is well-defined.

## Main definitions

* `HahnSeries.mapRingHom` : the ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` induced by a coefficient ring
  homomorphism `R →+* S`.
* `WeierstrassCurve.cLaurentRingHom` : the `z₂`-embedding `R⸨X⸩ →+* R⸨z₁⸩⸨z₂⸩`.
* `WeierstrassCurve.biX₁`, `biX₂`, `biY₁`, `biY₂`, `biW₁`, `biW₂` : the coordinate series of the
  two points and the Weierstrass expansions in `R⸨z₁⸩⸨z₂⸩`.

## Main results

* `WeierstrassCurve.biX₁_mul_biW₁`, `biX₂_mul_biW₂`, `biY₁_mul_biW₁`, `biY₂_mul_biW₂` : the
  defining identities `xᵢ·wᵢ = zᵢ`, `yᵢ·wᵢ = -1`.
* `WeierstrassCurve.biX₁_biY₁_weierstrass`, `biX₂_biY₂_weierstrass` : the point-on-curve identity
  for `P₁` and `P₂`.
* `WeierstrassCurve.isUnit_biX₂_sub_biX₁` : `x₂ - x₁` is a unit of `R⸨z₁⸩⸨z₂⸩`.

## ⚠️ Two `@[simp]` attributes were removed here, and the lemmas kept (`#1278`)

`HahnSeries.mapRingHom_single` and `HahnSeries.mapRingHom_C` carried `@[simp]` and **neither could
ever fire**: `HahnSeries.mapRingHom_apply` is itself `@[simp]` and unfolds `mapRingHom f x` to
`x.map f`, so the head of both patterns is gone before they are tried. Measured with Mathlib's
`simpNF` environment linter, which had never been run on this tree. Both are still named rewrites
with consumers here and in `EllipticCurves.FormalGroup.LaurentMap`; only the attribute went.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

open scoped LaurentSeries

namespace HahnSeries

variable {Γ R S : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [CommRing S]

/-- The ring homomorphism `R⟦Γ⟧ →+* S⟦Γ⟧` obtained by applying a coefficient ring homomorphism
`f : R →+* S` to every coefficient. -/
noncomputable def mapRingHom (f : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toAddMonoidHom.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

@[simp]
theorem mapRingHom_apply (f : R →+* S) (x : HahnSeries Γ R) : mapRingHom f x = x.map f := rfl

theorem mapRingHom_C (f : R →+* S) (r : R) :
    mapRingHom f (C r) = (C (f r) : HahnSeries Γ S) :=
  map_C r f

theorem mapRingHom_single (f : R →+* S) (a : Γ) (r : R) :
    mapRingHom f (single a r) = single a (f r) :=
  HahnSeries.map_single f.toAddMonoidHom.toZeroHom

end HahnSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

variable (R) in
/-- The `z₂`-embedding `R⸨X⸩ →+* R⸨z₁⸩⸨z₂⸩`: apply `HahnSeries.C : R →+* R⸨X⸩` to every
coefficient, sending the Laurent variable `X` to the outer variable `z₂`. -/
noncomputable def cLaurentRingHom : R⸨X⸩ →+* (R⸨X⸩)⸨X⸩ :=
  HahnSeries.mapRingHom (HahnSeries.C : R →+* R⸨X⸩)

variable (R) in
/-- The `z₁`-embedding `R⸨X⸩ →+* R⸨z₁⸩⸨z₂⸩`: the constant embedding into the coefficient ring. -/
noncomputable abbrev cConstRingHom : R⸨X⸩ →+* (R⸨X⸩)⸨X⸩ :=
  HahnSeries.C

/-! ### The two-variable coordinates -/

/-- `x₁ = x(z₁) ∈ R⸨z₁⸩⸨z₂⸩`, constant in `z₂`. -/
noncomputable def biX₁ : (R⸨X⸩)⸨X⸩ := cConstRingHom R W.formalX
/-- `x₂ = x(z₂) ∈ R⸨z₁⸩⸨z₂⸩`. -/
noncomputable def biX₂ : (R⸨X⸩)⸨X⸩ := cLaurentRingHom R W.formalX
/-- `y₁ = y(z₁) ∈ R⸨z₁⸩⸨z₂⸩`, constant in `z₂`. -/
noncomputable def biY₁ : (R⸨X⸩)⸨X⸩ := cConstRingHom R W.formalY
/-- `y₂ = y(z₂) ∈ R⸨z₁⸩⸨z₂⸩`. -/
noncomputable def biY₂ : (R⸨X⸩)⸨X⸩ := cLaurentRingHom R W.formalY
/-- `w₁ = w(z₁) ∈ R⸨z₁⸩⸨z₂⸩`, constant in `z₂`. -/
noncomputable def biW₁ : (R⸨X⸩)⸨X⸩ := cConstRingHom R (W.formalW : R⸨X⸩)
/-- `w₂ = w(z₂) ∈ R⸨z₁⸩⸨z₂⸩`. -/
noncomputable def biW₂ : (R⸨X⸩)⸨X⸩ := cLaurentRingHom R (W.formalW : R⸨X⸩)

/-- The inner variable `z₁ ∈ R⸨z₁⸩⸨z₂⸩`. -/
noncomputable def biZ₁ (_W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  cConstRingHom R (HahnSeries.single (1 : ℤ) 1)
/-- The outer variable `z₂ ∈ R⸨z₁⸩⸨z₂⸩`. -/
noncomputable def biZ₂ (_W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ := HahnSeries.single (1 : ℤ) 1

/-! ### Transported coordinate identities -/

/-- The `z₂`-embedding sends the local parameter `X` to the outer variable `z₂`. -/
theorem cLaurentRingHom_single_one :
    cLaurentRingHom R (HahnSeries.single (1 : ℤ) 1) = W.biZ₂ := by
  rw [cLaurentRingHom, HahnSeries.mapRingHom_single, map_one, biZ₂]

/-- The `z₂`-embedding fixes the constants: `ι₂ (C a) = C (C a)`. -/
theorem cLaurentRingHom_C (a : R) :
    cLaurentRingHom R (HahnSeries.C a) = HahnSeries.C (HahnSeries.C a : R⸨X⸩) := by
  rw [cLaurentRingHom, HahnSeries.mapRingHom_C]

/-- **Defining identity for `x₁`:** `x₁ · w₁ = z₁`. -/
theorem biX₁_mul_biW₁ : W.biX₁ * W.biW₁ = W.biZ₁ := by
  rw [biX₁, biW₁, biZ₁, ← map_mul, W.formalX_mul_coe_formalW]

/-- **Defining identity for `x₂`:** `x₂ · w₂ = z₂`. -/
theorem biX₂_mul_biW₂ : W.biX₂ * W.biW₂ = W.biZ₂ := by
  rw [biX₂, biW₂, ← map_mul, W.formalX_mul_coe_formalW, W.cLaurentRingHom_single_one]

/-- **Defining identity for `y₁`:** `y₁ · w₁ = -1`. -/
theorem biY₁_mul_biW₁ : W.biY₁ * W.biW₁ = -1 := by
  rw [biY₁, biW₁, ← map_mul, W.formalY_mul_coe_formalW, map_neg, map_one]

/-- **Defining identity for `y₂`:** `y₂ · w₂ = -1`. -/
theorem biY₂_mul_biW₂ : W.biY₂ * W.biW₂ = -1 := by
  rw [biY₂, biW₂, ← map_mul, W.formalY_mul_coe_formalW, map_neg, map_one]

/-- The local parameter relation `z₁ · y₁ = -x₁`. -/
theorem biZ₁_mul_biY₁ : W.biZ₁ * W.biY₁ = -W.biX₁ := by
  rw [biZ₁, biY₁, biX₁, ← map_mul, W.single_one_mul_formalY, map_neg]

/-- The local parameter relation `z₂ · y₂ = -x₂`. -/
theorem biZ₂_mul_biY₂ : W.biZ₂ * W.biY₂ = -W.biX₂ := by
  rw [biY₂, biX₂, ← W.cLaurentRingHom_single_one, ← map_mul, W.single_one_mul_formalY, map_neg]

/-- **The point-on-curve identity for `P₁ = (x₁, y₁)`** in `R⸨z₁⸩⸨z₂⸩`. -/
theorem biX₁_biY₁_weierstrass :
    W.biY₁ ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₁ * W.biY₁
        + HahnSeries.C (HahnSeries.C W.a₃) * W.biY₁
      = W.biX₁ ^ 3 + HahnSeries.C (HahnSeries.C W.a₂) * W.biX₁ ^ 2
        + HahnSeries.C (HahnSeries.C W.a₄) * W.biX₁ + HahnSeries.C (HahnSeries.C W.a₆) := by
  have h := congrArg (cConstRingHom R) W.formalX_formalY_weierstrass
  simp only [map_add, map_mul, map_pow] at h
  exact h

/-- **The point-on-curve identity for `P₂ = (x₂, y₂)`** in `R⸨z₁⸩⸨z₂⸩`. -/
theorem biX₂_biY₂_weierstrass :
    W.biY₂ ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂ * W.biY₂
        + HahnSeries.C (HahnSeries.C W.a₃) * W.biY₂
      = W.biX₂ ^ 3 + HahnSeries.C (HahnSeries.C W.a₂) * W.biX₂ ^ 2
        + HahnSeries.C (HahnSeries.C W.a₄) * W.biX₂ + HahnSeries.C (HahnSeries.C W.a₆) := by
  have h := congrArg (cLaurentRingHom R) W.formalX_formalY_weierstrass
  simp only [map_add, map_mul, map_pow, cLaurentRingHom_C] at h
  exact h

/-! ### The unit `x₂ - x₁` -/

/-- `w₁` and `w₂` are units of `R⸨z₁⸩⸨z₂⸩` (images of the unit `w` under a ring homomorphism). -/
theorem isUnit_biW₁ : IsUnit W.biW₁ := W.isUnit_coe_formalW.map (cConstRingHom R)
theorem isUnit_biW₂ : IsUnit W.biW₂ := W.isUnit_coe_formalW.map (cLaurentRingHom R)

/-- The `z₂`-coefficients of `x₂ = x(z₂)`: the `z₁`-constant coefficient `C (x(z)-coeff)`. -/
theorem coeff_biX₂ (g : ℤ) : W.biX₂.coeff g = HahnSeries.C (W.formalX.coeff g) := by
  rw [biX₂, cLaurentRingHom, HahnSeries.mapRingHom_apply, HahnSeries.map_coeff]

/-- The series `x₁ = x(z₁)` is supported in `z₂`-degree `0` only: off-degree coefficients vanish. -/
theorem coeff_biX₁_of_ne {g : ℤ} (h : g ≠ 0) : W.biX₁.coeff g = 0 := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

/-- The leading `z₂`-coefficient of `x₂ - x₁` is the unit `1`, at `z₂⁻²`. -/
theorem coeff_biX₂_sub_biX₁_neg_two : (W.biX₂ - W.biX₁).coeff (-2) = 1 := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_neg_two, W.coeff_biX₁_of_ne (by norm_num),
    sub_zero, map_one]

/-- `x₂ - x₁` has no `z₂`-terms below `z₂⁻²`. -/
theorem coeff_biX₂_sub_biX₁_of_lt {g : ℤ} (hg : g < -2) : (W.biX₂ - W.biX₁).coeff g = 0 := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, W.coeff_formalX_of_lt hg, map_zero,
    W.coeff_biX₁_of_ne (by omega), sub_zero]

/-- **The analytic key fact.** The divided-difference denominator `x₂ - x₁` is a unit of
`R⸨z₁⸩⸨z₂⸩`: its lowest `z₂`-term is `z₂⁻²` with the unit leading coefficient `1`. This is what
makes the slope `λ = (y₂ - y₁)·(x₂ - x₁)⁻¹` of the Weierstrass formal group law well-defined. -/
theorem isUnit_biX₂_sub_biX₁ : IsUnit (W.biX₂ - W.biX₁) := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton _
  · set d := W.biX₂ - W.biX₁ with hd
    have hlead : d.coeff (-2) = 1 := W.coeff_biX₂_sub_biX₁_neg_two
    have hne : d ≠ 0 := by
      intro h; rw [h, HahnSeries.coeff_zero] at hlead; exact one_ne_zero hlead.symm
    have hle : d.order ≤ -2 :=
      HahnSeries.order_le_of_coeff_ne_zero (by rw [hlead]; exact one_ne_zero)
    have hge : (-2 : ℤ) ≤ d.order := by
      by_contra hlt
      exact HahnSeries.coeff_order_eq_zero.not.2 hne (W.coeff_biX₂_sub_biX₁_of_lt (not_le.mp hlt))
    have horder : d.order = -2 := le_antisymm hle hge
    refine HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [HahnSeries.leadingCoeff_eq, horder, hlead]; exact isUnit_one
    · rw [horder]; exact AddGroup.isAddUnit _

end WeierstrassCurve
