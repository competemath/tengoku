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

/--
@isnad1 id=eq.0h5v.s8.9b19f217e25c from=translated src=- shape=9e52a7ac vocab=2fc9d742
-/
@[simp]
theorem mapRingHom_apply (f : R →+* S) (x : HahnSeries Γ R) : mapRingHom f x = x.map f := rfl

/--
@isnad1 id=eq.0h5v.s8.154f0b189481 from=translated src=- shape=238a95ae vocab=9042e2ac
-/
theorem mapRingHom_C (f : R →+* S) (r : R) :
    mapRingHom f (C r) = (C (f r) : HahnSeries Γ S) :=
  map_C r f

/--
@isnad1 id=eq.0h6v.s8.a633564cb975 from=translated src=- shape=13d310d8 vocab=7582d7af
-/
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

/-- The `z₂`-embedding sends the local parameter `X` to the outer variable `z₂`.
@isnad1 id=eq.0h2v.s8.442a4f071883 from=translated src=- shape=f25a3096 vocab=16debf1a
-/
theorem cLaurentRingHom_single_one :
    cLaurentRingHom R (HahnSeries.single (1 : ℤ) 1) = W.biZ₂ := by
  rw [cLaurentRingHom, HahnSeries.mapRingHom_single, map_one, biZ₂]

/-- The `z₂`-embedding fixes the constants: `ι₂ (C a) = C (C a)`.
@isnad1 id=eq.0h2v.s10.f0206880cf3a from=translated src=- shape=659d6847 vocab=966140e0
-/
theorem cLaurentRingHom_C (a : R) :
    cLaurentRingHom R (HahnSeries.C a) = HahnSeries.C (HahnSeries.C a : R⸨X⸩) := by
  rw [cLaurentRingHom, HahnSeries.mapRingHom_C]

/-- **Defining identity for `x₁`:** `x₁ · w₁ = z₁`.
@isnad1 id=eq.0h2v.s7.9d0240aeddc7 from=translated src=- shape=f34a5778 vocab=888f8f43
-/
theorem biX₁_mul_biW₁ : W.biX₁ * W.biW₁ = W.biZ₁ := by
  rw [biX₁, biW₁, biZ₁, ← map_mul, W.formalX_mul_coe_formalW]

/-- **Defining identity for `x₂`:** `x₂ · w₂ = z₂`.
@isnad1 id=eq.0h2v.s7.58ac2d03a4f7 from=translated src=- shape=f34a5778 vocab=e1c413ae
-/
theorem biX₂_mul_biW₂ : W.biX₂ * W.biW₂ = W.biZ₂ := by
  rw [biX₂, biW₂, ← map_mul, W.formalX_mul_coe_formalW, W.cLaurentRingHom_single_one]

/-- **Defining identity for `y₁`:** `y₁ · w₁ = -1`.
@isnad1 id=eq.0h2v.s8.d494cb8a26db from=translated src=- shape=a5bdeafe vocab=212f2adb
-/
theorem biY₁_mul_biW₁ : W.biY₁ * W.biW₁ = -1 := by
  rw [biY₁, biW₁, ← map_mul, W.formalY_mul_coe_formalW, map_neg, map_one]

/-- **Defining identity for `y₂`:** `y₂ · w₂ = -1`.
@isnad1 id=eq.0h2v.s8.5be688a21f4a from=translated src=- shape=a5bdeafe vocab=2954f999
-/
theorem biY₂_mul_biW₂ : W.biY₂ * W.biW₂ = -1 := by
  rw [biY₂, biW₂, ← map_mul, W.formalY_mul_coe_formalW, map_neg, map_one]

/-- The local parameter relation `z₁ · y₁ = -x₁`.
@isnad1 id=eq.0h2v.s8.f25596c4ae44 from=translated src=- shape=5dc151d9 vocab=530f2bfe
-/
theorem biZ₁_mul_biY₁ : W.biZ₁ * W.biY₁ = -W.biX₁ := by
  rw [biZ₁, biY₁, biX₁, ← map_mul, W.single_one_mul_formalY, map_neg]

/-- The local parameter relation `z₂ · y₂ = -x₂`.
@isnad1 id=eq.0h2v.s8.b8b99b08d397 from=translated src=- shape=5dc151d9 vocab=6affe33a
-/
theorem biZ₂_mul_biY₂ : W.biZ₂ * W.biY₂ = -W.biX₂ := by
  rw [biY₂, biX₂, ← W.cLaurentRingHom_single_one, ← map_mul, W.single_one_mul_formalY, map_neg]

/-- **The point-on-curve identity for `P₁ = (x₁, y₁)`** in `R⸨z₁⸩⸨z₂⸩`.
@isnad1 id=eq.0h2v.s12.91d03205558b from=translated src=- shape=999eccd5 vocab=fc10a28d
-/
theorem biX₁_biY₁_weierstrass :
    W.biY₁ ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₁ * W.biY₁
        + HahnSeries.C (HahnSeries.C W.a₃) * W.biY₁
      = W.biX₁ ^ 3 + HahnSeries.C (HahnSeries.C W.a₂) * W.biX₁ ^ 2
        + HahnSeries.C (HahnSeries.C W.a₄) * W.biX₁ + HahnSeries.C (HahnSeries.C W.a₆) := by
  have h := congrArg (cConstRingHom R) W.formalX_formalY_weierstrass
  simp only [map_add, map_mul, map_pow] at h
  exact h

/-- **The point-on-curve identity for `P₂ = (x₂, y₂)`** in `R⸨z₁⸩⸨z₂⸩`.
@isnad1 id=eq.0h2v.s12.667469eb8e14 from=translated src=- shape=999eccd5 vocab=eb63cc40
-/
theorem biX₂_biY₂_weierstrass :
    W.biY₂ ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂ * W.biY₂
        + HahnSeries.C (HahnSeries.C W.a₃) * W.biY₂
      = W.biX₂ ^ 3 + HahnSeries.C (HahnSeries.C W.a₂) * W.biX₂ ^ 2
        + HahnSeries.C (HahnSeries.C W.a₄) * W.biX₂ + HahnSeries.C (HahnSeries.C W.a₆) := by
  have h := congrArg (cLaurentRingHom R) W.formalX_formalY_weierstrass
  simp only [map_add, map_mul, map_pow, cLaurentRingHom_C] at h
  exact h

/-! ### The unit `x₂ - x₁` -/

/-- `w₁` and `w₂` are units of `R⸨z₁⸩⸨z₂⸩` (images of the unit `w` under a ring homomorphism).
@isnad1 id=isunit.0h2v.s6.979c3dcef9f8 from=translated src=- shape=f3151a31 vocab=e0ed3df4
-/
theorem isUnit_biW₁ : IsUnit W.biW₁ := W.isUnit_coe_formalW.map (cConstRingHom R)
/--
@isnad1 id=isunit.0h2v.s6.f335631c2e2f from=translated src=- shape=f3151a31 vocab=992b3225
-/
theorem isUnit_biW₂ : IsUnit W.biW₂ := W.isUnit_coe_formalW.map (cLaurentRingHom R)

/-- The `z₂`-coefficients of `x₂ = x(z₂)`: the `z₁`-constant coefficient `C (x(z)-coeff)`.
@isnad1 id=eq.0h3v.s7.6e88db185f4a from=translated src=- shape=eaaa5356 vocab=e58d03e6
-/
theorem coeff_biX₂ (g : ℤ) : W.biX₂.coeff g = HahnSeries.C (W.formalX.coeff g) := by
  rw [biX₂, cLaurentRingHom, HahnSeries.mapRingHom_apply, HahnSeries.map_coeff]

/-- The series `x₁ = x(z₁)` is supported in `z₂`-degree `0` only: off-degree coefficients vanish.
@isnad1 id=eq.1h3v.s6.c88a04965ad3 from=translated src=- shape=6dcc6b40 vocab=36ce3c98
-/
theorem coeff_biX₁_of_ne {g : ℤ} (h : g ≠ 0) : W.biX₁.coeff g = 0 := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

/-- The leading `z₂`-coefficient of `x₂ - x₁` is the unit `1`, at `z₂⁻²`.
@isnad1 id=eq.0h2v.s8.383541537ffa from=translated src=- shape=a6134059 vocab=659f5737
-/
theorem coeff_biX₂_sub_biX₁_neg_two : (W.biX₂ - W.biX₁).coeff (-2) = 1 := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_neg_two, W.coeff_biX₁_of_ne (by norm_num),
    sub_zero, map_one]

/-- `x₂ - x₁` has no `z₂`-terms below `z₂⁻²`.
@isnad1 id=eq.1h3v.s8.bb284b1c8a00 from=translated src=- shape=954bc76d vocab=abaff502
-/
theorem coeff_biX₂_sub_biX₁_of_lt {g : ℤ} (hg : g < -2) : (W.biX₂ - W.biX₁).coeff g = 0 := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, W.coeff_formalX_of_lt hg, map_zero,
    W.coeff_biX₁_of_ne (by omega), sub_zero]

/-- **The analytic key fact.** The divided-difference denominator `x₂ - x₁` is a unit of
`R⸨z₁⸩⸨z₂⸩`: its lowest `z₂`-term is `z₂⁻²` with the unit leading coefficient `1`. This is what
makes the slope `λ = (y₂ - y₁)·(x₂ - x₁)⁻¹` of the Weierstrass formal group law well-defined.
@isnad1 id=isunit.0h2v.s8.0611ce550632 from=translated src=- shape=0d6d0933 vocab=6eee0f23
-/
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
