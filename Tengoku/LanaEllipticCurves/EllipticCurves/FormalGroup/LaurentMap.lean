/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLawMap
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.FormalGroupLaurent
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PowerSeriesBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base-change naturality of the Laurent-side formal group law

For a ring homomorphism `f : R →+* S` and a Weierstrass curve `W : WeierstrassCurve R`, the
Weierstrass formal group law built inside the iterated Laurent ring
`R⸨z₁⸩⸨z₂⸩ := (R⸨X⸩)⸨X⸩ = HahnSeries ℤ (HahnSeries ℤ R)` commutes with base change:

`WeierstrassCurve.map_formalGroupLaurent` :
`Ψ f W.formalGroupLaurent = (W.map f).formalGroupLaurent`,

where `Ψ f := HahnSeries.mapRingHom (HahnSeries.mapRingHom f) : (R⸨X⸩)⸨X⸩ →+* (S⸨X⸩)⸨X⸩` is the
double base-change ring hom on the iterated Laurent ring and `W.map f : WeierstrassCurve S` is the
Mathlib base change of the curve (sending `aᵢ ↦ f W.aᵢ`).

This mirrors, on the *Laurent side*, the MvPowerSeries-side naturality of
`EllipticCurves.FormalGroup.GenuineLawMap`, and it is compatible with the writer
`HahnSeries.embedDoubleLaurent` (`HahnSeries.map_embedDoubleLaurent`): writing a bivariate power
series into the iterated Laurent ring commutes with base change.

## Strategy

Push `Ψ f` down the construction tower `w → x, y → x₁, x₂, y₁, y₂ → λ, ν → x₃, y₃ → F_E`. Every
layer is a ring-hom image except the Weierstrass expansion `w` and the two `Ring.inverse`
denominators:

* `map_formalW` (reused from `GenuineLawMap`) : the expansion is natural (uniqueness of the
  order-`≥ 1` fixed point of `wOp`).
* `PowerSeries.map_invOfUnit` : `PowerSeries.map f` commutes with `invOfUnit _ 1` at constant
  coefficient `1` (mirrors `WeierstrassCurve.map_invOfUnit`).
* `RingHom.map_ringInverse` : a ring hom commutes with `Ring.inverse` of a unit.
* everything else is pure functoriality of `HahnSeries.mapRingHom`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries PowerSeries

namespace RingHom

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A ring homomorphism commutes with `Ring.inverse` of a unit: `φ (u⁻¹) = (φ u)⁻¹`. Uniqueness of
the inverse (mirrors `WeierstrassCurve.map_invOfUnit`). -/
theorem map_ringInverse (φ : A →+* B) (u : A) (hu : IsUnit u) :
    φ (Ring.inverse u) = Ring.inverse (φ u) := by
  have h1 : φ u * φ (Ring.inverse u) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel u hu, map_one]
  have h2 : Ring.inverse (φ u) * φ u = 1 := Ring.inverse_mul_cancel _ (hu.map φ)
  calc φ (Ring.inverse u)
      = Ring.inverse (φ u) * φ u * φ (Ring.inverse u) := by rw [h2, one_mul]
    _ = Ring.inverse (φ u) * (φ u * φ (Ring.inverse u)) := by rw [mul_assoc]
    _ = Ring.inverse (φ u) := by rw [h1, mul_one]

end RingHom

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `PowerSeries.map f` commutes with `invOfUnit _ 1` when the constant coefficient is `1` (mirrors
`WeierstrassCurve.map_invOfUnit`, using that `map f` is a ring hom preserving the unit constant
coefficient). -/
theorem map_invOfUnit (f : R →+* S) (u : R⟦X⟧) (h : constantCoeff u = 1) :
    map f (invOfUnit u 1) = invOfUnit (map f u) 1 := by
  set T := (map f : R⟦X⟧ →+* S⟦X⟧) with hT
  have hval : constantCoeff u = ((1 : Rˣ) : R) := by rw [h, Units.val_one]
  have hsval : constantCoeff (T u) = ((1 : Sˣ) : S) := by
    rw [hT, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      h, map_one, Units.val_one]
  have h1 : T u * T (invOfUnit u 1) = 1 := by
    rw [hT, ← map_mul, mul_invOfUnit u 1 hval, map_one]
  have h2 : invOfUnit (T u) 1 * T u = 1 := invOfUnit_mul _ 1 hsval
  calc T (invOfUnit u 1)
      = invOfUnit (T u) 1 * T u * T (invOfUnit u 1) := by rw [h2, one_mul]
    _ = invOfUnit (T u) 1 * (T u * T (invOfUnit u 1)) := by rw [mul_assoc]
    _ = invOfUnit (T u) 1 := by rw [h1, mul_one]

end PowerSeries

namespace HahnSeries

variable {Γ R S : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [CommRing S]

/-! ### Generic naturality of `mapRingHom` -/

/-- `mapRingHom` composes: applying two coefficient ring homs in succession is applying the
composite. -/
theorem mapRingHom_mapRingHom {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : HahnSeries Γ R) : mapRingHom g (mapRingHom f x) = mapRingHom (g.comp f) x := by
  ext a
  simp only [mapRingHom_apply, map_coeff, RingHom.comp_apply]

/-- `mapRingHom f` commutes with the coercion of a power series into the Laurent series ring:
`mapRingHom f ↑p = ↑(PowerSeries.map f p)`. -/
theorem mapRingHom_ofPowerSeries (f : R →+* S) (p : R⟦X⟧) :
    mapRingHom f (ofPowerSeries ℤ R p) = ofPowerSeries ℤ S (PowerSeries.map f p) := by
  ext n
  rw [mapRingHom_apply, map_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [WeierstrassCurve.coe_powerSeries_coeff_of_neg p hn,
      WeierstrassCurve.coe_powerSeries_coeff_of_neg (PowerSeries.map f p) hn, map_zero]
  · lift n to ℕ using hn with k
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

/-- The `z₁`-embedding `HahnSeries.C : R⸨X⸩ →+* (R⸨X⸩)⸨X⸩` intertwines base change with
`mapRingHom`: `(mapRingHom f) ∘ C = C ∘ f` (i.e. `C (f r) = mapRingHom f (C r)`). -/
theorem mapRingHom_C_comp (f : R →+* S) :
    (mapRingHom f : R⸨X⸩ →+* S⸨X⸩).comp (HahnSeries.C : R →+* R⸨X⸩)
      = (HahnSeries.C : S →+* S⸨X⸩).comp f := by
  ext r
  simp only [RingHom.comp_apply, mapRingHom_C]

/-! ### Naturality of the writer `embedDoubleLaurent` -/

/-- **Base-change naturality of the writer.** Writing a bivariate power series into the iterated
Laurent ring commutes with base change:
`Ψ f (embedDoubleLaurent φ) = embedDoubleLaurent (MvPowerSeries.map f φ)`. Both sides have
`z₁^m z₂^n`-coefficient `f (MvPowerSeries.coeff (single 0 m + single 1 n) φ)`. -/
theorem map_embedDoubleLaurent (f : R →+* S) (φ : MvPowerSeries (Fin 2) R) :
    mapRingHom (mapRingHom f) (embedDoubleLaurent φ)
      = embedDoubleLaurent (MvPowerSeries.map f φ) := by
  rw [embedDoubleLaurent, embedDoubleLaurent, mapRingHom_ofPowerSeries]
  refine congrArg _ (PowerSeries.ext fun n => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, mapRingHom_ofPowerSeries]
  refine congrArg _ (PowerSeries.ext fun m => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, MvPowerSeries.coeff_map]

end HahnSeries

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Naturality of the two embeddings `ι₁, ι₂` -/

/-- The `z₁`-embedding `ι₁ = cConstRingHom` is natural: `Ψ f (ι₁ g) = ι₁ (mapRingHom f g)`. -/
theorem map_cConstRingHom (f : R →+* S) (g : R⸨X⸩) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) (cConstRingHom R g)
      = cConstRingHom S (HahnSeries.mapRingHom f g) :=
  HahnSeries.mapRingHom_C (HahnSeries.mapRingHom f) g

/-- The `z₂`-embedding `ι₂ = cLaurentRingHom` is natural: `Ψ f (ι₂ g) = ι₂ (mapRingHom f g)`. -/
theorem map_cLaurentRingHom (f : R →+* S) (g : R⸨X⸩) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) (cLaurentRingHom R g)
      = cLaurentRingHom S (HahnSeries.mapRingHom f g) := by
  unfold cLaurentRingHom
  rw [HahnSeries.mapRingHom_mapRingHom, HahnSeries.mapRingHom_mapRingHom,
    HahnSeries.mapRingHom_C_comp]

variable (W : WeierstrassCurve R)

/-! ### Naturality of the coordinate Laurent series -/

/-- Naturality of the cofactor `v`: `PowerSeries.map f W.wCofactor = (W.map f).wCofactor`. -/
theorem map_wCofactor (f : R →+* S) :
    PowerSeries.map f W.wCofactor = (W.map f).wCofactor := by
  ext n
  rw [PowerSeries.coeff_map, W.coeff_wCofactor, (W.map f).coeff_wCofactor, ← W.map_formalW f,
    PowerSeries.coeff_map]

/-- Naturality of the coerced expansion: `mapRingHom f (W.formalW : R⸨X⸩) = ((W.map f).formalW)`. -/
theorem map_coe_formalW (f : R →+* S) :
    HahnSeries.mapRingHom f (W.formalW : R⸨X⸩) = ((W.map f).formalW : S⸨X⸩) := by
  rw [HahnSeries.mapRingHom_ofPowerSeries, W.map_formalW f]

/-- Naturality of the coordinate series `x(z)`: `mapRingHom f W.formalX = (W.map f).formalX`. -/
theorem map_formalX (f : R →+* S) :
    HahnSeries.mapRingHom f W.formalX = (W.map f).formalX := by
  rw [formalX, formalX, map_mul, HahnSeries.mapRingHom_single, map_one,
    HahnSeries.mapRingHom_ofPowerSeries,
    PowerSeries.map_invOfUnit f W.wCofactor W.constantCoeff_wCofactor, W.map_wCofactor f]

/-- Naturality of the coordinate series `y(z)`: `mapRingHom f W.formalY = (W.map f).formalY`. -/
theorem map_formalY (f : R →+* S) :
    HahnSeries.mapRingHom f W.formalY = (W.map f).formalY := by
  rw [formalY, formalY, map_mul, HahnSeries.mapRingHom_single, map_neg, map_one,
    HahnSeries.mapRingHom_ofPowerSeries,
    PowerSeries.map_invOfUnit f W.wCofactor W.constantCoeff_wCofactor, W.map_wCofactor f]

/-! ### Naturality of the bivariate coordinates -/

/-- Naturality of `x₁ = x(z₁)`. -/
theorem map_biX₁ (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.biX₁ = (W.map f).biX₁ := by
  rw [biX₁, biX₁, map_cConstRingHom, W.map_formalX f]

/-- Naturality of `x₂ = x(z₂)`. -/
theorem map_biX₂ (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.biX₂ = (W.map f).biX₂ := by
  rw [biX₂, biX₂, map_cLaurentRingHom, W.map_formalX f]

/-- Naturality of `y₁ = y(z₁)`. -/
theorem map_biY₁ (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.biY₁ = (W.map f).biY₁ := by
  rw [biY₁, biY₁, map_cConstRingHom, W.map_formalY f]

/-- Naturality of `y₂ = y(z₂)`. -/
theorem map_biY₂ (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.biY₂ = (W.map f).biY₂ := by
  rw [biY₂, biY₂, map_cLaurentRingHom, W.map_formalY f]

/-- Naturality of the inner variable `z₁`. -/
theorem map_biZ₁ (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.biZ₁ = (W.map f).biZ₁ := by
  rw [biZ₁, biZ₁, map_cConstRingHom, HahnSeries.mapRingHom_single, map_one]

/-- Naturality of the outer variable `z₂`. -/
theorem map_biZ₂ (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.biZ₂ = (W.map f).biZ₂ := by
  rw [biZ₂, biZ₂, HahnSeries.mapRingHom_single, map_one]

/-! ### Naturality of the addition-law data -/

/-- Naturality of the slope `λ = (y₂ − y₁)·(x₂ − x₁)⁻¹`. -/
theorem map_formalLambda (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.formalLambda = (W.map f).formalLambda := by
  rw [formalLambda, formalLambda, map_mul, map_sub, W.map_biY₂ f, W.map_biY₁ f,
    RingHom.map_ringInverse _ _ W.isUnit_biX₂_sub_biX₁, map_sub, W.map_biX₂ f, W.map_biX₁ f]

/-- Naturality of the intercept `ν = y₁ − λ·x₁`. -/
theorem map_formalNu (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.formalNu = (W.map f).formalNu := by
  rw [formalNu, formalNu, map_sub, map_mul, W.map_biY₁ f, W.map_formalLambda f, W.map_biX₁ f]

/-- Naturality of the third `x`-coordinate `x₃ = λ² + a₁λ − a₂ − x₁ − x₂`. -/
theorem map_formalXThree (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.formalXThree = (W.map f).formalXThree := by
  rw [formalXThree, formalXThree]
  simp only [map_add, map_sub, map_mul, map_pow, HahnSeries.mapRingHom_C, W.map_formalLambda f,
    W.map_biX₁ f, W.map_biX₂ f, map_a₁, map_a₂]

/-- Naturality of the third `y`-coordinate `y₃ = −(λx₃ + ν) − a₁x₃ − a₃`. -/
theorem map_formalYThree (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.formalYThree = (W.map f).formalYThree := by
  rw [formalYThree, formalYThree]
  simp only [map_neg, map_add, map_sub, map_mul, HahnSeries.mapRingHom_C, W.map_formalLambda f,
    W.map_formalXThree f, W.map_formalNu f, map_a₁, map_a₃]

/-! ### Base-change naturality of the Laurent formal group law -/

/-- **Base-change naturality of the Weierstrass formal group law.**
`Ψ f W.formalGroupLaurent = (W.map f).formalGroupLaurent`. -/
theorem map_formalGroupLaurent (f : R →+* S) :
    HahnSeries.mapRingHom (HahnSeries.mapRingHom f) W.formalGroupLaurent
      = (W.map f).formalGroupLaurent := by
  rw [formalGroupLaurent, formalGroupLaurent, map_mul, map_neg, W.map_formalXThree f,
    RingHom.map_ringInverse _ _ W.isUnit_formalYThree, W.map_formalYThree f]

end WeierstrassCurve
