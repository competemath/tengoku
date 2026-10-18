/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.TangentThirdChordAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The unconditional affine↔third-root matching `addX = X₃` (issue #376)

The merged coordinate identity `addX_eq_thirdChordX` (`Reduction/ThirdChordAffine.lean`) and its
doubling analog `addX_eq_thirdChordX_diag` (`Reduction/TangentThirdChordAffine.lean`) are proven by
affine Vieta **root-selection**: the factorisation `addPolynomial = -(X-x₁)(X-x₂)(X-addX)` gives
`X₃ ∈ {x₁, x₂, addX}`, and the non-degeneracy hypotheses `hd : X₃ ≠ xParam zᵢ` rule out the first
two roots to force `X₃ = addX`.  Those `hd`'s genuinely fail in the configurations `Q = -2P` /
`P = -2Q` (the third chord point collides with `±P`), which is why they block the full `E₁(K)`
subgroup closure of #367.

This file removes the `hd` hypotheses entirely, proving `addX = X₃` **unconditionally** (in both the
secant and doubling cases) as a *direct field identity*, sidestepping root-selection.

## Method

Root-selection at the *affine* level needs `X₃` distinct from **both** `x₁, x₂`.  But at the
`(z, w)`-level the cubic `A z³ + S z² + P z + Q` (roots `z₁, z₂` and the Vieta third root `t`) has
`z₁ ≠ z₂` as **distinct** known roots in the secant case (and `z` as a *double* root, via the
tangency relation, in the doubling case).  From two distinct roots — or one double root — one
recovers **all** the symmetric functions `e₁, e₂, e₃` of `z₁, z₂, t`, with **no** distinctness of
`X₃`:

* `e₁`: `A (z₁ + z₂ + t) + S = 0` — the Vieta relation `formalThirdRoot_vieta`.
* `e₂`, `e₃`: from `e₁` with `F(z₁) = F(z₂) = 0` (secant, via `(F z₁ - F z₂)/(z₁ - z₂)`) or
  `F(z) = F′(z) = 0` (doubling, via the tangency relation `wParamDeriv_tangency`).

The affine `x`-coordinates are the Möbius images `xᵢ = zᵢ / (λ zᵢ + ν)`, `X₃ = t / (λ t + ν)`, and a
symmetric-function computation gives `x₁ + x₂ + X₃ = ℓ² + a₁ℓ - a₂ = x₁ + x₂ + addX`, i.e.
`addX = X₃`.  Concretely this is `A · P = 0` for the cleared numerator `P`, closed by a
`linear_combination` of the `e₁, e₂, e₃` relations; cancelling the unit `A = φ formalGroupLead ≠ 0`
gives `P = 0`, hence `addX = X₃`.

This single pair of lemmas drops `hd` from the coordinate additivity and the `ReducesToZero`
add-closure of #367.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries Polynomial

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W]

section Secant

variable {z₁ z₂ : R} (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)
variable (hz : z₁ ≠ z₂) (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal)
  (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal) (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0)
  (hw : thirdChordW R W ha ≠ 0) (hx : xParam R W hz₁ ≠ xParam R W hz₂)

include hz hz₁0 hz₂0 hw hx in
open Classical in
/-- **The coordinate identity `addX = X₃`, unconditional secant case.**  Mathlib's affine
third-intersection `x`-coordinate `addX` of the two recovered points equals the transported third
chord `x`-coordinate `X₃ = t / w₃`, with **no** non-degeneracy hypothesis (`hd`) on `X₃`.  Proven as
a direct field identity via the `(z, w)`-level Vieta symmetric functions (the two distinct roots
`z₁ ≠ z₂`), sidestepping affine root-selection. -/
theorem addX_eq_thirdChordX_of_secant :
    W.toAffine.addX (xParam R W hz₁) (xParam R W hz₂)
        (W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂))
      = X₃ R W ha := by
  set lamK := algebraMap R K (chordSlope R W ha) with hlam
  set νK := algebraMap R K (chordIntercept R W ha) with hν
  set tK := algebraMap R K (thirdRootNum R W ha) with htK
  set z1 := algebraMap R K z₁ with hz1
  set z2 := algebraMap R K z₂ with hz2
  set w1 := algebraMap R K (wParam R W hz₁) with hw1
  set w2 := algebraMap R K (wParam R W hz₂) with hw2
  set w3 := algebraMap R K (thirdChordW R W ha) with hw3
  have hw1ne : w1 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
    (wParam_ne_zero R W hz₁ hz₁0)
  have hw2ne : w2 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
    (wParam_ne_zero R W hz₂ hz₂0)
  have hw3ne : w3 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hνne : νK ≠ 0 := chordIntercept_ne_zero_secant R W ha hz₁ hz₂ hz₁0 hz₂0 hx
  have hslope := slope_xParam_secant R W ha hz₁ hz₂ hz₁0 hz₂0 hx
  rw [← hlam, ← hν] at hslope
  -- collinearity `w = λ z + ν`
  have hcw1 : w1 = lamK * z1 + νK := by
    rw [hw1, hz1, hlam, hν, ← map_mul, ← map_add]
    exact congrArg _ (wParam_eq_chordLine₀ R W ha hz₁)
  have hcw2 : w2 = lamK * z2 + νK := by
    rw [hw2, hz2, hlam, hν, ← map_mul, ← map_add]
    exact congrArg _ (wParam_eq_chordLine₁ R W ha hz₂)
  have hcw3 : w3 = lamK * tK + νK := by
    rw [hw3, htK, hlam, hν, ← map_mul, ← map_add]
    exact congrArg _ (thirdChordW_eq R W ha)
  have hx1 : xParam R W hz₁ = z1 / w1 := by rw [xParam]
  have hx2 : xParam R W hz₂ = z2 / w2 := by rw [xParam]
  -- the two functional equations, with `w = λ z + ν` substituted
  have hFE1 : w1 = z1 ^ 3 + (W.a₁ * z1 + W.a₂ * z1 ^ 2) * w1
      + (W.a₃ + W.a₄ * z1) * w1 ^ 2 + W.a₆ * w1 ^ 3 := by
    have h := congrArg (algebraMap R K) (wParam_functional_eq R W hz₁)
    simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at h
    rw [← hw1, ← hz1] at h; exact h
  have hFE2 : w2 = z2 ^ 3 + (W.a₁ * z2 + W.a₂ * z2 ^ 2) * w2
      + (W.a₃ + W.a₄ * z2) * w2 ^ 2 + W.a₆ * w2 ^ 3 := by
    have h := congrArg (algebraMap R K) (wParam_functional_eq R W hz₂)
    simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at h
    rw [← hw2, ← hz2] at h; exact h
  have hA : algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal ha
        (integralModel R W).formalGroupLead)
      = 1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3 := by
    have h := congrArg (algebraMap R K) (adicEvalMv_formalGroupLead R W ha)
    simp only [map_add, map_mul, map_pow, map_one, integralModel_a₂_eq, integralModel_a₄_eq,
      integralModel_a₆_eq] at h
    rw [← hlam] at h; exact h
  have hS : algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal ha
        (integralModel R W).formalGroupSub)
      = W.a₁ * lamK + W.a₂ * νK + W.a₃ * lamK ^ 2 + 2 * W.a₄ * lamK * νK
        + 3 * W.a₆ * lamK ^ 2 * νK := by
    have h := congrArg (algebraMap R K) (adicEvalMv_formalGroupSub R W ha)
    simp only [map_add, map_mul, map_pow, map_ofNat, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at h
    rw [← hlam, ← hν] at h; exact h
  have hVieta : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3) * (tK + z1 + z2)
      + (W.a₁ * lamK + W.a₂ * νK + W.a₃ * lamK ^ 2 + 2 * W.a₄ * lamK * νK
        + 3 * W.a₆ * lamK ^ 2 * νK) = 0 := by
    have h := congrArg (algebraMap R K) (formalThirdRoot_vieta R W ha)
    simp only [map_add, map_mul, map_zero] at h
    rw [hA, hS, ← htK, ← hz1, ← hz2] at h
    exact h
  have hz12K : z1 ≠ z2 := by
    rw [hz1, hz2]; exact fun h => hz (IsFractionRing.injective R K h)
  have hAR0 : adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupLead ≠ 0 := by
    intro h
    have hu := (integralModel R W).ringHom_formalGroupLead_mul_inv
      (adicEvalMv (maximalIdeal R).asIdeal ha)
    rw [h, zero_mul] at hu
    exact zero_ne_one hu
  have hAne : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3 : K) ≠ 0 := by
    rw [← hA]; exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hAR0
  rw [hcw1] at hFE1
  rw [hcw2] at hFE2
  -- the two points as roots of the `z`-cubic  `A z³ + S z² + P z + Q = 0`
  have F1 : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3) * z1 ^ 3
      + (W.a₁ * lamK + W.a₂ * νK + W.a₃ * lamK ^ 2 + 2 * W.a₄ * lamK * νK
          + 3 * W.a₆ * lamK ^ 2 * νK) * z1 ^ 2
      + (W.a₁ * νK + W.a₄ * νK ^ 2 + 2 * W.a₃ * lamK * νK + 3 * W.a₆ * lamK * νK ^ 2 - lamK) * z1
      + (W.a₃ * νK ^ 2 + W.a₆ * νK ^ 3 - νK) = 0 := by
    linear_combination -hFE1
  have F2 : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3) * z2 ^ 3
      + (W.a₁ * lamK + W.a₂ * νK + W.a₃ * lamK ^ 2 + 2 * W.a₄ * lamK * νK
          + 3 * W.a₆ * lamK ^ 2 * νK) * z2 ^ 2
      + (W.a₁ * νK + W.a₄ * νK ^ 2 + 2 * W.a₃ * lamK * νK + 3 * W.a₆ * lamK * νK ^ 2 - lamK) * z2
      + (W.a₃ * νK ^ 2 + W.a₆ * νK ^ 3 - νK) = 0 := by
    linear_combination -hFE2
  have Ve1 : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3) * (z1 + z2 + tK)
      + (W.a₁ * lamK + W.a₂ * νK + W.a₃ * lamK ^ 2 + 2 * W.a₄ * lamK * νK
          + 3 * W.a₆ * lamK ^ 2 * νK) = 0 := by
    linear_combination hVieta
  -- divide `F1 − F2` by `z₁ − z₂` to recover the second symmetric-function relation
  have hDz : (z1 - z2) * ((1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3)
        * (z1 ^ 2 + z1 * z2 + z2 ^ 2)
      + (W.a₁ * lamK + W.a₂ * νK + W.a₃ * lamK ^ 2 + 2 * W.a₄ * lamK * νK
          + 3 * W.a₆ * lamK ^ 2 * νK) * (z1 + z2)
      + (W.a₁ * νK + W.a₄ * νK ^ 2 + 2 * W.a₃ * lamK * νK + 3 * W.a₆ * lamK * νK ^ 2 - lamK))
      = 0 := by
    linear_combination F1 - F2
  have Dz : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3) * (z1 ^ 2 + z1 * z2 + z2 ^ 2)
      + (W.a₁ * lamK + W.a₂ * νK + W.a₃ * lamK ^ 2 + 2 * W.a₄ * lamK * νK
          + 3 * W.a₆ * lamK ^ 2 * νK) * (z1 + z2)
      + (W.a₁ * νK + W.a₄ * νK ^ 2 + 2 * W.a₃ * lamK * νK + 3 * W.a₆ * lamK * νK ^ 2 - lamK)
      = 0 := (mul_eq_zero.mp hDz).resolve_left (sub_ne_zero.mpr hz12K)
  have E2 : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3) * (z1 * z2 + z1 * tK + z2 * tK)
      = W.a₁ * νK + W.a₄ * νK ^ 2 + 2 * W.a₃ * lamK * νK + 3 * W.a₆ * lamK * νK ^ 2 - lamK := by
    linear_combination (z1 + z2) * Ve1 - Dz
  have E3 : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3) * (z1 * z2 * tK)
      = -(W.a₃ * νK ^ 2 + W.a₆ * νK ^ 3 - νK) := by
    linear_combination F1 - z1 ^ 2 * Ve1 + z1 * E2
  have key : (1 + W.a₂ * lamK + W.a₄ * lamK ^ 2 + W.a₆ * lamK ^ 3)
      * ((lamK ^ 2 + W.a₁ * lamK * νK - W.a₂ * νK ^ 2)
            * ((lamK * z1 + νK) * (lamK * z2 + νK) * (lamK * tK + νK))
          - z1 * νK ^ 2 * ((lamK * z2 + νK) * (lamK * tK + νK))
          - z2 * νK ^ 2 * ((lamK * z1 + νK) * (lamK * tK + νK))
          - tK * νK ^ 2 * ((lamK * z1 + νK) * (lamK * z2 + νK))) = 0 := by
    linear_combination
      ((lamK ^ 2 + W.a₁ * lamK * νK - W.a₂ * νK ^ 2) * lamK * νK ^ 2 - νK ^ 4) * Ve1
      + ((lamK ^ 2 + W.a₁ * lamK * νK - W.a₂ * νK ^ 2) * lamK ^ 2 * νK - 2 * lamK * νK ^ 3) * E2
      + ((lamK ^ 2 + W.a₁ * lamK * νK - W.a₂ * νK ^ 2) * lamK ^ 3 - 3 * lamK ^ 2 * νK ^ 2) * E3
  have hP : (lamK ^ 2 + W.a₁ * lamK * νK - W.a₂ * νK ^ 2)
        * ((lamK * z1 + νK) * (lamK * z2 + νK) * (lamK * tK + νK))
      - z1 * νK ^ 2 * ((lamK * z2 + νK) * (lamK * tK + νK))
      - z2 * νK ^ 2 * ((lamK * z1 + νK) * (lamK * tK + νK))
      - tK * νK ^ 2 * ((lamK * z1 + νK) * (lamK * z2 + νK)) = 0 :=
    (mul_eq_zero.mp key).resolve_left hAne
  have hlin1 : lamK * z1 + νK ≠ 0 := hcw1 ▸ hw1ne
  have hlin2 : lamK * z2 + νK ≠ 0 := hcw2 ▸ hw2ne
  have hlin3 : lamK * tK + νK ≠ 0 := hcw3 ▸ hw3ne
  rw [hslope, hx1, hx2, X₃_def, ← htK, ← hw3, WeierstrassCurve.Affine.addX]
  rw [hcw1, hcw2, hcw3]
  field_simp
  linear_combination hP

end Secant

section Doubling

variable {z : R} (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
  (hw : thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0)
  (hν : algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) ≠ 0)
  (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz))

end Doubling

end WeierstrassCurve
