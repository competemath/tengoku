/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLawIdentification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bridge lemmas and the reduction of the core identity `(★)` to `(K1)`, `(K4)`

`EllipticCurves.FormalGroup.GenuineLawIdentification` reduced the identification
`embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent` to the single polynomial identity

`(★)  φ(z₃') · y₃ = x₃ · φ(D)`

(`W.embedDoubleLaurent_formalGroupZW_of_core`), where `φ = HahnSeries.embedDoubleLaurent`. This
file takes the next step: it supplies reusable *bridge lemmas* between the `(z, w)`- and
`(x, y)`-planes and reduces `(★)` **unconditionally** to two coordinate relations at the third
intersection point.

## The reduction of `(★)` to two coordinate relations at the third point

Write `Z := φ(z₃')`, `μ := φ(λ_zw)`, `ν_L := φ(ν_zw)`, `λ := formalLambda`, `ν := formalNu`,
`x₃ := formalXThree`, and the third-intersection values `Y := λ·x₃ + ν` (line `y`-value) and
`P := μ·Z + ν_L` (chord `w`-value). Then `(★)` is a `linear_combination` of

* `(K1)`  `Z · Y = -x₃`   (the `z·y = -x` relation at the third point), and
* `(K4)`  `x₃ · P = Z`     (the `x·w = z` relation at the third point).

This reduction is `embedDoubleLaurent_formalThirdRoot_mul_formalYThree_of_K1_K4` below (sorry-free).
The inputs `(K1)`/`(K4)` encode that the projective-linear change of coordinates `z = -x/y`,
`w = -1/y` maps the `(x, y)`-secant's third intersection `(x₃, Y)` to the `(z, w)`-chord's third
intersection `(Z, P)` (Silverman AEC IV.1, Theorem 1.1); establishing them is the research-grade
crux of **this** route (see below) and is left open.

⚠️ **"Left open" is a statement about this route, not about the identification.**  The goal this
file reduces — `embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent` — is merged and
unconditional over every `CommRing R` as `WeierstrassCurve.embedDoubleLaurent_formalGroupZW`
(`EllipticCurves.FormalGroup.GenuineLawTransfer`, issue #310), reached by the third-root matching
of `EllipticCurves.FormalGroup.GenuineLawIdentification` and the universal-domain transfer.
`(K1)`/`(K4)` were never proved and nothing downstream waits on them; the reduction and the bridge
lemmas below are kept because they are sorry-free, reusable, and the `IsUnit W.formalNu` lead is
still the shortest description of what this route would need.

## Bridge lemmas provided (all sorry-free, reusable)

* `isUnit_embedDoubleLaurent_formalGroupLead` / `embedDoubleLaurent_formalGroupLead_mul_inverse` :
  `A = φ(formalGroupLead)` is a unit, with its explicit inverse-cancellation.
* `chordW_biZ₁` / `chordW_biZ₂` : the chord `w = μz + ν_L` passes through `(z₁, w₁)`, `(z₂, w₂)`
  (the second uses the slope bridge).
* `zPlaneCurve_biZ₁` / `zPlaneCurve_biZ₂` : the `z`-plane curve equations at `(z₁, w₁)` and
  `(z₂, w₂)`, i.e. the `φ`-images of `formalCubicResidual_root_zero`/`_one` with the chord
  `w`-values substituted.

## The remaining crux `(K1)`/`(K4)`

`(K1)`/`(K4)` relate the `(z, w)`-plane Vieta third root `Z = -(B·A⁻¹) - z₁ - z₂` to the
`(x, y)`-plane third point `(x₃, Y)`. There is no `z`-cubic Vieta *factorisation*
`residual = A·(z - z₁)(z - z₂)(z - Z)` in the library, and matching the third roots appears to
need either that fact or the unit property of `z₂ - z₁`. A useful lead: `z₂ - z₁ = biZ₂ - biZ₁`
satisfies `z₂ - z₁ = -ν · (x₂ - x₁) · (y₁·y₂)⁻¹`, so — as `x₂ - x₁`, `y₁`, `y₂` are units —
`z₂ - z₁` is a unit **iff** `formalNu` is a unit; proving `IsUnit W.formalNu` (an order/leading-
coefficient argument in the style of `isUnit_formalYThree`) would unlock the Vieta route.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries
open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Foundational helpers: unit of `A`, the chord `w`-values, the `z`-plane curve equations -/

/-- The constant coefficient of `formalWDividedDiff` vanishes (re-derived publicly from
`two_le_order_formalWDividedDiff`). -/
theorem constantCoeff_formalWDividedDiff :
    MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
    (le_trans (by exact_mod_cast one_le_two) W.two_le_order_formalWDividedDiff)

/-- `constantCoeff formalGroupLead = 1`. -/
theorem constantCoeff_formalGroupLead :
    MvPowerSeries.constantCoeff W.formalGroupLead = 1 := by
  rw [formalGroupLead]
  simp only [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, map_one,
    W.constantCoeff_formalWDividedDiff]
  ring

/-- `A = φ(formalGroupLead)` is a unit of `(R⸨X⸩)⸨X⸩`. -/
theorem isUnit_embedDoubleLaurent_formalGroupLead :
    IsUnit (HahnSeries.embedDoubleLaurent W.formalGroupLead) := by
  have hone : HahnSeries.embedDoubleLaurent W.formalGroupLead
      * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupLead 1) = 1 := by
    rw [← HahnSeries.embedDoubleLaurentRingHom_apply, ← HahnSeries.embedDoubleLaurentRingHom_apply,
      ← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupLead 1
        (by rw [W.constantCoeff_formalGroupLead, Units.val_one]), map_one]
  exact IsUnit.of_mul_eq_one _ hone

/-- `A · Ring.inverse A = 1`. -/
theorem embedDoubleLaurent_formalGroupLead_mul_inverse :
    HahnSeries.embedDoubleLaurent W.formalGroupLead
      * Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupLead) = 1 :=
  Ring.mul_inverse_cancel _ W.isUnit_embedDoubleLaurent_formalGroupLead

/-- **Chord `w`-value at `z₁`.** `μ · z₁ + ν_L = w₁`: the chord `w = μz + ν_L` passes through
`(z₁, w₁)`. -/
theorem chordW_biZ₁ :
    HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.biZ₁
        + HahnSeries.embedDoubleLaurent W.formalGroupNu = W.biW₁ := by
  rw [W.embedDoubleLaurent_formalGroupNu]; ring

/-- **Chord `w`-value at `z₂`.** `μ · z₂ + ν_L = w₂`: the chord passes through `(z₂, w₂)` (uses the
slope bridge). -/
theorem chordW_biZ₂ :
    HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.biZ₂
        + HahnSeries.embedDoubleLaurent W.formalGroupNu = W.biW₂ := by
  rw [W.embedDoubleLaurent_formalGroupNu]
  linear_combination W.embedDoubleLaurent_formalWDividedDiff_spec

/-- **`z`-plane curve equation at `(z₁, w₁)`** (the `φ`-image of `formalCubicResidual_root_zero`,
with the chord `w`-value simplified to `w₁`). -/
theorem zPlaneCurve_biZ₁ :
    W.biZ₁ ^ 3
        + (HahnSeries.C (HahnSeries.C W.a₁) * W.biZ₁
            + HahnSeries.C (HahnSeries.C W.a₂) * W.biZ₁ ^ 2) * W.biW₁
        + (HahnSeries.C (HahnSeries.C W.a₃)
            + HahnSeries.C (HahnSeries.C W.a₄) * W.biZ₁) * W.biW₁ ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆) * W.biW₁ ^ 3
        - W.biW₁ = 0 := by
  have h := congrArg HahnSeries.embedDoubleLaurentRingHom W.formalCubicResidual_root_zero
  simp only [map_add, map_sub, map_mul, map_pow, map_zero,
    HahnSeries.embedDoubleLaurentRingHom_apply, W.embedDoubleLaurent_biZ₁,
    HahnSeries.embedDoubleLaurent_C] at h
  rw [W.chordW_biZ₁] at h
  exact h

/-- **`z`-plane curve equation at `(z₂, w₂)`.** -/
theorem zPlaneCurve_biZ₂ :
    W.biZ₂ ^ 3
        + (HahnSeries.C (HahnSeries.C W.a₁) * W.biZ₂
            + HahnSeries.C (HahnSeries.C W.a₂) * W.biZ₂ ^ 2) * W.biW₂
        + (HahnSeries.C (HahnSeries.C W.a₃)
            + HahnSeries.C (HahnSeries.C W.a₄) * W.biZ₂) * W.biW₂ ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆) * W.biW₂ ^ 3
        - W.biW₂ = 0 := by
  have h := congrArg HahnSeries.embedDoubleLaurentRingHom W.formalCubicResidual_root_one
  simp only [map_add, map_sub, map_mul, map_pow, map_zero,
    HahnSeries.embedDoubleLaurentRingHom_apply, W.embedDoubleLaurent_biZ₂,
    HahnSeries.embedDoubleLaurent_C] at h
  rw [W.chordW_biZ₂] at h
  exact h

/-! ### The reduction of `(★)` to the two coordinate relations `(K1)`, `(K4)` -/

/-- **The core identity `(★)` from `(K1)` and `(K4)`.** `φ(z₃') · y₃ = x₃ · φ(D)`, obtained from the
two coordinate relations

* `(K1)`  `Z · Y = -x₃`  (`hK1`, with `Y = λ·x₃ + ν`), and
* `(K4)`  `x₃ · P = Z`   (`hK4`, with `P = μ·Z + ν_L`),

by a single `linear_combination`. This is the unconditional algebraic reduction; supplying the
geometric inputs `(K1)`/`(K4)` closes the identification via
`W.embedDoubleLaurent_formalGroupZW_of_core`. -/
theorem embedDoubleLaurent_formalThirdRoot_mul_formalYThree_of_K1_K4
    (hK1 : HahnSeries.embedDoubleLaurent W.formalThirdRoot
        * (W.formalLambda * W.formalXThree + W.formalNu) = -W.formalXThree)
    (hK4 : W.formalXThree
        * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
            * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu)
          = HahnSeries.embedDoubleLaurent W.formalThirdRoot) :
    HahnSeries.embedDoubleLaurent W.formalThirdRoot * W.formalYThree
      = W.formalXThree * HahnSeries.embedDoubleLaurent W.formalGroupDen := by
  rw [W.embedDoubleLaurent_formalGroupDen, formalYThree]
  linear_combination (-1 : (R⸨X⸩)⸨X⸩) * hK1 + HahnSeries.C (HahnSeries.C W.a₃) * hK4

/-- **The identification, conditional on `(K1)`/`(K4)`.** Given the two coordinate relations at the
third point, the `(z, w)` and Laurent formal group laws agree:
`embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent`. -/
theorem embedDoubleLaurent_formalGroupZW_of_K1_K4
    (hK1 : HahnSeries.embedDoubleLaurent W.formalThirdRoot
        * (W.formalLambda * W.formalXThree + W.formalNu) = -W.formalXThree)
    (hK4 : W.formalXThree
        * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
            * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu)
          = HahnSeries.embedDoubleLaurent W.formalThirdRoot) :
    HahnSeries.embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent :=
  W.embedDoubleLaurent_formalGroupZW_of_core
    (W.embedDoubleLaurent_formalThirdRoot_mul_formalYThree_of_K1_K4 hK1 hK4)

end WeierstrassCurve
