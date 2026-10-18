/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLawIdentificationCore
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.CubicFactorisation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric matching: reducing the `(z, w)`↔`(x, y)` identification to the single relation `(K4)`

`EllipticCurves.FormalGroup.GenuineLawIdentificationCore` reduced the identification
`embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent` to **two** coordinate relations at the
third intersection point,

* `(K1)`  `Z · Y = -x₃`   (the `z·y = -x` relation), and
* `(K4)`  `x₃ · P = Z`     (the `x·w = z` relation),

where (writing `φ = HahnSeries.embedDoubleLaurent`) `Z := φ(z₃')` is the `(z, w)`-plane Vieta third
root, `μ := φ(λ_zw)`, `ν_L := φ(ν_zw)`, `λ := formalLambda`, `ν := formalNu`, `x₃ := formalXThree`,
`Y := λ·x₃ + ν` (the secant `y`-value) and `P := μ·Z + ν_L` (the chord `w`-value).

This file collapses the pair `(K1)`/`(K4)` down to the **single** relation `(K4)`, by supplying the
two *linear bridge* identities that link the `(z, w)`- and `(x, y)`-plane chord/secant data:

* `formalWDividedDiff_image_eq`  `μ = ν_L · λ`   (the two chords have proportional slopes), and
* `formalGroupNu_image_mul_formalNu`  `ν_L · ν = -1`   (proportional intercepts).

Both are consequences of the base coordinate relations `z·y = -x`, `y·w = -1`, `x·w = z` at the two
base points `(z₁, w₁)`, `(z₂, w₂)` together with `chordW_biZ₁`/`chordW_biZ₂` (the chord passes
through them). From them, `(K3)` `Y·P = -1` and hence `(K1)` follow from `(K4)` by pure algebra, so
the whole identification is reduced to `(K4)` alone (`embedDoubleLaurent_formalGroupZW_of_K4`).

We also record `zPlaneCurve_thirdRoot`: the `φ`-image of `formalCubicResidual_root_thirdRoot`, i.e.
the `z`-plane curve equation `(Z, P)` at the Vieta third root. This is the exact analogue of
`zPlaneCurve_biZ₁`/`_biZ₂` at the third root and is the geometric input from which a proof of `(K4)`
(via the `z`-cubic Vieta factorisation and the coordinate change `z = -x/y`, `w = -1/y`) proceeds.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries
open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The `z`-plane curve equation at the Vieta third root -/

/-- **`z`-plane curve equation at the third root `(Z, P)`.** The `φ`-image of
`formalCubicResidual_root_thirdRoot`: the Vieta third root `Z = φ(z₃')` together with the chord
`w`-value `P = μ·Z + ν_L` satisfies the `z`-plane Weierstrass equation. This is the third-root
analogue of `zPlaneCurve_biZ₁`/`zPlaneCurve_biZ₂`. -/
theorem zPlaneCurve_thirdRoot :
    HahnSeries.embedDoubleLaurent W.formalThirdRoot ^ 3
        + (HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.C (HahnSeries.C W.a₂)
              * HahnSeries.embedDoubleLaurent W.formalThirdRoot ^ 2)
          * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
              * HahnSeries.embedDoubleLaurent W.formalThirdRoot
              + HahnSeries.embedDoubleLaurent W.formalGroupNu)
        + (HahnSeries.C (HahnSeries.C W.a₃)
            + HahnSeries.C (HahnSeries.C W.a₄)
              * HahnSeries.embedDoubleLaurent W.formalThirdRoot)
          * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
              * HahnSeries.embedDoubleLaurent W.formalThirdRoot
              + HahnSeries.embedDoubleLaurent W.formalGroupNu) ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆)
          * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
              * HahnSeries.embedDoubleLaurent W.formalThirdRoot
              + HahnSeries.embedDoubleLaurent W.formalGroupNu) ^ 3
        - (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
            * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu) = 0 := by
  have h := congrArg HahnSeries.embedDoubleLaurentRingHom W.formalCubicResidual_root_thirdRoot
  simpa only [map_add, map_sub, map_mul, map_pow, map_zero,
    HahnSeries.embedDoubleLaurentRingHom_apply, HahnSeries.embedDoubleLaurent_C] using h

/-! ### The linear bridge identities between the `(z, w)`- and `(x, y)`-plane chord/secant data -/

/-- **Base-point bridge at `z₁`.** `μ·x₁ - ν_L·y₁ = 1`. Multiplying the chord relation
`μ·z₁ + ν_L = w₁` by `y₁` and using `z₁·y₁ = -x₁`, `y₁·w₁ = -1`. -/
theorem mulBridge_biZ₁ :
    HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.biX₁
        - HahnSeries.embedDoubleLaurent W.formalGroupNu * W.biY₁ = 1 := by
  linear_combination (-W.biY₁) * W.chordW_biZ₁
    + HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.biZ₁_mul_biY₁
    - W.biY₁_mul_biW₁

/-- **Base-point bridge at `z₂`.** `μ·x₂ - ν_L·y₂ = 1`. -/
theorem mulBridge_biZ₂ :
    HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.biX₂
        - HahnSeries.embedDoubleLaurent W.formalGroupNu * W.biY₂ = 1 := by
  linear_combination (-W.biY₂) * W.chordW_biZ₂
    + HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.biZ₂_mul_biY₂
    - W.biY₂_mul_biW₂

/-- **Slope bridge.** `μ = ν_L · λ`: the `(z, w)`-chord slope equals `ν_L` times the `(x, y)`-secant
slope. Obtained by cancelling the unit `x₂ - x₁` from `μ·(x₂ - x₁) = ν_L·λ·(x₂ - x₁)` (the
difference of the two base-point bridges, using the secant slope `λ·(x₂ - x₁) = y₂ - y₁`). -/
theorem formalWDividedDiff_image_eq :
    HahnSeries.embedDoubleLaurent W.formalWDividedDiff
      = HahnSeries.embedDoubleLaurent W.formalGroupNu * W.formalLambda := by
  obtain ⟨u, hu⟩ := W.isUnit_biX₂_sub_biX₁
  have hmul : (W.biX₂ - W.biX₁)
      * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
          - HahnSeries.embedDoubleLaurent W.formalGroupNu * W.formalLambda) = 0 := by
    linear_combination W.mulBridge_biZ₂ - W.mulBridge_biZ₁
      - HahnSeries.embedDoubleLaurent W.formalGroupNu * W.formalLambda_mul_biX_sub
  have hu' : (u : (R⸨X⸩)⸨X⸩)
      * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
          - HahnSeries.embedDoubleLaurent W.formalGroupNu * W.formalLambda) = 0 := by
    rw [hu]; exact hmul
  have := (Units.mul_right_eq_zero u).mp hu'
  linear_combination this

/-- **Intercept bridge.** `ν_L · ν = -1`. Substituting the secant `y₁ = λ·x₁ + ν` into the base
bridge `μ·x₁ - ν_L·y₁ = 1` and using the slope bridge `μ = ν_L·λ`. -/
theorem formalGroupNu_image_mul_formalNu :
    HahnSeries.embedDoubleLaurent W.formalGroupNu * W.formalNu = -1 := by
  linear_combination -W.mulBridge_biZ₁ + W.biX₁ * W.formalWDividedDiff_image_eq
    - HahnSeries.embedDoubleLaurent W.formalGroupNu * W.biY₁_eq

/-! ### Collapsing `(K1)`, `(K3)` onto `(K4)` -/

/-- **`(K3)` from `(K4)`.** `Y · P = -1` (the `y·w = -1` relation at the third point), derived from
`(K4)` and the two linear bridges. -/
theorem thirdPoint_K3_of_K4
    (hK4 : W.formalXThree
        * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
            * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu)
          = HahnSeries.embedDoubleLaurent W.formalThirdRoot) :
    (W.formalLambda * W.formalXThree + W.formalNu)
        * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
            * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu)
      = -1 := by
  linear_combination W.formalLambda * hK4
    + W.formalNu * HahnSeries.embedDoubleLaurent W.formalThirdRoot
        * W.formalWDividedDiff_image_eq
    + (W.formalLambda * HahnSeries.embedDoubleLaurent W.formalThirdRoot + 1)
        * W.formalGroupNu_image_mul_formalNu

/-- **`(K1)` from `(K4)`.** `Z · Y = -x₃` (the `z·y = -x` relation at the third point), derived from
`(K4)` and `(K3)` (`ZY = x₃·P·Y = x₃·(-1) = -x₃`). -/
theorem thirdPoint_K1_of_K4
    (hK4 : W.formalXThree
        * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
            * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu)
          = HahnSeries.embedDoubleLaurent W.formalThirdRoot) :
    HahnSeries.embedDoubleLaurent W.formalThirdRoot
        * (W.formalLambda * W.formalXThree + W.formalNu)
      = -W.formalXThree := by
  linear_combination W.formalXThree * W.thirdPoint_K3_of_K4 hK4
    - (W.formalLambda * W.formalXThree + W.formalNu) * hK4

/-- **The identification from `(K4)` alone.** Given only the single third-point relation `(K4)`
`x₃ · P = Z`, the `(z, w)`- and Laurent formal group laws agree. `(K1)` is recovered internally via
the two linear bridges. -/
theorem embedDoubleLaurent_formalGroupZW_of_K4
    (hK4 : W.formalXThree
        * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
            * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu)
          = HahnSeries.embedDoubleLaurent W.formalThirdRoot) :
    HahnSeries.embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent :=
  W.embedDoubleLaurent_formalGroupZW_of_K1_K4 (W.thirdPoint_K1_of_K4 hK4) hK4

end WeierstrassCurve
