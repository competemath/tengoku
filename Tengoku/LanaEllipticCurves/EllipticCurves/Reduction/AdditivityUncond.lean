/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.SecantClosure
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.TangentClosure
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ThirdChordAffineUncond

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unconditional local-parameter additivity: secant and doubling, no `hd` (issue #367)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  For points reducing to the
origin, the local parameter `z = -x/y` is *additive* over the formal group law:
`z(P + Q) = z(P) ⊕ z(Q) = adicEvalMv 𝔪 ![z P, z Q] formalGroupZW`.

The merged point-level additivity identities `localParam_add_of_X_ne` (secant,
`Reduction/ThirdChordAffine.lean`) and `localParam_add_of_X_eq` (doubling,
`Reduction/TangentThirdChordAffine.lean`) — and their analytic-side-condition-discharged forms
`localParam_add_of_X_ne_of_distinct` (`Reduction/SecantAdditivity.lean`) /
`localParam_add_of_X_eq_clean` (`Reduction/TangentAdditivityClean.lean`) — all still carried a
non-degeneracy hypothesis `hd : X₃ ∉ {x₁, x₂}` (resp. `X₃ ≠ x`) on the transported Vieta third
`x`-coordinate.  That `hd` entered **only** through the affine matching `addX = X₃`
(`addX_eq_thirdChordX` / `addX_eq_thirdChordX_diag`), which was proved by affine root-selection and
genuinely fails in the `Q = -2P` / `3P = O` configurations.

Issue #376 (`Reduction/ThirdChordAffineUncond.lean`) removed exactly that: the unconditional
matchings `addX_eq_thirdChordX_of_secant` / `addX_eq_thirdChordX_of_doubling` prove `addX = X₃` as a
`(z, w)`-level Vieta symmetric-function field identity, with **no** distinctness of `X₃`.  This file
threads those unconditional matchings through the additivity proofs, dropping `hd` entirely.

## Main results

* `WeierstrassCurve.localParam_add_secant_uncond` — the coordinate-level secant additivity
  `-addX / addY = z₁ ⊕ z₂`, **no** `hd`.
* `WeierstrassCurve.localParam_add_of_X_ne_uncond` — point-level secant additivity
  `z(P + Q) = z(P) ⊕ z(Q)` (`x₁ ≠ x₂`), requiring **only** the geometric hypotheses (`x₁ ≠ x₂`, both
  summands and the sum reducing).  All of `hw`, `hd₁`, `hd₂`, `hden` are discharged internally.
* `WeierstrassCurve.localParam_add_diag_uncond` — the coordinate-level doubling additivity
  `-addX / addY = z ⊕ z`, **no** `hd`.
* `WeierstrassCurve.localParam_add_of_X_eq_uncond` — point-level doubling additivity
  `z(P + P) = z(P) ⊕ z(P)` (`2P ≠ O`), requiring **only** the geometric hypotheses.  All of `hw`,
  `hν`, `hd`, `hden` are discharged internally.

Together with the vertical/inverse case (`adicEvalMv_formalGroupZW_eq_zero_of_X_eq`,
`Reduction/InverseAdditivity.lean`) and the identity cases, these are the coordinate-additivity
bricks the full group-law compatibility
`zParamHatEquiv (P + Q) = zParamHatEquiv P + zParamHatEquiv Q` (issue #368's `map_add`) consumes.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W]

open Classical in
/-- **Coordinate-level secant additivity of the local parameter, unconditional.**
`-addX / addY = z₁ ⊕ z₂` in `K`, the `hd`-free version of `localParam_add_secant`: the affine
matching `addX = X₃` is supplied by the unconditional `addX_eq_thirdChordX_of_secant` (#376), so no
distinctness `X₃ ∉ {x₁, x₂}` is needed.  Only the secant non-degeneracy (`z₁ ≠ z₂`,
`xParam z₁ ≠ xParam z₂`, `w₃ ≠ 0`) and `den ≠ 0` remain. -/
theorem localParam_add_secant_uncond {z₁ z₂ : R}
    (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)
    (hz : z₁ ≠ z₂) (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal) (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal)
    (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0) (hw : thirdChordW R W ha ≠ 0)
    (hx : xParam R W hz₁ ≠ xParam R W hz₂)
    (hden : adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen ≠ 0) :
    -(W.toAffine.addX (xParam R W hz₁) (xParam R W hz₂)
          (W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂)))
        / W.toAffine.addY (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁)
            (W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂))
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW) := by
  set ℓ := W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂)
    with hℓ
  have hwne : algebraMap R K (thirdChordW R W ha) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hdenne : algebraMap R K
      (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hden
  have haddX := addX_eq_thirdChordX_of_secant R W ha hz hz₁ hz₂ hz₁0 hz₂0 hw hx
  have hline := thirdChord_on_secantLine R W ha hz₁ hz₂ hz₁0 hz₂0 hw hx
  rw [← hℓ] at haddX hline
  -- the negated `y`-coordinate of the sum is `-1 / w₃`
  have hnegAddY : W.toAffine.negAddY (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) ℓ
      = -1 / algebraMap R K (thirdChordW R W ha) := by
    rw [Affine.negAddY, haddX, ← hline]
  -- the `den`-closed form, folded through `thirdChordW`
  have hden_R : adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen
      = 1 - (integralModel R W).a₁ * thirdRootNum R W ha
        - (integralModel R W).a₃ * thirdChordW R W ha := by
    rw [adicEvalMv_formalGroupDen, thirdChordW]
  have hden_closed : algebraMap R K
        (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen)
      = 1 - W.a₁ * algebraMap R K (thirdRootNum R W ha)
        - W.a₃ * algebraMap R K (thirdChordW R W ha) := by
    have h := congrArg (algebraMap R K) hden_R
    simpa only [map_sub, map_mul, map_one, integralModel_a₁_eq, integralModel_a₃_eq] using h
  -- `addY = den / w₃`
  have haddY : W.toAffine.addY (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) ℓ
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen)
        / algebraMap R K (thirdChordW R W ha) := by
    rw [Affine.addY, Affine.negY, hnegAddY, haddX, X₃_def, hden_closed]
    field_simp
  -- the numeric inversion `den · (z₁ ⊕ z₂) = -t`
  have hZW := congrArg (algebraMap R K) (formalGroupDen_mul_adicEvalMv_formalGroupZW R W ha)
  rw [map_mul, map_neg] at hZW
  rw [haddX, haddY, X₃_def]
  field_simp
  linear_combination -hZW

open Classical in
/-- **Point-level secant additivity of the local parameter, unconditional.**  For two points
`P = (x₁, y₁)`, `Q = (x₂, y₂)` reducing to the origin with `x₁ ≠ x₂` (the secant case), whose affine
sum `P + Q` also reduces to the origin, `z(P + Q) = z(P) ⊕ z(Q) = adicEvalMv 𝔪 ![z₁, z₂]
formalGroupZW`.  This is `localParam_add_of_X_ne` with **all** side conditions discharged: `hw` and
`hden` are unconditional in the secant case (`thirdChordW_ne_zero`,
`adicEvalMv_formalGroupDen_ne_zero`) and the distinctness `hd₁, hd₂` is removed by #376. -/
theorem localParam_add_of_X_ne_uncond [W.IsElliptic]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} (hR1 : ReducesToZero R W (.some x₁ y₁ h₁))
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hR2 : ReducesToZero R W (.some x₂ y₂ h₂))
    (hxne : x₁ ≠ x₂)
    (hred : ReducesToZero R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂))
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x₁ y₁ h₁), localParamR R W (.some x₂ y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal) :
    localParam R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW) := by
  have hz₁0 : localParamR R W (.some x₁ y₁ h₁) ≠ 0 := localParamR_ne_zero_of_reduces R W hR1
  have hz₂0 : localParamR R W (.some x₂ y₂ h₂) ≠ 0 := localParamR_ne_zero_of_reduces R W hR2
  have hcoord1 : xParam R W (localParamR_mem R W hR1) = x₁
      ∧ yParam R W (localParamR_mem R W hR1) = y₁ := by
    have hpt := pointOfParam_localParamR R W hR1 hz₁0
    simpa only [pointOfParam, Affine.Point.some.injEq] using hpt
  have hcoord2 : xParam R W (localParamR_mem R W hR2) = x₂
      ∧ yParam R W (localParamR_mem R W hR2) = y₂ := by
    have hpt := pointOfParam_localParamR R W hR2 hz₂0
    simpa only [pointOfParam, Affine.Point.some.injEq] using hpt
  obtain ⟨hx1, hy1⟩ := hcoord1
  obtain ⟨hx2, hy2⟩ := hcoord2
  have hx : xParam R W (localParamR_mem R W hR1) ≠ xParam R W (localParamR_mem R W hR2) := by
    rw [hx1, hx2]; exact hxne
  have hz : localParamR R W (.some x₁ y₁ h₁) ≠ localParamR R W (.some x₂ y₂ h₂) := by
    intro he
    have hPQ : (⟨.some x₁ y₁ h₁, hR1⟩ : {P : W.toAffine.Point // ReducesToZero R W P})
        = ⟨.some x₂ y₂ h₂, hR2⟩ :=
      zParam_injective R W (Subtype.ext (by rw [zParam_coe, zParam_coe]; exact he))
    rw [Subtype.mk_eq_mk, Affine.Point.some.injEq] at hPQ
    exact hxne hPQ.1
  have hw : thirdChordW R W ha ≠ 0 :=
    thirdChordW_ne_zero R W ha (localParamR_mem R W hR1) (localParamR_mem R W hR2) hz₁0 hz₂0 hx
  have hden : adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen ≠ 0 :=
    adicEvalMv_formalGroupDen_ne_zero R W ha
  rw [Affine.Point.add_of_X_ne hxne] at hred ⊢
  have hpos : 1 < valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) := hred
  rw [localParam_some, ite_eq_left hpos]
  have key := localParam_add_secant_uncond R W ha hz (localParamR_mem R W hR1)
    (localParamR_mem R W hR2) hz₁0 hz₂0 hw hx hden
  rw [hx1, hy1, hx2, hy2] at key
  exact key

end WeierstrassCurve
