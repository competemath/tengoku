/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.SecantAdditivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Secant closure of the reduction kernel `E₁(K)` (issue #367, partial)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  Working towards the fact that
the reduction kernel `E₁(K) = {P // ReducesToZero R W P}` is closed under addition (issue #367),
this file discharges the **non-degenerate secant case**: for `P, Q ∈ E₁(K)` with `x(P) ≠ x(Q)` and
honestly-geometric distinctness `X₃ ∉ {x(P), x(Q)}`, the affine sum `P + Q` again reduces to the
origin.

The merged secant additivity `localParam_add_of_X_ne_of_distinct`
(`Reduction/SecantAdditivity.lean`) takes `ReducesToZero R W (P + Q)` as a *hypothesis* (`hred`).
Here we **prove** that hypothesis in the secant case, so the additivity identity holds without
assuming closure a priori.

## The closure argument

Mathlib's affine sum in the secant case is `P + Q = some (addX x₁ x₂ ℓ) (addY …)` (`add_of_X_ne`),
so `ReducesToZero R W (P + Q)` unfolds to `1 < v(addX x₁ x₂ ℓ)`.  Now:

* `addX x₁ x₂ ℓ = X₃` — Mathlib's affine third-intersection `x`-coordinate is the transported Vieta
  third point (`addX_eq_thirdChordX`, needing the distinctness `X₃ ∉ {x₁, x₂}`);
* `X₃ = t / w₃ = t / wParam t = xParam t` where `t = thirdRootNum` — the third chord `w`-value is
  the coordinate expansion `wParam t` (`thirdChordW_eq_wParam`);
* `1 < v(xParam t)` for `t ≠ 0` (`one_lt_valuation_xParam`, with `t ≠ 0` from
  `thirdRootNum_ne_zero`), i.e. the recovered third point has a pole.

Hence `1 < v(addX)`, so `P + Q ∈ E₁(K)`.  **No new analytic machinery is needed** — the valuation
control comes entirely from the merged coordinate-recovery bricks; in particular the closure does
*not* pass through the cancellation-sensitive direct slope-valuation route (Silverman AEC VII.2).

## Main results

* `WeierstrassCurve.reducesToZero_add_of_X_ne_of_distinct` — `P, Q ∈ E₁(K)`, `x₁ ≠ x₂`,
  `X₃ ∉ {x₁, x₂}` ⇒ `P + Q ∈ E₁(K)` (the secant add-closure).
* `WeierstrassCurve.localParam_add_secant_of_distinct` — the secant additivity of the local
  parameter `localParam (P + Q) = z(P) ⊕ z(Q)` **without** the `hred` hypothesis, obtained by
  feeding the closure lemma into `localParam_add_of_X_ne_of_distinct`.

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
/-- **Secant add-closure of the reduction kernel.**  For two points `P = (x₁, y₁)`, `Q = (x₂, y₂)`
reducing to the origin with `x₁ ≠ x₂` (the secant case) and the honestly-geometric distinctness
`X₃ ∉ {x₁, x₂}`, the affine sum `P + Q` again reduces to the origin.

This discharges the `hred` hypothesis of `localParam_add_of_X_ne_of_distinct` in the non-degenerate
secant case: the affine third-intersection `x`-coordinate `addX = X₃ = xParam t`
(`t = thirdRootNum`) has a pole (`1 < v(xParam t)` for `t ≠ 0`), which is exactly the
`ReducesToZero` condition.  The
excluded distinctness failures `X₃ ∈ {x₁, x₂}` are the degenerate `2P + Q = O` / `P + 2Q = O`
configurations, where closure holds by `reducesToZero_neg` instead. -/
theorem reducesToZero_add_of_X_ne_of_distinct [W.IsElliptic]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} (hR1 : ReducesToZero R W (.some x₁ y₁ h₁))
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hR2 : ReducesToZero R W (.some x₂ y₂ h₂))
    (hxne : x₁ ≠ x₂)
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x₁ y₁ h₁), localParamR R W (.some x₂ y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal)
    (hd1 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR1))
    (hd2 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR2)) :
    ReducesToZero R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) := by
  -- the two parameters are nonzero
  have hz₁0 : localParamR R W (.some x₁ y₁ h₁) ≠ 0 := localParamR_ne_zero_of_reduces R W hR1
  have hz₂0 : localParamR R W (.some x₂ y₂ h₂) ≠ 0 := localParamR_ne_zero_of_reduces R W hR2
  -- the recovered coordinates are the original ones
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
  -- the two recovered `x`-coordinates are distinct (the secant condition on the parameters)
  have hx : xParam R W (localParamR_mem R W hR1) ≠ xParam R W (localParamR_mem R W hR2) := by
    rw [hx1, hx2]; exact hxne
  -- the parameters themselves are distinct (via injectivity of `zParam` and `x₁ ≠ x₂`)
  have hz : localParamR R W (.some x₁ y₁ h₁) ≠ localParamR R W (.some x₂ y₂ h₂) := by
    intro he
    have hPQ : (⟨.some x₁ y₁ h₁, hR1⟩ : {P : W.toAffine.Point // ReducesToZero R W P})
        = ⟨.some x₂ y₂ h₂, hR2⟩ :=
      zParam_injective R W (Subtype.ext (by rw [zParam_coe, zParam_coe]; exact he))
    rw [Subtype.mk_eq_mk, Affine.Point.some.injEq] at hPQ
    exact hxne hPQ.1
  -- the third-chord `w`-value and the Vieta root are unconditionally nonzero in the secant case
  have hw : thirdChordW R W ha ≠ 0 :=
    thirdChordW_ne_zero R W ha (localParamR_mem R W hR1) (localParamR_mem R W hR2) hz₁0 hz₂0 hx
  have htne : thirdRootNum R W ha ≠ 0 :=
    thirdRootNum_ne_zero R W ha (localParamR_mem R W hR1) (localParamR_mem R W hR2) hz₁0 hz₂0 hx
  -- `addX = X₃` (the affine matching), and `X₃ = xParam t` (the third point is `pointOfParam t`)
  have haddX : W.toAffine.addX (xParam R W (localParamR_mem R W hR1))
        (xParam R W (localParamR_mem R W hR2))
        (W.toAffine.slope (xParam R W (localParamR_mem R W hR1))
          (xParam R W (localParamR_mem R W hR2))
          (yParam R W (localParamR_mem R W hR1)) (yParam R W (localParamR_mem R W hR2)))
      = X₃ R W ha :=
    addX_eq_thirdChordX R W ha hz (localParamR_mem R W hR1) (localParamR_mem R W hR2)
      hz₁0 hz₂0 hw hx hd1 hd2
  have hX3eq : X₃ R W ha = xParam R W (thirdRootNum_mem R W ha) := by
    rw [X₃_def, xParam, thirdChordW_eq_wParam R W ha hz]
  -- rephrase the affine matching in the original coordinates
  rw [hx1, hx2, hy1, hy2] at haddX
  -- the recovered third point has a pole: `1 < v(addX)`
  have hfinal : 1 < valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) := by
    rw [haddX, hX3eq]
    exact one_lt_valuation_xParam R W (thirdRootNum_mem R W ha) htne
  -- Mathlib's affine sum is the secant third point `(addX, addY)`; `ReducesToZero` is `1 < v(addX)`
  rw [Affine.Point.add_of_X_ne hxne]
  exact hfinal

open Classical in
/-- **Secant additivity of the local parameter, closure discharged.**  For `P, Q ∈ E₁(K)` with
`x₁ ≠ x₂` and `X₃ ∉ {x₁, x₂}`, `localParam (P + Q) = z(P) ⊕ z(Q)` in `K` — the merged
`localParam_add_of_X_ne_of_distinct` with its `ReducesToZero (P + Q)` hypothesis supplied by
`reducesToZero_add_of_X_ne_of_distinct`.  The only remaining hypotheses are the honest secant
geometry (`x₁ ≠ x₂`, `X₃ ∉ {x₁, x₂}`). -/
theorem localParam_add_secant_of_distinct [W.IsElliptic]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} (hR1 : ReducesToZero R W (.some x₁ y₁ h₁))
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hR2 : ReducesToZero R W (.some x₂ y₂ h₂))
    (hxne : x₁ ≠ x₂)
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x₁ y₁ h₁), localParamR R W (.some x₂ y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal)
    (hd1 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR1))
    (hd2 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR2)) :
    localParam R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW) :=
  localParam_add_of_X_ne_of_distinct R W hR1 hR2 hxne
    (reducesToZero_add_of_X_ne_of_distinct R W hR1 hR2 hxne ha hd1 hd2) ha hd1 hd2

end WeierstrassCurve
