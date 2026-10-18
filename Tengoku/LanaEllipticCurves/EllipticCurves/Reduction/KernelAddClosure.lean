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
# Full add-closure of the reduction kernel `E₁(K)` and the subgroup `E₁ : AddSubgroup` (issue #367)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  The reduction kernel
`E₁(K) = {P | ReducesToZero R W P}` is the set of points reducing to the origin.  This file proves
that `E₁(K)` is **closed under addition** for *all* `P, Q ∈ E₁(K)` — with no non-degeneracy
hypothesis — and packages it as an `AddSubgroup` of `(W⁄K).Point`.

## What was missing, and how #376 removes it

The merged non-degenerate closures `reducesToZero_add_of_X_ne_of_distinct` (secant,
`Reduction/SecantClosure.lean`) and `reducesToZero_add_of_X_eq_of_distinct` (doubling,
`Reduction/TangentClosure.lean`) both carried a distinctness hypothesis `hd : X₃ ∉ {x₁, x₂}` on the
transported Vieta third `x`-coordinate.  Those `hd`'s genuinely fail in the `Q = -2P` / `3P = O`
configurations (the third chord point collides with `±P`), and were the single blocker of the full
subgroup closure.

Issue #376 (`Reduction/ThirdChordAffineUncond.lean`, PR #107) removed exactly that hypothesis:
`addX_eq_thirdChordX_of_secant` / `addX_eq_thirdChordX_of_doubling` prove the affine matching
`addX = X₃` *unconditionally*, as a `(z, w)`-level Vieta symmetric-function field identity.
Swapping those in for `addX_eq_thirdChordX` / `_diag` drops `hd` from the closures, so the
previously-degenerate distinctness-failure configurations are now covered by the *same* secant /
doubling arguments.

## The closure argument (unchanged in substance)

Mathlib's affine sum in the secant case is `P + Q = some (addX x₁ x₂ ℓ) (addY …)` (`add_of_X_ne`)
and in the doubling case `P + P = some (addX x x ℓ) (addY …)` (`add_self_of_Y_ne`), so
`ReducesToZero R W (P + Q)` unfolds to `1 < v(addX)`.  Now `addX = X₃ = t / w₃ = xParam t`
(`t = thirdRootNum`, via `addX_eq_thirdChordX_of_secant`/`_of_doubling` and
`thirdChordW_eq_wParam`), and `1 < v(xParam t)` for `t ≠ 0` (`one_lt_valuation_xParam`) — the
recovered third point has a pole.  Hence `1 < v(addX)`, i.e. `P + Q ∈ E₁(K)`.

## Main results

* `WeierstrassCurve.reducesToZero_add_of_X_ne` — secant add-closure, **no** `hd`.
* `WeierstrassCurve.reducesToZero_add_of_X_eq` — doubling add-closure, **no** `hd`.
* `WeierstrassCurve.reducesToZero_add` — full add-closure: `P, Q ∈ E₁(K) ⇒ P + Q ∈ E₁(K)` for all
  `P, Q` (the vertical `Q = -P`, secant, and doubling cases assembled).
* `WeierstrassCurve.E₁` — the reduction kernel packaged as `AddSubgroup (W⁄K).Point`, with
  `mem_E₁`.

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
/-- **Secant add-closure of the reduction kernel, unconditional.**  For two points
`P = (x₁, y₁)`, `Q = (x₂, y₂)` reducing to the origin with `x₁ ≠ x₂` (the secant case), the affine
sum `P + Q` again reduces to the origin — with **no** non-degeneracy hypothesis on the third
`x`-coordinate `X₃` (the `hd`-free version of `reducesToZero_add_of_X_ne_of_distinct`, using the
unconditional matching `addX_eq_thirdChordX_of_secant` of #376). -/
theorem reducesToZero_add_of_X_ne [W.IsElliptic]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} (hR1 : ReducesToZero R W (.some x₁ y₁ h₁))
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hR2 : ReducesToZero R W (.some x₂ y₂ h₂))
    (hxne : x₁ ≠ x₂)
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x₁ y₁ h₁), localParamR R W (.some x₂ y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal) :
    ReducesToZero R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) := by
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
  have htne : thirdRootNum R W ha ≠ 0 :=
    thirdRootNum_ne_zero R W ha (localParamR_mem R W hR1) (localParamR_mem R W hR2) hz₁0 hz₂0 hx
  have haddX : W.toAffine.addX (xParam R W (localParamR_mem R W hR1))
        (xParam R W (localParamR_mem R W hR2))
        (W.toAffine.slope (xParam R W (localParamR_mem R W hR1))
          (xParam R W (localParamR_mem R W hR2))
          (yParam R W (localParamR_mem R W hR1)) (yParam R W (localParamR_mem R W hR2)))
      = X₃ R W ha :=
    addX_eq_thirdChordX_of_secant R W ha hz (localParamR_mem R W hR1) (localParamR_mem R W hR2)
      hz₁0 hz₂0 hw hx
  have hX3eq : X₃ R W ha = xParam R W (thirdRootNum_mem R W ha) := by
    rw [X₃_def, xParam, thirdChordW_eq_wParam R W ha hz]
  rw [hx1, hx2, hy1, hy2] at haddX
  have hfinal : 1 < valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) := by
    rw [haddX, hX3eq]
    exact one_lt_valuation_xParam R W (thirdRootNum_mem R W ha) htne
  rw [Affine.Point.add_of_X_ne hxne]
  exact hfinal

end WeierstrassCurve
