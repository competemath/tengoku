/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ThirdChordNonvanishing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Secant additivity with the analytic side conditions discharged (issue #367)

The point-level secant additivity `WeierstrassCurve.localParam_add_of_X_ne`
(`Reduction/ThirdChordAffine.lean`) proves, for `P = (x₁, y₁)`, `Q = (x₂, y₂)` reducing to the
origin with `x₁ ≠ x₂` and `P + Q` also reducing to the origin,
`localParam (P + Q) = adicEvalMv 𝔪 ![z₁, z₂] formalGroupZW` — the additivity of the local
parameter — but it carries **four** non-degeneracy side conditions:

* `hw : w₃ ≠ 0` (the third chord point is not at infinity),
* `hd1, hd2 : X₃ ∉ {x₁, x₂}` (the transported third `x`-coordinate is distinct from the summands),
* `hden : den ≠ 0` (the sum is not `2`-torsion, i.e. `addY ≠ 0`).

Two of these — `hw` and `hden` — are now **unconditional** in the secant case, discharged by the
merged bricks `thirdChordW_ne_zero` (`Reduction/ThirdChordNonvanishing.lean`, PR #92) and
`adicEvalMv_formalGroupDen_ne_zero` (`Reduction/AdditivityValuation.lean`, PR #90).  This file
packages that: `WeierstrassCurve.localParam_add_of_X_ne_of_distinct` states the secant additivity
requiring **only** the genuinely-geometric distinctness `hd1, hd2` (which fail exactly in the
`2P + Q = O` / `P + 2Q = O` configurations, where the third chord point coincides with `±P` / `±Q`).

This is the clean secant-case API the `E₁(K)` subgroup assembly of #367 consumes.

⚠️ This paragraph used to say the surviving `hd1, hd2` would be *"handled by the eventual full case
analysis"*.  **They were not handled; they were removed.**
`WeierstrassCurve.addX_eq_thirdChordX_of_secant` (`Reduction/ThirdChordAffineUncond.lean`, #376)
proves `addX = X₃` as a `(z, w)`-level symmetric-function field identity with no distinctness of
`X₃` at all, and `WeierstrassCurve.localParam_add_of_X_ne_uncond`
(`Reduction/AdditivityUncond.lean`) is this statement with `hd1, hd2` gone.  *The degenerate
configurations were not enumerated; the proof stopped needing to know about them.*  The doubling
(#373) and inverse (`Q = -P`) cases are likewise merged — `localParam_add_of_X_eq_uncond` and
`adicEvalMv_formalGroupZW_eq_zero_of_X_eq` — and the assembly is
`WeierstrassCurve.reducesToZero_add` / `E₁AddEquiv`.

## Main result

* `WeierstrassCurve.localParam_add_of_X_ne_of_distinct` — secant additivity of the local parameter
  with `hw`/`hden` discharged, requiring only `hd1, hd2 : X₃ ∉ {x₁, x₂}`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W]

open Classical in
/-- **Point-level secant additivity of the local parameter, analytic side conditions discharged.**
For two points `P = (x₁, y₁)`, `Q = (x₂, y₂)` reducing to the origin with `x₁ ≠ x₂` (the secant
case), whose affine sum `P + Q` also reduces to the origin,
`localParam (P + Q) = adicEvalMv 𝔪 ![z₁, z₂] formalGroupZW`, requiring **only** the genuinely
geometric distinctness `hd1, hd2 : X₃ ∉ {x₁, x₂}`.

This strengthens `localParam_add_of_X_ne` by discharging its `hw : w₃ ≠ 0` and `hden : den ≠ 0`
hypotheses internally: in the secant case both are unconditional, from `thirdChordW_ne_zero`
(`w₃ = wParam t` with `t ≠ 0`) and `adicEvalMv_formalGroupDen_ne_zero` (`den ≡ 1 mod 𝔪`).  The
remaining `hd1, hd2` fail exactly in the `2P + Q = O` / `P + 2Q = O` configurations and are the
honestly-degenerate conditions the full case analysis of #367 must still address. -/
theorem localParam_add_of_X_ne_of_distinct [W.IsElliptic]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} (hR1 : ReducesToZero R W (.some x₁ y₁ h₁))
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hR2 : ReducesToZero R W (.some x₂ y₂ h₂))
    (hxne : x₁ ≠ x₂)
    (hred : ReducesToZero R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂))
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x₁ y₁ h₁), localParamR R W (.some x₂ y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal)
    (hd1 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR1))
    (hd2 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR2)) :
    localParam R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW) := by
  -- the two parameters are nonzero
  have hz₁0 : localParamR R W (.some x₁ y₁ h₁) ≠ 0 := localParamR_ne_zero_of_reduces R W hR1
  have hz₂0 : localParamR R W (.some x₂ y₂ h₂) ≠ 0 := localParamR_ne_zero_of_reduces R W hR2
  -- the recovered `x`-coordinates are the original ones, so `xParam z₁ ≠ xParam z₂` (the secant
  -- condition on the parameters), which the `hw` discharge consumes
  have hcoord1 : xParam R W (localParamR_mem R W hR1) = x₁
      ∧ yParam R W (localParamR_mem R W hR1) = y₁ := by
    have hpt := pointOfParam_localParamR R W hR1 hz₁0
    simpa only [pointOfParam, Affine.Point.some.injEq] using hpt
  have hcoord2 : xParam R W (localParamR_mem R W hR2) = x₂
      ∧ yParam R W (localParamR_mem R W hR2) = y₂ := by
    have hpt := pointOfParam_localParamR R W hR2 hz₂0
    simpa only [pointOfParam, Affine.Point.some.injEq] using hpt
  have hx : xParam R W (localParamR_mem R W hR1) ≠ xParam R W (localParamR_mem R W hR2) := by
    rw [hcoord1.1, hcoord2.1]; exact hxne
  -- `hw` and `hden` are unconditional in the secant case
  have hw : thirdChordW R W ha ≠ 0 :=
    thirdChordW_ne_zero R W ha (localParamR_mem R W hR1) (localParamR_mem R W hR2) hz₁0 hz₂0 hx
  have hden : adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen ≠ 0 :=
    adicEvalMv_formalGroupDen_ne_zero R W ha
  exact localParam_add_of_X_ne R W hR1 hR2 hxne hred ha hw hd1 hd2 hden

end WeierstrassCurve
