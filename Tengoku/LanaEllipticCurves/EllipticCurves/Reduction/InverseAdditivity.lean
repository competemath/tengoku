/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.FormalGroupAdditivity
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.AdditivityValuation
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.KernelBijection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vertical additivity: the inverse case of the additivity crux (issue #367)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  For two points `P₁ = (x, y₁)`,
`P₂ = (x, y₂)` reducing to the origin that share the **same `x`-coordinate** — geometrically
`P₂ = -P₁` (unless `P₁ = P₂`) — the chord through them in the `(z, w)`-plane passes through the
origin `O`, so its third intersection with the curve is `O` itself.  In formal-group terms the sum
`z(P₁) ⊕ z(P₂)` vanishes:

```
adicEvalMv 𝔪 ![z(P₁), z(P₂)] formalGroupZW = 0,
```

the **vertical additivity** that closes the inverse case `Q = -P` of the additivity identity
`z(P + Q) = z(P) ⊕ z(Q)` (there `P + Q = O`, so `z(P + Q) = 0`).

The proof needs no third-chord root-extraction.  Writing `λ`, `ν` for the numeric chord slope and
intercept, `A = φ formalGroupLead`, `S = φ formalGroupSub`, `t = φ formalThirdRoot`:

* the intercept `ν = 0`, because negation fixes the `x`-coordinate, so
  `x(z₁) = x(z₂)` forces the chord line `w = λ z + ν` through the two curve points to pass through
  the origin (`chordIntercept_eq_zero_of_X_eq`);
* with `ν = 0` both `z₁, z₂` are nonzero roots of `A z² + S z − λ`, whence
  `A (z₁ + z₂) + S = 0`, and Vieta's relation `A (t + z₁ + z₂) + S = 0` gives `A t = 0`, i.e.
  `t = 0` (`A` is a unit) — the third root is the origin (`thirdRootNum_eq_zero_of_X_eq`);
* finally `den · φ formalGroupZW = -t = 0` with `den ≠ 0` gives the vanishing
  (`adicEvalMv_formalGroupZW_eq_zero_of_X_eq`).

## Main results

* `WeierstrassCurve.chordIntercept_eq_zero_of_X_eq` — `ν = 0` for two equal-`x` points.
* `WeierstrassCurve.thirdRootNum_eq_zero_of_X_eq` — `t = 0`.
* `WeierstrassCurve.adicEvalMv_formalGroupZW_eq_zero_of_X_eq` — vertical additivity.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]

/-- **The chord intercept vanishes for two points sharing an `x`-coordinate.**  With
`z₁ = z(P₁)`, `z₂ = z(P₂)` the local parameters of two points `P₁ = (x, y₁)`, `P₂ = (x, y₂)`
reducing to the origin, the numeric chord intercept `ν = φ formalGroupNu` is `0`: recovered points
have
`x(z₁) = x = x(z₂)`, so the chord line `w = λ z + ν` through `(z₁, w(z₁))`, `(z₂, w(z₂))` passes
through the origin. -/
theorem chordIntercept_eq_zero_of_X_eq
    {x y₁ y₂ : K} {h₁ : W.toAffine.Nonsingular x y₁} {h₂ : W.toAffine.Nonsingular x y₂}
    (hx : 1 < valuation K (maximalIdeal R) x)
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x y₁ h₁), localParamR R W (.some x y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal)
    (hz12 : localParamR R W (.some x y₁ h₁) ≠ localParamR R W (.some x y₂ h₂)) :
    chordIntercept R W ha = 0 := by
  set z₁ := localParamR R W (.some x y₁ h₁) with hz1d
  set z₂ := localParamR R W (.some x y₂ h₂) with hz2d
  have hz1ne : z₁ ≠ 0 := localParamR_ne_zero_of_reduces R W (h := h₁) hx
  have hz2ne : z₂ ≠ 0 := localParamR_ne_zero_of_reduces R W (h := h₂) hx
  have hz1m : z₁ ∈ (maximalIdeal R).asIdeal := by simpa using ha 0
  have hz2m : z₂ ∈ (maximalIdeal R).asIdeal := by simpa using ha 1
  -- the recovered `x`-coordinates are the common `x`
  have hxP1 : xParam R W hz1m = x := by
    have hpt := pointOfParam_localParamR R W hx hz1ne
    simp only [pointOfParam, Affine.Point.some.injEq] at hpt
    exact hpt.1
  have hxP2 : xParam R W hz2m = x := by
    have hpt := pointOfParam_localParamR R W hx hz2ne
    simp only [pointOfParam, Affine.Point.some.injEq] at hpt
    exact hpt.1
  have hw1 : algebraMap R K (wParam R W hz1m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz1m hz1ne)
  have hw2 : algebraMap R K (wParam R W hz2m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz2m hz2ne)
  -- `w(z₁) · z₂ = w(z₂) · z₁` (equal slopes from the origin, since the `x`-coordinates agree)
  have hcross : wParam R W hz1m * z₂ = wParam R W hz2m * z₁ := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul]
    have hxe : xParam R W hz1m = xParam R W hz2m := by rw [hxP1, hxP2]
    rw [xParam, xParam, div_eq_div_iff hw1 hw2] at hxe
    linear_combination -hxe
  -- the two chord equations `w(zᵢ) = λ zᵢ + ν`
  have hE1 : wParam R W hz1m = chordSlope R W ha * z₁ + chordIntercept R W ha := by
    rw [← wLineZero_eq_wParam R W ha hz1m]; exact wLineZero_eq_chord R W ha
  have hE2 : wParam R W hz2m = chordSlope R W ha * z₂ + chordIntercept R W ha := by
    rw [← wLineOne_eq_wParam R W ha hz2m]; exact wLineOne_eq_chord R W ha
  -- eliminate `w` to get `ν · (z₂ - z₁) = 0`
  have hkey : chordIntercept R W ha * (z₂ - z₁) = 0 := by
    linear_combination -z₂ * hE1 + z₁ * hE2 + hcross
  rcases mul_eq_zero.mp hkey with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hz12

/-- **The third chord root is the origin for two equal-`x` points.**  With the intercept `ν = 0`
(`chordIntercept_eq_zero_of_X_eq`), both parameters `z₁, z₂` are nonzero roots of the quadratic
`A z² + S z − λ`, so `A (z₁ + z₂) + S = 0`; Vieta's relation `A (t + z₁ + z₂) + S = 0` then gives
`A t = 0`, and `A` is a unit, so the numeric third root `t = φ formalThirdRoot` vanishes. -/
theorem thirdRootNum_eq_zero_of_X_eq
    {x y₁ y₂ : K} {h₁ : W.toAffine.Nonsingular x y₁} {h₂ : W.toAffine.Nonsingular x y₂}
    (hx : 1 < valuation K (maximalIdeal R) x)
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x y₁ h₁), localParamR R W (.some x y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal)
    (hz12 : localParamR R W (.some x y₁ h₁) ≠ localParamR R W (.some x y₂ h₂)) :
    thirdRootNum R W ha = 0 := by
  set z₁ := localParamR R W (.some x y₁ h₁) with hz1d
  set z₂ := localParamR R W (.some x y₂ h₂) with hz2d
  have hz1ne : z₁ ≠ 0 := localParamR_ne_zero_of_reduces R W (h := h₁) hx
  have hz2ne : z₂ ≠ 0 := localParamR_ne_zero_of_reduces R W (h := h₂) hx
  have hz1m : z₁ ∈ (maximalIdeal R).asIdeal := by simpa using ha 0
  have hz2m : z₂ ∈ (maximalIdeal R).asIdeal := by simpa using ha 1
  have hnu : chordIntercept R W ha = 0 := chordIntercept_eq_zero_of_X_eq R W hx ha hz12
  -- the chord line, with `ν = 0`, is `w = λ z`
  have hwl0 : wLineZero R W ha = chordSlope R W ha * z₁ := by
    rw [wLineZero_eq_chord, hnu, add_zero]
  have hwl1 : wLineOne R W ha = chordSlope R W ha * z₂ := by
    rw [wLineOne_eq_chord, hnu, add_zero]
  -- the numeric collinearity equations become cubics in `z₁, z₂` on the line `w = λ z`
  have hf1 := wLineZero_functional_eq R W ha
  rw [hwl0] at hf1
  have hf2 := wLineOne_functional_eq R W ha
  rw [hwl1] at hf2
  have hAcf := adicEvalMv_formalGroupLead R W ha
  have hScf := adicEvalMv_formalGroupSub R W ha
  have hvieta := formalThirdRoot_vieta R W ha
  have hlead := (integralModel R W).ringHom_formalGroupLead_mul_inv
    (adicEvalMv (maximalIdeal R).asIdeal ha)
  set A := adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupLead with hAd
  set S := adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupSub with hSd
  set lam := chordSlope R W ha with hlamd
  -- `zᵢ` is a nonzero root of `A z² + S z − λ`
  have hqz1 : A * z₁ ^ 2 + S * z₁ - lam = 0 := by
    have hcube : z₁ * (A * z₁ ^ 2 + S * z₁ - lam) = 0 := by
      rw [hAcf, hScf, hnu]; linear_combination -hf1
    rcases mul_eq_zero.mp hcube with h | h
    · exact absurd h hz1ne
    · exact h
  have hqz2 : A * z₂ ^ 2 + S * z₂ - lam = 0 := by
    have hcube : z₂ * (A * z₂ ^ 2 + S * z₂ - lam) = 0 := by
      rw [hAcf, hScf, hnu]; linear_combination -hf2
    rcases mul_eq_zero.mp hcube with h | h
    · exact absurd h hz2ne
    · exact h
  -- the two-root relation `A (z₁ + z₂) + S = 0`
  have hsum : A * (z₁ + z₂) + S = 0 := by
    have hfac : (z₁ - z₂) * (A * (z₁ + z₂) + S) = 0 := by linear_combination hqz1 - hqz2
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hz12
    · exact h
  -- Vieta `A (t + z₁ + z₂) + S = 0` minus the two-root relation gives `A · t = 0`
  have hAt : A * thirdRootNum R W ha = 0 := by linear_combination hvieta - hsum
  have hAne : A ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hlead; exact one_ne_zero hlead.symm
  rcases mul_eq_zero.mp hAt with h | h
  · exact absurd h hAne
  · exact h

/-- **Vertical additivity — the inverse case of the additivity crux.**  For two points
`P₁ = (x, y₁)`, `P₂ = (x, y₂)` reducing to the origin with a common `x`-coordinate and distinct
local parameters (`P₂ = -P₁`), the formal-group sum of their local parameters vanishes:
`adicEvalMv 𝔪 ![z(P₁), z(P₂)] formalGroupZW = 0`.  Equivalently `z(P₁) ⊕ z(P₂) = 0` in `Ê(𝔪)`,
matching the affine fact `P₁ + P₂ = O`.  This is the formal-side input the inverse case
`Q = -P` of `z(P + Q) = z(P) ⊕ z(Q)` (issue #367) consumes. -/
theorem adicEvalMv_formalGroupZW_eq_zero_of_X_eq
    {x y₁ y₂ : K} {h₁ : W.toAffine.Nonsingular x y₁} {h₂ : W.toAffine.Nonsingular x y₂}
    (hx : 1 < valuation K (maximalIdeal R) x)
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x y₁ h₁), localParamR R W (.some x y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal)
    (hz12 : localParamR R W (.some x y₁ h₁) ≠ localParamR R W (.some x y₂ h₂)) :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW = 0 := by
  have ht : thirdRootNum R W ha = 0 := thirdRootNum_eq_zero_of_X_eq R W hx ha hz12
  have hden := formalGroupDen_mul_adicEvalMv_formalGroupZW R W ha
  rw [ht, neg_zero] at hden
  rcases mul_eq_zero.mp hden with h | h
  · exact absurd h (adicEvalMv_formalGroupDen_ne_zero R W ha)
  · exact h

end WeierstrassCurve
