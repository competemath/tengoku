/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.FormalGroupAdditivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The affine↔formal chord line bridge (issue #367, partial)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an
elliptic curve with an integral model.  For two parameters `z₁, z₂ ∈ 𝔪`, the formal-side chord
data `λ = chordSlope`, `ν = chordIntercept` (`Reduction/FormalGroupAdditivity.lean`) are the
slope and intercept of the line `w = λ z + ν` through the two formal points `(zᵢ, w(zᵢ))` in the
`(z, w)`-plane.  This file transports that line to the **affine** `(x, y)`-plane of `W`, where the
reduction theory recovers `x(zᵢ) = zᵢ / w(zᵢ) = xParam`, `y(zᵢ) = -1 / w(zᵢ) = yParam`
(`Reduction/LocalParameterInverse.lean`).

Under `x = z / w`, `y = -1 / w`, the `(z, w)`-line `w = λ z + ν` becomes the **affine line**
`λ x - ν y = 1`.  The results here pin this down — the ingredients the affine-matching rung of
issue #367 (`localParam (P + Q) = z₁ ⊕ z₂`, Silverman AEC IV.1 / VII.2.2) consumes to identify
Mathlib's secant `slope`/`addX`/`addY` with the formal group law of the parameters:

* `WeierstrassCurve.wParam_eq_chordLine₀` / `_₁` — the expansion `w(zᵢ) = λ zᵢ + ν`, i.e. the two
  formal points lie on the chord line (`wLineZero/One_eq_wParam` ∘ `wLineZero/One_eq_chord`).
* `WeierstrassCurve.collinear₀` / `_₁` — the recovered affine points `(xParam zᵢ, yParam zᵢ)` lie
  on the transported line `λ x - ν y = 1`.
* `WeierstrassCurve.chordIntercept_ne_zero_secant` — in the secant case `x(z₁) ≠ x(z₂)` the
  intercept `ν` is nonzero (else the two points would share their `x`-coordinate).
* `WeierstrassCurve.slope_xParam_secant` — **the affine slope is `λ / ν`**: Mathlib's secant slope
  of the two recovered points equals `chordSlope / chordIntercept`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
variable (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)

theorem wParam_eq_chordLine₀ (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal) :
    wParam R W hz₁ = chordSlope R W ha * z₁ + chordIntercept R W ha := by
  rw [← wLineZero_eq_chord R W ha, wLineZero_eq_wParam R W ha hz₁]

theorem wParam_eq_chordLine₁ (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal) :
    wParam R W hz₂ = chordSlope R W ha * z₂ + chordIntercept R W ha := by
  rw [← wLineOne_eq_chord R W ha, wLineOne_eq_wParam R W ha hz₂]

theorem collinear₀ (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal) (hz₁0 : z₁ ≠ 0) :
    algebraMap R K (chordSlope R W ha) * xParam R W hz₁
      - algebraMap R K (chordIntercept R W ha) * yParam R W hz₁ = 1 := by
  have hwne : algebraMap R K (wParam R W hz₁) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz₁ hz₁0)
  have hchord := congrArg (algebraMap R K) (wParam_eq_chordLine₀ R W ha hz₁)
  rw [map_add, map_mul] at hchord
  rw [xParam, yParam]
  field_simp
  linear_combination (-1 : K) * hchord

theorem collinear₁ (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal) (hz₂0 : z₂ ≠ 0) :
    algebraMap R K (chordSlope R W ha) * xParam R W hz₂
      - algebraMap R K (chordIntercept R W ha) * yParam R W hz₂ = 1 := by
  have hwne : algebraMap R K (wParam R W hz₂) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz₂ hz₂0)
  have hchord := congrArg (algebraMap R K) (wParam_eq_chordLine₁ R W ha hz₂)
  rw [map_add, map_mul] at hchord
  rw [xParam, yParam]
  field_simp
  linear_combination (-1 : K) * hchord

theorem chordIntercept_ne_zero_secant (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal)
    (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal) (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0)
    (hx : xParam R W hz₁ ≠ xParam R W hz₂) :
    algebraMap R K (chordIntercept R W ha) ≠ 0 := by
  intro hν
  have hc1 := collinear₀ R W ha hz₁ hz₁0
  have hc2 := collinear₁ R W ha hz₂ hz₂0
  rw [hν, zero_mul, sub_zero] at hc1 hc2
  have hlam : algebraMap R K (chordSlope R W ha) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc1; exact one_ne_zero hc1.symm
  exact hx (mul_left_cancel₀ hlam (hc1.trans hc2.symm))

open Classical in
theorem slope_xParam_secant (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal)
    (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal) (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0)
    (hx : xParam R W hz₁ ≠ xParam R W hz₂) :
    W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂)
      = algebraMap R K (chordSlope R W ha) / algebraMap R K (chordIntercept R W ha) := by
  rw [Affine.slope_of_X_ne hx]
  have hν : algebraMap R K (chordIntercept R W ha) ≠ 0 :=
    chordIntercept_ne_zero_secant R W ha hz₁ hz₂ hz₁0 hz₂0 hx
  have hxne : xParam R W hz₁ - xParam R W hz₂ ≠ 0 := sub_ne_zero.mpr hx
  have hc1 := collinear₀ R W ha hz₁ hz₁0
  have hc2 := collinear₁ R W ha hz₂ hz₂0
  rw [div_eq_div_iff hxne hν]
  linear_combination hc2 - hc1

end WeierstrassCurve
