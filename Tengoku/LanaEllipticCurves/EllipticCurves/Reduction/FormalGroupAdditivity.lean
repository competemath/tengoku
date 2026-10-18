/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.FormalGroupEval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The additivity crux `z(P + Q) = F_E(z P, z Q)` — the chord matching (issue #367)

Building on the formal-side numeric evaluation of `formalGroupZW` (`Reduction/FormalGroupEval.lean`,
rung (a) of the #361 crux), this file supplies the numeric chord data of the pole-free law: the
value `adicEvalMv 𝔪 ![z₁, z₂] formalGroupZW` unfolds through the chord construction in the
`(z, w)`-plane.  This is the formal-side input to the affine matching (rung (b)).

The chord data of the pole-free law `formalGroupZW` are, under the ring homomorphism
`φ = adicEvalMv 𝔪 ![z₁, z₂]`, numeric quantities in the `(z, w)`-plane:

* `λ = φ formalWDividedDiff`, `ν = φ formalGroupNu` — the slope and intercept of the chord line
  `w = λ z + ν` through the two formal points `(z₁, w(z₁))`, `(z₂, w(z₂))` (pinned to the
  coordinate expansion by `wLineZero_eq_wParam` / `wLineOne_eq_wParam`).
* `A = φ formalGroupLead = 1 + a₂λ + a₄λ² + a₆λ³` — the leading coefficient of the cubic obtained
  by substituting the line into the Weierstrass functional equation.
* `S = φ formalGroupSub` — its `z²`-coefficient.
* `t = φ formalThirdRoot = -S·A⁻¹ - z₁ - z₂` — the Vieta **third root** of that cubic.

The main results here:

* `WeierstrassCurve.adicEvalMv_formalGroupLead` / `_formalGroupSub` — the numeric closed forms of
  the cubic's leading and sub-leading coefficients.
* `WeierstrassCurve.formalThirdRoot_vieta` — the Vieta relation `A·(t + z₁ + z₂) + S = 0`.
* `WeierstrassCurve.thirdChordPoint_functional_eq` — **the third chord point is on the curve**:
  the pair `(t, λt + ν)` solves the numeric Weierstrass functional equation.  This is the geometric
  heart of the addition law (Silverman AEC IV.1): the line through two curve points meets the curve
  in a third point, obtained here by Vieta from the two known intersections.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open MvPowerSeries IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]

section Numeric

variable (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
variable (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)

/-- The numeric slope of the chord line in the `(z, w)`-plane: `λ = φ formalWDividedDiff`. -/
noncomputable def chordSlope : R :=
  adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalWDividedDiff

/-- The numeric intercept of the chord line in the `(z, w)`-plane: `ν = φ formalGroupNu`. -/
noncomputable def chordIntercept : R :=
  adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupNu

omit [IsFractionRing R K] in
/-- The chord line value at `z₁` unfolds to `λ z₁ + ν`. -/
theorem wLineZero_eq_chord :
    wLineZero R W ha = chordSlope R W ha * z₁ + chordIntercept R W ha := by
  rw [wLineZero, chordSlope, chordIntercept, map_add, map_mul, adicEvalMv_X]
  rfl

omit [IsFractionRing R K] in
/-- The chord line value at `z₂` unfolds to `λ z₂ + ν`. -/
theorem wLineOne_eq_chord : wLineOne R W ha = chordSlope R W ha * z₂ + chordIntercept R W ha := by
  rw [wLineOne, chordSlope, chordIntercept, map_add, map_mul, adicEvalMv_X]
  rfl

omit [IsFractionRing R K] in
/-- Numeric closed form of the cubic's leading coefficient `A = φ formalGroupLead`. -/
theorem adicEvalMv_formalGroupLead :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupLead =
      1 + (integralModel R W).a₂ * chordSlope R W ha
        + (integralModel R W).a₄ * chordSlope R W ha ^ 2
        + (integralModel R W).a₆ * chordSlope R W ha ^ 3 := by
  rw [formalGroupLead, chordSlope]
  simp only [map_add, map_mul, map_pow, map_one, adicEvalMv_C]

omit [IsFractionRing R K] in
/-- Numeric closed form of the cubic's `z²`-coefficient `S = φ formalGroupSub`. -/
theorem adicEvalMv_formalGroupSub :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupSub =
      (integralModel R W).a₁ * chordSlope R W ha
        + (integralModel R W).a₂ * chordIntercept R W ha
        + (integralModel R W).a₃ * chordSlope R W ha ^ 2
        + 2 * (integralModel R W).a₄ * chordSlope R W ha * chordIntercept R W ha
        + 3 * (integralModel R W).a₆ * chordSlope R W ha ^ 2 * chordIntercept R W ha := by
  rw [formalGroupSub, chordSlope, chordIntercept]
  simp only [map_add, map_mul, map_pow, map_ofNat, adicEvalMv_C]

/-- The numeric Vieta third root `t = φ formalThirdRoot`. -/
noncomputable def thirdRootNum : R :=
  adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalThirdRoot

omit [IsFractionRing R K] in
/-- **The Vieta relation for the third root.** With `A = φ formalGroupLead`, `S = φ formalGroupSub`
and `t = φ formalThirdRoot`, one has `A·(t + z₁ + z₂) + S = 0` — the statement that `t` is the
third root of the cubic `A z³ + S z² + ⋯` complementary to the two known roots `z₁, z₂`. -/
theorem formalThirdRoot_vieta :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupLead
        * (thirdRootNum R W ha + z₁ + z₂)
      + adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupSub = 0 := by
  have hA := (integralModel R W).ringHom_formalGroupLead_mul_inv
    (adicEvalMv (maximalIdeal R).asIdeal ha)
  rw [thirdRootNum, formalThirdRoot]
  simp only [map_sub, map_neg, map_mul, adicEvalMv_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- goal now involves A * (-(S * A⁻¹) - z₁ - z₂ + z₁ + z₂) + S ; use A * A⁻¹ = 1
  set A := adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupLead
  set S := adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupSub
  linear_combination (-S) * hA

omit [IsFractionRing R K] in
/-- **The third chord point is on the curve.** With `λ = φ formalWDividedDiff`,
`ν = φ formalGroupNu`, and `t = φ formalThirdRoot`, the pair `(t, λ t + ν)` solves the numeric
Weierstrass functional equation.  This is the geometric heart of the addition law: the chord through
the two curve points `(z₁, w(z₁))`, `(z₂, w(z₂))` meets the `(z, w)`-curve in a third point,
obtained by Vieta from the two known intersections (`wLineZero/One_functional_eq` +
`formalThirdRoot_vieta`).  Requires `z₁ ≠ z₂` (the secant case). -/
theorem thirdChordPoint_functional_eq (hz : z₁ ≠ z₂) :
    chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha
      = thirdRootNum R W ha ^ 3
        + ((integralModel R W).a₁ * thirdRootNum R W ha
            + (integralModel R W).a₂ * thirdRootNum R W ha ^ 2)
          * (chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha)
        + ((integralModel R W).a₃ + (integralModel R W).a₄ * thirdRootNum R W ha)
          * (chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha) ^ 2
        + (integralModel R W).a₆
          * (chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha) ^ 3 := by
  set lam := chordSlope R W ha with hlam
  set nu := chordIntercept R W ha with hnu
  set t := thirdRootNum R W ha with ht
  have h1 := wLineZero_functional_eq R W ha
  rw [wLineZero_eq_chord R W ha, ← hlam, ← hnu] at h1
  have h2 := wLineOne_functional_eq R W ha
  rw [wLineOne_eq_chord R W ha, ← hlam, ← hnu] at h2
  have r0 := formalThirdRoot_vieta R W ha
  rw [adicEvalMv_formalGroupLead R W ha, adicEvalMv_formalGroupSub R W ha, ← hlam, ← hnu, ← ht]
    at r0
  refine mul_left_cancel₀ (sub_ne_zero.mpr hz) ?_
  linear_combination ((z₁ - z₂) + (t - z₁)) * h1 - (t - z₁) * h2
    - (z₁ - z₂) * (t - z₁) * (t - z₂) * r0

omit [IsFractionRing R K] in
/-- Numeric closed form of the negation denominator `den = φ formalGroupDen`, in terms of the third
root `t`, the chord slope `λ` and intercept `ν`: `den = 1 - a₁ t - a₃ (λ t + ν)`.  Here `λ t + ν`
is the `w`-coordinate of the third chord point. -/
theorem adicEvalMv_formalGroupDen :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen =
      1 - (integralModel R W).a₁ * thirdRootNum R W ha
        - (integralModel R W).a₃
          * (chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha) := by
  rw [formalGroupDen, thirdRootNum, chordSlope, chordIntercept]
  simp only [map_sub, map_add, map_mul, map_one, adicEvalMv_C]

omit [IsFractionRing R K] in
/-- **The numeric formal group law is `-t / den`.**  The `𝔪`-adic value of `formalGroupZW`
satisfies `den · φ formalGroupZW = -t`, where `t = φ formalThirdRoot` is the third chord root and
`den = φ formalGroupDen` is the negation denominator.  Combined with the closed forms for `den`
and `t`, this expresses the formal sum `z₁ ⊕ z₂` as the numeric inversion of the third chord
point — the last formal-side ingredient before the affine matching. -/
theorem formalGroupDen_mul_adicEvalMv_formalGroupZW :
    adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen
        * adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW
      = -thirdRootNum R W ha := by
  have hden := (integralModel R W).ringHom_formalGroupDen_mul_inv
    (adicEvalMv (maximalIdeal R).asIdeal ha)
  rw [formalGroupZW, thirdRootNum]
  simp only [map_mul, map_neg]
  set den := adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen
  set deninv :=
    adicEvalMv (maximalIdeal R).asIdeal ha (invOfUnit (integralModel R W).formalGroupDen 1)
  set t := adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalThirdRoot
  linear_combination (-t) * hden

end Numeric

end WeierstrassCurve
