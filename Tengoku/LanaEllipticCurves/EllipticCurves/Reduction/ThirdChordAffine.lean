/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.ChordAffineBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The third chord point on the affine curve and the secant coordinate identity (issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  For two parameters `z₁, z₂ ∈ 𝔪` with `z₁ ≠ z₂`, the formal-side
addition law (`Reduction/FormalGroupAdditivity.lean`) produces the **third chord point** in the
`(z, w)`-plane: the pair `(t, w₃)` with `t = thirdRootNum` the Vieta third root and
`w₃ = λ t + ν = thirdChordW` the value of the chord line there.  This file transports that point to
the **affine** `(x, y)`-plane and identifies it with Mathlib's affine third-intersection point
`addX`/`addY`, closing the coordinate-level additivity of the local parameter.

Concretely, writing `X₃ = t / w₃`, `Y₃ = -1 / w₃` for the affine image (via `x = z/w`, `y = -1/w`):

* `WeierstrassCurve.equation_thirdChordPoint` — `(X₃, Y₃)` lies on the affine curve (the numeric
  transport of `thirdChordPoint_functional_eq`, mirroring `equation_xParam_yParam`).
* `WeierstrassCurve.thirdChord_on_secantLine` — `(X₃, Y₃)` lies on the affine secant line through
  the two recovered points `(xParam zᵢ, yParam zᵢ)`, i.e. `Y₃ = ℓ (X₃ - x₁) + y₁` with
  `ℓ = W.slope` the affine slope (`= λ / ν`, `slope_xParam_secant`).
* `WeierstrassCurve.Affine.addPolynomial_eval_eq_zero_of_equation` — a general fact: a curve point
  on the line `Y = ℓ(X - x₁) + y₁` is a root of the addition polynomial.
* `WeierstrassCurve.addX_eq_thirdChordX` — **the coordinate identity `addX · w₃ = t`**: Mathlib's
  affine `addX` of the two recovered points equals the transported third-root `x`-coordinate
  `X₃ = t / w₃` (in the generic secant case, where `X₃ ∉ {x₁, x₂}`).  This is the affine matching
  the addition law hinges on (Silverman AEC IV.1 / VII.2.2).
* `WeierstrassCurve.localParam_add_secant` — **the coordinate-level additivity**:
  `-addX / addY = z₁ ⊕ z₂` in `K`, where `z₁ ⊕ z₂ = adicEvalMv 𝔪 ![z₁, z₂] formalGroupZW` is the
  formal group law of the parameters.
* `WeierstrassCurve.localParam_add_of_X_ne` — the **point-level** secant additivity
  `z(P + Q) = z(P) ⊕ z(Q)`, carrying the four non-degeneracy side conditions its sibling files then
  discharge.  (⚠️ It was missing from this list.)

⚠️ The `localParam_add_secant` bullet used to end *"The remaining work for #367 is the point-level
assembly (`P + Q = some (addX) (addY)` via `Point.add_of_X_ne`, the degenerate/doubling cases, and
the `ReducesToZero` subgroup closure)."*  **All three are merged**: the point-level secant and
doubling identities are `WeierstrassCurve.localParam_add_of_X_ne_uncond` /
`localParam_add_of_X_eq_uncond`
(`Reduction/AdditivityUncond.lean`), the degenerate configurations were removed rather than
enumerated (`addX_eq_thirdChordX_of_secant`, `Reduction/ThirdChordAffineUncond.lean`, #376), and the
closure is `WeierstrassCurve.reducesToZero_add` / `E₁` (`Reduction/KernelAddClosure.lean`), from
which `E₁AddEquiv` (`Reduction/KernelFormalGroupIso.lean`) closes #367/#368.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- **A curve point on the secant line is a root of the addition polynomial.**  If `(X₃, Y₃)` lies
on the Weierstrass curve and on the line `Y = ℓ (X - x₁) + y₁`, then `X₃` is a root of the addition
polynomial `addPolynomial x₁ y₁ ℓ` (whose roots are the `x`-coordinates of the three intersections
of that line with the curve). -/
theorem addPolynomial_eval_eq_zero_of_equation (W : WeierstrassCurve.Affine F)
    {x₁ y₁ ℓ X₃ Y₃ : F} (hline : Y₃ = ℓ * (X₃ - x₁) + y₁) (hcurve : W.Equation X₃ Y₃) :
    (W.addPolynomial x₁ y₁ ℓ).eval X₃ = 0 := by
  rw [equation_iff] at hcurve
  rw [addPolynomial_eq]
  subst hline
  simp only [Cubic.toPoly, eval_neg, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination hcurve

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z₁ z₂ : R}
variable (ha : ∀ s : Fin 2, ![z₁, z₂] s ∈ (maximalIdeal R).asIdeal)

/-- The `w`-coordinate of the third chord point in the `(z, w)`-plane: `w₃ = λ t + ν`, where
`λ = chordSlope`, `ν = chordIntercept` and `t = thirdRootNum` is the Vieta third root. -/
noncomputable def thirdChordW : R :=
  chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha

omit [IsFractionRing R K] in
theorem thirdChordW_eq :
    thirdChordW R W ha = chordSlope R W ha * thirdRootNum R W ha + chordIntercept R W ha :=
  rfl

omit [IsFractionRing R K] in
/-- **The third chord point satisfies the Weierstrass functional equation.**  In the form of the
numeric functional equation for `wParam`, but at the third-root point `(t, w₃)`: this is the
statement that `(t, w₃)` lies on the `(z, w)`-curve (`thirdChordPoint_functional_eq`, restated in
terms of `thirdChordW`). -/
theorem thirdChord_functional_eq (hz : z₁ ≠ z₂) :
    thirdChordW R W ha = thirdRootNum R W ha ^ 3
      + ((integralModel R W).a₁ * thirdRootNum R W ha
          + (integralModel R W).a₂ * thirdRootNum R W ha ^ 2) * thirdChordW R W ha
      + ((integralModel R W).a₃ + (integralModel R W).a₄ * thirdRootNum R W ha)
          * thirdChordW R W ha ^ 2
      + (integralModel R W).a₆ * thirdChordW R W ha ^ 3 := by
  simp only [thirdChordW]
  linear_combination thirdChordPoint_functional_eq R W ha hz

omit [IsFractionRing R K] in
/-- The `K`-image of the numeric functional equation for the third chord point, in the curve's own
coefficients `W.aᵢ = algebraMap R K (integralModel R W).aᵢ`.  Mirrors
`algebraMap_wParam_functional_eq`. -/
private theorem algebraMap_thirdChord_functional_eq (hz : z₁ ≠ z₂) :
    algebraMap R K (thirdChordW R W ha) = algebraMap R K (thirdRootNum R W ha) ^ 3
      + (W.a₁ * algebraMap R K (thirdRootNum R W ha)
          + W.a₂ * algebraMap R K (thirdRootNum R W ha) ^ 2) * algebraMap R K (thirdChordW R W ha)
      + (W.a₃ + W.a₄ * algebraMap R K (thirdRootNum R W ha))
          * algebraMap R K (thirdChordW R W ha) ^ 2
      + W.a₆ * algebraMap R K (thirdChordW R W ha) ^ 3 := by
  have h := congrArg (algebraMap R K) (thirdChord_functional_eq R W ha hz)
  simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
    integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at h
  exact h

/-- **The affine third chord point lies on the curve.**  The transported point
`(X₃, Y₃) = (t / w₃, -1 / w₃)` satisfies the Weierstrass equation of `W`.  Numeric transport of
`thirdChordPoint_functional_eq`, mirroring `equation_xParam_yParam`.  Requires `w₃ ≠ 0` (the third
point is not at infinity, i.e. `P + Q ≠ O`) and `z₁ ≠ z₂` (the secant case). -/
theorem equation_thirdChordPoint (hz : z₁ ≠ z₂) (hw : thirdChordW R W ha ≠ 0) :
    W.toAffine.Equation (algebraMap R K (thirdRootNum R W ha) / algebraMap R K (thirdChordW R W ha))
      (-1 / algebraMap R K (thirdChordW R W ha)) := by
  have hwne : algebraMap R K (thirdChordW R W ha) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hfe := algebraMap_thirdChord_functional_eq R W ha hz
  rw [Affine.equation_iff]
  field_simp
  linear_combination hfe

omit [IsFractionRing R K] in
/-- The numerator collinearity relation for the third chord point: `λ t + ν = w₃` in `K`. -/
theorem thirdChord_line_num :
    algebraMap R K (chordSlope R W ha) * algebraMap R K (thirdRootNum R W ha)
      + algebraMap R K (chordIntercept R W ha) = algebraMap R K (thirdChordW R W ha) := by
  rw [thirdChordW, map_add, map_mul]

/-- The affine third-chord `x`-coordinate `X₃ = t / w₃` — the transported `x`-coordinate of the
third chord point `(t, w₃)` under `x = z / w`.  Public so that downstream assembly can state the
genuinely-degenerate distinctness side conditions `X₃ ∉ {x₁, x₂}` (which fail exactly in the
`2P + Q = O` / `P + 2Q = O` configurations). -/
noncomputable def X₃ : K :=
  algebraMap R K (thirdRootNum R W ha) / algebraMap R K (thirdChordW R W ha)

omit [IsFractionRing R K] in
theorem X₃_def :
    X₃ R W ha = algebraMap R K (thirdRootNum R W ha) / algebraMap R K (thirdChordW R W ha) :=
  rfl

section Secant

variable (hz : z₁ ≠ z₂) (hz₁ : z₁ ∈ (maximalIdeal R).asIdeal)
  (hz₂ : z₂ ∈ (maximalIdeal R).asIdeal) (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0)
  (hw : thirdChordW R W ha ≠ 0) (hx : xParam R W hz₁ ≠ xParam R W hz₂)

include hz₁0 hz₂0 hw hx in
open Classical in
/-- **The affine third chord point lies on the secant line** through the two recovered points.
Writing `X₃ = t / w₃`, `Y₃ = -1 / w₃` and `ℓ = W.slope (…)` (the affine secant slope `= λ / ν`),
one has `Y₃ = ℓ (X₃ - x₁) + y₁`.  Consequence of the two collinearity relations
(`collinear₀`, `thirdChord_line_num`) and `slope_xParam_secant`. -/
theorem thirdChord_on_secantLine :
    -1 / algebraMap R K (thirdChordW R W ha)
      = W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂)
          * (X₃ R W ha - xParam R W hz₁)
        + yParam R W hz₁ := by
  rw [slope_xParam_secant R W ha hz₁ hz₂ hz₁0 hz₂0 hx, X₃_def]
  have hν := chordIntercept_ne_zero_secant R W ha hz₁ hz₂ hz₁0 hz₂0 hx
  have hwne : algebraMap R K (thirdChordW R W ha) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hc0 := collinear₀ R W ha hz₁ hz₁0
  have hnum := thirdChord_line_num R W ha
  field_simp
  linear_combination algebraMap R K (thirdChordW R W ha) * hc0 - hnum

include hz hz₁0 hz₂0 hw hx in
open Classical in
/-- **The coordinate identity `addX = X₃` (i.e. `addX · w₃ = t`).**  In the generic secant case
(`z₁ ≠ z₂`, `xParam z₁ ≠ xParam z₂`, and the transported third `x`-coordinate `X₃ = t / w₃`
distinct from `x₁`, `x₂`), Mathlib's affine third-intersection `x`-coordinate `addX` of the two
recovered points equals `X₃`.  This is the affine matching at the heart of the addition law
(Silverman AEC IV.1): the chord meets the curve in exactly the third point `(X₃, Y₃)`. -/
theorem addX_eq_thirdChordX
    (hd1 : X₃ R W ha ≠ xParam R W hz₁) (hd2 : X₃ R W ha ≠ xParam R W hz₂) :
    W.toAffine.addX (xParam R W hz₁) (xParam R W hz₂)
        (W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂))
      = X₃ R W ha := by
  have h₁ := equation_xParam_yParam R W hz₁ hz₁0
  have h₂ := equation_xParam_yParam R W hz₂ hz₂0
  have hxy : ¬(xParam R W hz₁ = xParam R W hz₂ ∧
      yParam R W hz₁ = W.toAffine.negY (xParam R W hz₂) (yParam R W hz₂)) := fun h => hx h.1
  have hline : (-1 / algebraMap R K (thirdChordW R W ha))
      = W.toAffine.slope (xParam R W hz₁) (xParam R W hz₂) (yParam R W hz₁) (yParam R W hz₂)
          * (X₃ R W ha - xParam R W hz₁) + yParam R W hz₁ :=
    thirdChord_on_secantLine R W ha hz₁ hz₂ hz₁0 hz₂0 hw hx
  have hcurve : W.toAffine.Equation (X₃ R W ha) (-1 / algebraMap R K (thirdChordW R W ha)) :=
    equation_thirdChordPoint R W ha hz hw
  have hroot := W.toAffine.addPolynomial_eval_eq_zero_of_equation hline hcurve
  rw [W.toAffine.addPolynomial_slope h₁ h₂ hxy] at hroot
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C, neg_eq_zero] at hroot
  rcases mul_eq_zero.mp hroot with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hd1
    · exact absurd (sub_eq_zero.mp h') hd2
  · exact (sub_eq_zero.mp h).symm

include hz hz₁0 hz₂0 hw hx in
open Classical in
/-- **The coordinate-level additivity of the local parameter (generic secant case).**
`-addX / addY = z₁ ⊕ z₂` in `K`, where the left side is the local parameter `-x/y` of the affine
sum point `(addX, addY)` of the two recovered points `(xParam zᵢ, yParam zᵢ)`, and the right side
is the formal group law `z₁ ⊕ z₂ = adicEvalMv 𝔪 ![z₁, z₂] formalGroupZW` of the parameters.  This
is the affine-matching identity that #367 hinges on (Silverman AEC IV.1 / VII.2.2): combining the
coordinate identity `addX = t / w₃` (`addX_eq_thirdChordX`) with the numeric inversion
`den · (z₁ ⊕ z₂) = -t` (`formalGroupDen_mul_adicEvalMv_formalGroupZW`).  Hypotheses: the secant
non-degeneracy (`z₁ ≠ z₂`, `xParam z₁ ≠ xParam z₂`, `X₃ ∉ {x₁, x₂}`, `w₃ ≠ 0`) and `den ≠ 0`
(`addY ≠ 0`, i.e. `P + Q` is not `2`-torsion). -/
theorem localParam_add_secant
    (hd1 : X₃ R W ha ≠ xParam R W hz₁) (hd2 : X₃ R W ha ≠ xParam R W hz₂)
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
  have haddX := addX_eq_thirdChordX R W ha hz hz₁ hz₂ hz₁0 hz₂0 hw hx hd1 hd2
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

end Secant

open Classical in
/-- **Point-level secant additivity of the local parameter (generic case).**  For two points
`P = (x₁, y₁)`, `Q = (x₂, y₂)` reducing to the origin with `x₁ ≠ x₂` (the secant case), whose affine
sum `P + Q` also reduces to the origin, the local parameter of the sum equals the formal group law
of the parameters:
`z(P + Q) = z₁ ⊕ z₂ = adicEvalMv 𝔪 ![z₁, z₂] formalGroupZW`, where `zᵢ = localParamR R W Pᵢ`.
Combining Mathlib's affine addition (`Point.add_of_X_ne`, the sum is `(addX, addY)`) with the
coordinate identity `localParam_add_secant`.  Conditional on the non-degeneracy hypotheses of that
identity (`w₃ ≠ 0`, `X₃ ∉ {x₁, x₂}`, `den ≠ 0`) and on the sum reducing to the origin; discharging
those (and the doubling / inverse cases) completes the `E₁(K)` subgroup closure of #367. -/
theorem localParam_add_of_X_ne [W.IsElliptic]
    {x₁ y₁ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} (hR1 : ReducesToZero R W (.some x₁ y₁ h₁))
    {x₂ y₂ : K} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hR2 : ReducesToZero R W (.some x₂ y₂ h₂))
    (hxne : x₁ ≠ x₂)
    (hred : ReducesToZero R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂))
    (ha : ∀ s : Fin 2,
        ![localParamR R W (.some x₁ y₁ h₁), localParamR R W (.some x₂ y₂ h₂)] s
          ∈ (maximalIdeal R).asIdeal)
    (hw : thirdChordW R W ha ≠ 0)
    (hd1 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR1))
    (hd2 : X₃ R W ha ≠ xParam R W (localParamR_mem R W hR2))
    (hden : adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupDen ≠ 0) :
    localParam R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal ha (integralModel R W).formalGroupZW) := by
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
  -- and the parameters themselves are distinct (via injectivity of `zParam` and `x₁ ≠ x₂`)
  have hz : localParamR R W (.some x₁ y₁ h₁) ≠ localParamR R W (.some x₂ y₂ h₂) := by
    intro he
    have hPQ : (⟨.some x₁ y₁ h₁, hR1⟩ : {P : W.toAffine.Point // ReducesToZero R W P})
        = ⟨.some x₂ y₂ h₂, hR2⟩ :=
      zParam_injective R W (Subtype.ext (by rw [zParam_coe, zParam_coe]; exact he))
    rw [Subtype.mk_eq_mk, Affine.Point.some.injEq] at hPQ
    exact hxne hPQ.1
  -- Mathlib's affine sum is the secant third point `(addX, addY)`; on the origin-reducing locus the
  -- local parameter takes its `-addX/addY` branch
  rw [Affine.Point.add_of_X_ne hxne] at hred ⊢
  have hpos : 1 < valuation K (maximalIdeal R)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) := hred
  rw [localParam_some, ite_eq_left hpos]
  have key := localParam_add_secant R W ha hz (localParamR_mem R W hR1) (localParamR_mem R W hR2)
    hz₁0 hz₂0 hw hx hd1 hd2 hden
  rw [hx1, hy1, hx2, hy2] at key
  exact key

end WeierstrassCurve
