/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.BivariateCoords

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The addition-law data `λ, ν, x₃, y₃` and the point-on-curve identity for `P₃`

Building on the iterated-Laurent-ring infrastructure of
`EllipticCurves.FormalGroup.BivariateCoords` — the two coordinate points `P₁ = (x₁, y₁)`,
`P₂ = (x₂, y₂) ∈ R⸨z₁⸩⸨z₂⸩`, their transported point-on-curve identities, and the crucial unit
`x₂ − x₁` — this file constructs the geometric addition-law data of the Weierstrass formal group
(Silverman, *The Arithmetic of Elliptic Curves*, IV.1, III.2.3):

* the **slope** `λ := (y₂ − y₁)·(x₂ − x₁)⁻¹` of the secant line through `P₁, P₂`;
* the **intercept** `ν := y₁ − λ·x₁`, so the line is `y = λx + ν`;
* the third `x`-coordinate `x₃ := λ² + a₁λ − a₂ − x₁ − x₂` (Vieta for the cubic obtained by
  substituting the line into the Weierstrass equation);
* the third `y`-coordinate `y₃ := −(λx₃ + ν) − a₁x₃ − a₃`, the group-law coordinate `−(P₁ ⊕ P₂)`.

The main result `WeierstrassCurve.formalXThree_formalYThree_weierstrass` proves that `(x₃, y₃)`
satisfies the Weierstrass equation, so `P₃ = (x₃, y₃)` lies on the curve.

## Note on the sign of `y₃`

The naive `−(λx₃ + ν)` (the reflection of the line value) is *not* a point of the curve — the
curve's negation is `(x, y) ↦ (x, −y − a₁x − a₃)`, so the third group-law coordinate carries the
extra `−a₁x₃ − a₃` terms: `y₃ = −(λ + a₁)x₃ − ν − a₃` (Silverman AEC III.2.3). This is the value
used here and it is what makes the point-on-curve identity hold over a general commutative ring.

## Main definitions

* `WeierstrassCurve.formalLambda`, `WeierstrassCurve.formalNu`, `WeierstrassCurve.formalXThree`,
  `WeierstrassCurve.formalYThree` : the addition-law data `λ, ν, x₃, y₃ ∈ R⸨z₁⸩⸨z₂⸩`.

## Main results

* `WeierstrassCurve.formalLambda_mul_biX_sub` : `λ·(x₂ − x₁) = y₂ − y₁` (the defining property of
  the slope, using that `x₂ − x₁` is a unit).
* `WeierstrassCurve.biY₁_eq`, `WeierstrassCurve.biY₂_eq` : `P₁, P₂` lie on the secant `y = λx + ν`.
* `WeierstrassCurve.weierstrass_thirdInt` : the third intersection point `(x₃, λx₃ + ν)` lies on the
  curve (the Vieta/secant computation).
* `WeierstrassCurve.formalXThree_formalYThree_weierstrass` : the point-on-curve identity for
  `P₃ = (x₃, y₃)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, III.2.3.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The addition-law data -/

/-- The slope `λ = (y₂ − y₁)·(x₂ − x₁)⁻¹` of the secant line through `P₁` and `P₂`. -/
noncomputable def formalLambda : (R⸨X⸩)⸨X⸩ :=
  (W.biY₂ - W.biY₁) * Ring.inverse (W.biX₂ - W.biX₁)

/-- The intercept `ν = y₁ − λ·x₁` of the secant line `y = λx + ν` through `P₁` and `P₂`. -/
noncomputable def formalNu : (R⸨X⸩)⸨X⸩ := W.biY₁ - W.formalLambda * W.biX₁

/-- The third `x`-coordinate `x₃ = λ² + a₁λ − a₂ − x₁ − x₂` (Vieta for the secant cubic). -/
noncomputable def formalXThree : (R⸨X⸩)⸨X⸩ :=
  W.formalLambda ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.formalLambda
    - HahnSeries.C (HahnSeries.C W.a₂) - W.biX₁ - W.biX₂

/-- The third `y`-coordinate `y₃ = −(λx₃ + ν) − a₁x₃ − a₃`, the group-law coordinate of
`−(P₁ ⊕ P₂)`. (See the module docstring: the `−a₁x₃ − a₃` terms are the curve's negation and are
required for `(x₃, y₃)` to lie on the curve.) -/
noncomputable def formalYThree : (R⸨X⸩)⸨X⸩ :=
  -(W.formalLambda * W.formalXThree + W.formalNu)
    - HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree - HahnSeries.C (HahnSeries.C W.a₃)

/-! ### The secant line -/

/-- **Defining property of the slope.** `λ·(x₂ − x₁) = y₂ − y₁`, using that `x₂ − x₁` is a unit. -/
theorem formalLambda_mul_biX_sub :
    W.formalLambda * (W.biX₂ - W.biX₁) = W.biY₂ - W.biY₁ := by
  unfold formalLambda
  rw [mul_assoc, Ring.inverse_mul_cancel _ W.isUnit_biX₂_sub_biX₁, mul_one]

/-- `P₁ = (x₁, y₁)` lies on the secant line `y = λx + ν`. -/
theorem biY₁_eq : W.biY₁ = W.formalLambda * W.biX₁ + W.formalNu := by
  unfold formalNu; ring

/-- `P₂ = (x₂, y₂)` lies on the secant line `y = λx + ν`. -/
theorem biY₂_eq : W.biY₂ = W.formalLambda * W.biX₂ + W.formalNu := by
  unfold formalNu
  linear_combination -W.formalLambda_mul_biX_sub

/-! ### The point-on-curve identity for `P₃` -/

/-- **The third intersection point is on the curve.** The point `(x₃, λx₃ + ν)`, where the secant
line `y = λx + ν` through `P₁, P₂` meets the curve a third time, satisfies the Weierstrass equation.

The proof substitutes the line into the Weierstrass equation to get a monic cubic in `x` vanishing
at `x₁, x₂` (that is `biX₁_biY₁_weierstrass`, `biX₂_biY₂_weierstrass` rewritten along the line);
dividing the difference of the two vanishing conditions by the *unit* `x₂ − x₁` yields Vieta's
middle relation `K = 0`, from which `x₃ = λ² + a₁λ − a₂ − x₁ − x₂` is the third root. -/
theorem weierstrass_thirdInt :
    (W.formalLambda * W.formalXThree + W.formalNu) ^ 2
        + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          * (W.formalLambda * W.formalXThree + W.formalNu)
        + HahnSeries.C (HahnSeries.C W.a₃) * (W.formalLambda * W.formalXThree + W.formalNu)
      = W.formalXThree ^ 3 + HahnSeries.C (HahnSeries.C W.a₂) * W.formalXThree ^ 2
        + HahnSeries.C (HahnSeries.C W.a₄) * W.formalXThree
        + HahnSeries.C (HahnSeries.C W.a₆) := by
  -- Substitute the line `yᵢ = λ xᵢ + ν` into the point-on-curve identities for `P₁, P₂`.
  have q1 := W.biX₁_biY₁_weierstrass
  rw [W.biY₁_eq] at q1
  have q2 := W.biX₂_biY₂_weierstrass
  rw [W.biY₂_eq] at q2
  -- The symmetric quotient `K` of the difference of the two cubics.
  set K : (R⸨X⸩)⸨X⸩ :=
    -(W.biX₁ ^ 2 + W.biX₁ * W.biX₂ + W.biX₂ ^ 2)
      + (W.formalLambda ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.formalLambda
          - HahnSeries.C (HahnSeries.C W.a₂)) * (W.biX₁ + W.biX₂)
      + (2 * W.formalLambda * W.formalNu + HahnSeries.C (HahnSeries.C W.a₁) * W.formalNu
          + HahnSeries.C (HahnSeries.C W.a₃) * W.formalLambda
          - HahnSeries.C (HahnSeries.C W.a₄)) with hKdef
  -- Cancelling the unit `x₂ − x₁` gives `K = 0`.
  have hK : K = 0 := by
    obtain ⟨u, hu⟩ := W.isUnit_biX₂_sub_biX₁
    have hmul : (W.biX₂ - W.biX₁) * K = 0 := by rw [hKdef]; linear_combination q2 - q1
    have hu' : (u : (R⸨X⸩)⸨X⸩) * K = 0 := by rw [hu]; exact hmul
    exact (Units.mul_right_eq_zero u).mp hu'
  -- `x₃` is the third root: `G(x₃) = G(x₁) + (x₃ − x₁)·K`.
  unfold formalXThree
  linear_combination q1
    + (W.formalLambda ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.formalLambda
        - HahnSeries.C (HahnSeries.C W.a₂) - W.biX₁ - W.biX₂ - W.biX₁) * hK

/-- **The point-on-curve identity for `P₃ = (x₃, y₃)`.** The third group-law point satisfies the
Weierstrass equation of `W`:
`y₃² + a₁·x₃·y₃ + a₃·y₃ = x₃³ + a₂·x₃² + a₄·x₃ + a₆` in `R⸨z₁⸩⸨z₂⸩`.

This follows from `weierstrass_thirdInt` by the curve's negation symmetry `y ↦ −y − a₁x − a₃`. -/
theorem formalXThree_formalYThree_weierstrass :
    W.formalYThree ^ 2 + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree * W.formalYThree
        + HahnSeries.C (HahnSeries.C W.a₃) * W.formalYThree
      = W.formalXThree ^ 3 + HahnSeries.C (HahnSeries.C W.a₂) * W.formalXThree ^ 2
        + HahnSeries.C (HahnSeries.C W.a₄) * W.formalXThree
        + HahnSeries.C (HahnSeries.C W.a₆) := by
  unfold formalYThree
  linear_combination W.weierstrass_thirdInt

end WeierstrassCurve
