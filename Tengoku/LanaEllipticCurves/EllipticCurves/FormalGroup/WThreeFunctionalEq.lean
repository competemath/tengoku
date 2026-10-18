/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.FormalGroupLaurent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Weierstrass functional equation for the third `w`-coordinate `W₃ = -y₃⁻¹`

Building on `EllipticCurves.FormalGroup.FormalGroupLaurent`, this file records the third
`w`-coordinate of the group-law point `P₃ = P₁ ⊕ P₂` in the iterated Laurent ring `R⸨z₁⸩⸨z₂⸩`,

`W₃ := -y₃⁻¹ = W.formalWThree`,

and proves that it satisfies the **Weierstrass functional equation with local parameter**
`F_E = W.formalGroupLaurent`:

`W₃ = F_E³ + (a₁F_E + a₂F_E²)·W₃ + (a₃ + a₄F_E)·W₃² + a₆·W₃³`.

This is the exact analogue, with the univariate local parameter `z = X` replaced by the bivariate
parameter `F_E = z(P₃)`, of the defining fixed-point identity `W.formalW = W.wOp W.formalW`
(`EllipticCurves.FormalGroup.Expansion`). It is the load-bearing algebraic input to the
composition/uniqueness route towards the inner pole-freeness of `F_E` (issue #286): the univariate
Weierstrass expansion `formalW` is the *unique* order-`≥ 1` solution of this functional equation, so
`W₃ = formalW ∘ F_E`, exhibiting `F_E` (and hence `x₃, y₃`) as genuine power-series compositions.

The proof is purely algebraic: substituting `F_E = -x₃·y₃⁻¹` and `W₃ = -y₃⁻¹` and clearing the unit
`y₃³` reduces the identity, via `y₃·y₃⁻¹ = 1`, to the point-on-curve identity for `P₃`
(`W.formalXThree_formalYThree_weierstrass`).

## Main definitions and results

* `WeierstrassCurve.formalWThree` : `W₃ = -y₃⁻¹ ∈ R⸨z₁⸩⸨z₂⸩`.
* `WeierstrassCurve.formalWThree_functional_eq` : the Weierstrass functional equation for `W₃` with
  parameter `F_E`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The **third `w`-coordinate** `W₃ = -y₃⁻¹` of the group-law point `P₃ = P₁ ⊕ P₂`, an element of
the iterated Laurent ring `R⸨z₁⸩⸨z₂⸩`. Since `F_E = -x₃·y₃⁻¹` we have `F_E = x₃ · W₃` and
`y₃ = -W₃⁻¹`, so `(F_E, W₃)` are the `(z, w)`-coordinates of `P₃`. -/
noncomputable def formalWThree : (R⸨X⸩)⸨X⸩ := -Ring.inverse W.formalYThree

/-- **The Weierstrass functional equation for `W₃ = -y₃⁻¹` with parameter `F_E`.** With
`F_E = W.formalGroupLaurent` and the double constant embedding `C₂ a = C (C a) : R → R⸨z₁⸩⸨z₂⸩`,

`W₃ = F_E³ + (a₁F_E + a₂F_E²)·W₃ + (a₃ + a₄F_E)·W₃² + a₆·W₃³`,

the exact analogue of `W.formalW = W.wOp W.formalW` with the local parameter `z` replaced by `F_E`.

Proof: `F_E = -x₃·y₃⁻¹` and `W₃ = -y₃⁻¹`, so clearing the unit `y₃³` (using `y₃·y₃⁻¹ = 1`) turns
the claim into the point-on-curve identity `y₃² + a₁x₃y₃ + a₃y₃ = x₃³ + a₂x₃² + a₄x₃ + a₆`
(`formalXThree_formalYThree_weierstrass`). -/
theorem formalWThree_functional_eq :
    W.formalWThree
      = W.formalGroupLaurent ^ 3
        + (HahnSeries.C (HahnSeries.C W.a₁) * W.formalGroupLaurent
            + HahnSeries.C (HahnSeries.C W.a₂) * W.formalGroupLaurent ^ 2) * W.formalWThree
        + (HahnSeries.C (HahnSeries.C W.a₃)
            + HahnSeries.C (HahnSeries.C W.a₄) * W.formalGroupLaurent) * W.formalWThree ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆) * W.formalWThree ^ 3 := by
  -- Abbreviations: `x = x₃`, `y = y₃`, `yi = y₃⁻¹`.
  set x := W.formalXThree with hx
  set y := W.formalYThree with hy
  set yi := Ring.inverse W.formalYThree with hyi
  -- The structural relation `y·yi = 1` (`y₃` is a unit).
  have hyyi : y * yi = 1 := W.formalYThree_mul_inverse
  -- `F_E = -x·yi` (definitional) and `W₃ = -yi`.
  have hF : W.formalGroupLaurent = -x * yi := by rw [formalGroupLaurent, ← hx, ← hyi]
  have hW : W.formalWThree = -yi := by rw [formalWThree, ← hyi]
  -- The point-on-curve identity for `P₃`.
  have hWE := W.formalXThree_formalYThree_weierstrass
  rw [← hx, ← hy] at hWE
  -- `y³` is cancellable: `yi³·y³ = 1`.
  have hcancel : yi ^ 3 * y ^ 3 = 1 := by
    have hc : (yi * y) ^ 3 = 1 := by rw [mul_comm, hyyi]; ring
    linear_combination hc
  have hRcancel : ∀ a b : (R⸨X⸩)⸨X⸩, y ^ 3 * a = y ^ 3 * b → a = b := fun a b h => by
    calc a = yi ^ 3 * y ^ 3 * a := by rw [hcancel, one_mul]
      _ = yi ^ 3 * (y ^ 3 * a) := by ring
      _ = yi ^ 3 * (y ^ 3 * b) := by rw [h]
      _ = yi ^ 3 * y ^ 3 * b := by ring
      _ = b := by rw [hcancel, one_mul]
  -- The identity, cleared by the unit `y³`, reduces to the `P₃` Weierstrass identity.
  have key : y ^ 3 * (-yi)
      = y ^ 3 * ((-x * yi) ^ 3
        + (HahnSeries.C (HahnSeries.C W.a₁) * (-x * yi)
            + HahnSeries.C (HahnSeries.C W.a₂) * (-x * yi) ^ 2) * (-yi)
        + (HahnSeries.C (HahnSeries.C W.a₃)
            + HahnSeries.C (HahnSeries.C W.a₄) * (-x * yi)) * (-yi) ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆) * (-yi) ^ 3) := by
    linear_combination
      (-y ^ 2
        + (x ^ 3 + HahnSeries.C (HahnSeries.C W.a₂) * x ^ 2
            + HahnSeries.C (HahnSeries.C W.a₄) * x + HahnSeries.C (HahnSeries.C W.a₆))
          * (y ^ 2 * yi ^ 2 + y * yi + 1)
        - HahnSeries.C (HahnSeries.C W.a₁) * x * (y ^ 2 * yi + y)
        - HahnSeries.C (HahnSeries.C W.a₃) * (y ^ 2 * yi + y)) * hyyi
      - hWE
  rw [hF, hW]
  exact hRcancel _ _ key

end WeierstrassCurve
