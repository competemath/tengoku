/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.AdditionLawUnit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Weierstrass formal group law `F_E := -x₃·y₃⁻¹` in `R⸨z₁⸩⸨z₂⸩`

Building on `EllipticCurves.FormalGroup.AdditionLawUnit`, which proves that the third
`y`-coordinate `y₃ = W.formalYThree` of the Weierstrass addition law is a **unit** of the iterated
Laurent ring `R⸨z₁⸩⸨z₂⸩`, this file defines the Weierstrass formal group law as the Laurent element

`F_E := -x₃ · y₃⁻¹`

(the local parameter `z₃ = -x₃/y₃` of `P₃ = P₁ ⊕ P₂`, Silverman AEC IV.1, Theorem 1.1) and records
its leading behaviour: `F_E` has `z₂`-order `0`, i.e. it is pole-free in `z₂` (the first step
towards recognising `F_E = z₁ + z₂ - a₁z₁z₂ - ⋯` as a genuine power series, which is issue #265).

## Main definitions and results

* `WeierstrassCurve.formalGroupLaurent` : the Laurent element `F_E = -x₃·y₃⁻¹ ∈ R⸨z₁⸩⸨z₂⸩`.
* `WeierstrassCurve.formalGroupLaurent_mul_formalYThree` : `F_E · y₃ = -x₃`, the defining identity.
* `WeierstrassCurve.orderTop_formalGroupLaurent` : `F_E.orderTop = 0` (pole-free in `z₂`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The **Weierstrass formal group law** as a Laurent element: `F_E = -x₃ · y₃⁻¹`, the local
parameter `z₃ = -x₃/y₃` of `P₃ = P₁ ⊕ P₂`. It is well-defined because `y₃ = W.formalYThree` is a
unit (`WeierstrassCurve.isUnit_formalYThree`). (Silverman AEC IV.1.) -/
noncomputable def formalGroupLaurent : (R⸨X⸩)⸨X⸩ :=
  (-W.formalXThree) * Ring.inverse W.formalYThree

/-- `y₃ · y₃⁻¹ = 1` (the inverse used in `F_E` is a genuine inverse, since `y₃` is a unit). -/
theorem formalYThree_mul_inverse : W.formalYThree * Ring.inverse W.formalYThree = 1 :=
  Ring.mul_inverse_cancel _ W.isUnit_formalYThree

/-- **Defining identity of the formal group law.** `F_E · y₃ = -x₃`. -/
theorem formalGroupLaurent_mul_formalYThree :
    W.formalGroupLaurent * W.formalYThree = -W.formalXThree := by
  rw [formalGroupLaurent, mul_assoc, Ring.inverse_mul_cancel _ W.isUnit_formalYThree, mul_one]

/-- **`F_E` is pole-free in `z₂`.** The Weierstrass formal group law has `z₂`-order `0`: its poles
in `x₃` and `y₃` have equal `z₂`-order `0`, so the quotient has order `0`. (This is the first step
towards `F_E = z₁ + z₂ - ⋯`; that `F_E` is a power series in both gradings is issue #265.) -/
theorem orderTop_formalGroupLaurent [Nontrivial R] :
    W.formalGroupLaurent.orderTop = (0 : WithTop ℤ) := by
  have hxne : W.formalXThree ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (by rw [W.orderTop_formalXThree]; exact WithTop.zero_ne_top)
  have hFne : W.formalGroupLaurent ≠ 0 := by
    intro h
    apply hxne
    have hx : -W.formalXThree = 0 := by
      rw [← W.formalGroupLaurent_mul_formalYThree, h, zero_mul]
    exact neg_eq_zero.mp hx
  have hlc : W.formalGroupLaurent.leadingCoeff * W.formalYThree.leadingCoeff ≠ 0 := by
    rw [W.leadingCoeff_formalYThree, ne_eq, W.isUnit_formalY.mul_left_eq_zero]
    exact HahnSeries.leadingCoeff_ne_zero.mpr hFne
  have hmul := HahnSeries.orderTop_mul_of_ne_zero hlc
  rw [W.formalGroupLaurent_mul_formalYThree, HahnSeries.orderTop_neg, W.orderTop_formalXThree,
    W.orderTop_formalYThree, add_zero] at hmul
  exact hmul.symm

end WeierstrassCurve
