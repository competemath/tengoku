/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.RingTheory.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The universal Weierstrass curve and the specialisation homomorphism

A statement about *every* Weierstrass curve over *every* commutative ring is a statement about
**one** curve over **one** ring, provided the statement is stable under base change.  The curve is
the **universal** one,

`univ : WeierstrassCurve (MvPolynomial (Fin 5) ℤ)`, with `aᵢ = MvPolynomial.X i`,

and the base change is along the **specialisation homomorphism** `W.specialize : S →+* R` sending
`X i` to the corresponding coefficient of `W`, for which `univ.map W.specialize = W`.

`S = MvPolynomial (Fin 5) ℤ` is a characteristic-`0` integral domain, which is what makes the
reduction worth performing: over `S` (or over `S ⊗ ℚ`, or over its fraction field) arguments are
available that are not available over a general `CommRing` — no torsion in the coefficients, no
`2 = 0`, and a fraction field to work in.

## Main definitions

* `WeierstrassCurve.univ` : the universal Weierstrass curve.
* `WeierstrassCurve.specialize` : the specialisation homomorphism `S →+* R` attached to a curve.

## Main results

* `WeierstrassCurve.univ_map_specialize` : `univ.map W.specialize = W`.

## Implementation notes

This file imports **only** Mathlib, deliberately.  Both of its consumers — the formal-group
identification in `EllipticCurves.FormalGroup.UniversalIdentification` /
`EllipticCurves.FormalGroup.GenuineLawTransfer`, and the division-polynomial reduction in
`EllipticCurves.Torsion.OmegaUniversal` — sit in unrelated corners of the library, and the
universal curve depends on nothing from either.  The three declarations below were originally
written inside the formal-group files and are unchanged by the move.
-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The **universal Weierstrass curve** over `S := MvPolynomial (Fin 5) ℤ`, with `aᵢ = X i`.
`S` is a characteristic-`0` integral domain, so its base change carries the unconditional
identification. -/
noncomputable def univ : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) where
  a₁ := MvPolynomial.X 0
  a₂ := MvPolynomial.X 1
  a₃ := MvPolynomial.X 2
  a₄ := MvPolynomial.X 3
  a₆ := MvPolynomial.X 4

/-- The **specialisation homomorphism** `S = MvPolynomial (Fin 5) ℤ →+* R` sending the universal
generators `X 0, …, X 4` to the coefficients `a₁, a₂, a₃, a₄, a₆` of `W`.  Base changing the
universal curve along it recovers `W` (`univ_map_specialize`). -/
noncomputable def specialize (W : WeierstrassCurve R) : MvPolynomial (Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/-- Base changing the universal curve along `W.specialize` recovers `W`:
`univ.map W.specialize = W`. -/
theorem univ_map_specialize (W : WeierstrassCurve R) : univ.map W.specialize = W := by
  ext <;>
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, univ, specialize,
      MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

end WeierstrassCurve
