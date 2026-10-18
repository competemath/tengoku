/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Evaluation of the division polynomials at an affine point

Mathlib develops the division polynomials of a Weierstrass curve `W` purely *univariately* and
*bivariately*, as polynomials `W.ψ n, W.Ψ n, W.φ n ∈ R[X][Y]` and `W.ΨSq n, W.Φ n ∈ R[X]`, together
with the coordinate-ring congruences

* `WeierstrassCurve.Affine.CoordinateRing.mk_ψ    : mk W (W.ψ n) = mk W (W.Ψ n)`
* `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq : mk W (W.Ψ n) ^ 2 = mk W (C (W.ΨSq n))`
* `WeierstrassCurve.Affine.CoordinateRing.mk_φ    : mk W (W.φ n) = mk W (C (W.Φ n))`

living in the affine coordinate ring `R[W] = AdjoinRoot W.polynomial`. What is missing — and what
this file supplies — is the *evaluation of these polynomials at an actual affine point* `(x, y)` of
`W`,
turning the coordinate-ring congruences into honest polynomial identities in `R`.

The key observation is that the evaluation-at-`(x, y)` ring homomorphism out of the coordinate ring
already exists in Mathlib: for a point `(x, y)` lying on `W`, i.e. with `h : W.Equation x y` (which
unfolds to `W.polynomial.evalEval x y = 0`), `AdjoinRoot.evalEval h : AdjoinRoot W.polynomial →+* R`
sends `mk W g` to `g.evalEval x y`. Since `R[W]` is by definition `AdjoinRoot W.polynomial`, this is
exactly the map we need. For a nonsingular point `P = .some x y hP : W.Point`, the required
hypothesis is `hP.1 : W.Equation x y`.

Applying this ring homomorphism to the three congruences above transports them to the identities

* `ψ_evalEval    : (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y`
* `ψ_sq_evalEval : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x`
* `φ_evalEval    : (W.φ n).evalEval x y = (W.Φ n).eval x`

In particular the *square* of `ψₙ` and the value of `φₙ` at a point of `W` depend only on the
`x`-coordinate, through the univariate polynomials `ΨSqₙ` and `Φₙ`. This is the foundational input
to the elliptic-divisibility-sequence recurrence and to the multiplication-by-`n` coordinate formula
`x(n • P) = Φₙ(x) / ΨSqₙ(x)`, developed separately.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.evalEvalHom`: the evaluation-at-`(x, y)` ring homomorphism
  `R[W] → R` attached to a point `(x, y)` on `W`.

## Main statements

* `WeierstrassCurve.Affine.ψ_evalEval`, `WeierstrassCurve.Affine.ψ_sq_evalEval`,
  `WeierstrassCurve.Affine.Ψ_sq_evalEval`, `WeierstrassCurve.Affine.φ_evalEval`: the transported
  identities described above.
* `WeierstrassCurve.Affine.ψ_zero_evalEval`, `WeierstrassCurve.Affine.ψ_one_evalEval`,
  `WeierstrassCurve.Affine.ψ_two_evalEval`: the low-index base evaluations.
* `WeierstrassCurve.C_b_relation`: Mathlib's `b`-relation `4b₈ = b₂b₆ − b₄²` pushed through `C`
  into `R[X]`.

## Why `C_b_relation` is here rather than beside a consumer

It is not about evaluation at a point and has nothing to do with the rest of this file; it is here
because this file is a **leaf** — it imports no `EllipticCurves` module, only the two Mathlib files
that already supply everything the lemma needs — and it is in the import closure of most of the
library.  The relation was written twice independently, once `private` over a field in
`EllipticCurves.Torsion.TriplingSurjective` and once public over a `CommRing` in
`EllipticCurves.Torsion.OmegaNumerator`, and those two modules have **only this one** in the
intersection of their closures, so a single shared copy has to live here or the dependency between
them inverts (`#1418`).

## ⚠️ Two `@[simp]` attributes were removed here, and the lemmas kept (`#1278`)

`ψ_zero_evalEval` and `ψ_one_evalEval` carried `@[simp]`, and the default simp set **already proves
both** — through Mathlib's `ψ_zero` / `ψ_one` with `Polynomial.evalEval_zero` / `evalEval_one`.
Measured with Mathlib's `simpNF` environment linter, which had never been run on this tree. Both
lemmas are unchanged; only the attribute went.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W : Affine R} {x y : R}

namespace CoordinateRing

/-- The evaluation-at-`(x, y)` ring homomorphism `R[W] → R` on the affine coordinate ring, attached
to a point `(x, y)` lying on `W` (`h : W.Equation x y`). It is Mathlib's `AdjoinRoot.evalEval`
transported along the definitional equality `R[W] = AdjoinRoot W.polynomial`, and sends the class
`mk W g` of a bivariate polynomial `g` to its evaluation `g.evalEval x y`. -/
noncomputable def evalEvalHom (h : W.Equation x y) : W.CoordinateRing →+* R :=
  AdjoinRoot.evalEval h

@[simp]
lemma evalEvalHom_mk (h : W.Equation x y) (g : R[X][Y]) :
    evalEvalHom h (mk W g) = g.evalEval x y :=
  AdjoinRoot.evalEval_mk h g

end CoordinateRing

section Eval

/-- The bivariate `n`-division polynomial `ψₙ` and the polynomial `Ψₙ` agree when evaluated at a
point `(x, y)` of `W`, since they define the same class in the coordinate ring. -/
lemma ψ_evalEval (h : W.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y := by
  have H := congrArg (CoordinateRing.evalEvalHom h) (CoordinateRing.mk_ψ W n)
  rwa [CoordinateRing.evalEvalHom_mk, CoordinateRing.evalEvalHom_mk] at H

/-- The square of the `n`-division polynomial `ψₙ` at a point `(x, y)` of `W` depends only on the
`x`-coordinate: it equals the univariate polynomial `ΨSqₙ` evaluated at `x`. -/
lemma ψ_sq_evalEval (h : W.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have H := congrArg (CoordinateRing.evalEvalHom h) (CoordinateRing.mk_Ψ_sq W n)
  rw [map_pow, CoordinateRing.evalEvalHom_mk, CoordinateRing.evalEvalHom_mk, evalEval_C] at H
  rw [ψ_evalEval h, H]

/-- The square of `Ψₙ` at a point `(x, y)` of `W` equals the univariate polynomial `ΨSqₙ` evaluated
at `x`. -/
lemma Ψ_sq_evalEval (h : W.Equation x y) (n : ℤ) :
    (W.Ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  rw [← ψ_evalEval h, ψ_sq_evalEval h]

/-- The bivariate polynomial `φₙ` at a point `(x, y)` of `W` depends only on the `x`-coordinate: it
equals the univariate polynomial `Φₙ` evaluated at `x`. -/
lemma φ_evalEval (h : W.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by
  have H := congrArg (CoordinateRing.evalEvalHom h) (CoordinateRing.mk_φ W n)
  rwa [CoordinateRing.evalEvalHom_mk, CoordinateRing.evalEvalHom_mk, evalEval_C] at H

end Eval

section BaseCases

/-- The `0`-division polynomial vanishes at every point: `ψ₀(x, y) = 0`. -/
lemma ψ_zero_evalEval : (W.ψ 0).evalEval x y = 0 := by
  rw [ψ_zero, evalEval_zero]

/-- The `1`-division polynomial is the constant `1`: `ψ₁(x, y) = 1`. -/
lemma ψ_one_evalEval : (W.ψ 1).evalEval x y = 1 := by
  rw [ψ_one, evalEval_one]

/-- The `2`-division polynomial at a point: `ψ₂(x, y) = 2y + a₁x + a₃`. -/
lemma ψ_two_evalEval : (W.ψ 2).evalEval x y = 2 * y + W.a₁ * x + W.a₃ := by
  rw [ψ_two]
  exact evalEval_polynomialY x y

end BaseCases

end WeierstrassCurve.Affine

namespace WeierstrassCurve

/-! ### Mathlib's `b`-relation, in `R[X]` -/

/-- **`4b₈ = b₂b₆ − b₄²`, pushed through `C` into `R[X]`.**  This is Mathlib's
`WeierstrassCurve.b_relation` in the ring where the division-polynomial identities live, and the
form `linear_combination` needs when the goal is an identity of *polynomials* rather than of
scalars.

It is the one input that `ring1` cannot supply for itself.  With `b₂, b₄, b₆, b₈` taken as
independent atoms the identities that consume it are **false** —
`WeierstrassCurve.Affine.preΨ₄_eq` (`EllipticCurves.Torsion.TriplingSurjective`), whose `X²`
coefficient is `10b₈` on one side and `6b₈ + b₂b₆ − b₄²` on the other, and
`WeierstrassCurve.hasΦDoubling_two` (`EllipticCurves.Torsion.OmegaNumerator`), whose two sides
differ by an explicit `33`-term cofactor times `4b₈ − b₂b₆ + b₄²`.  They become true exactly
modulo this relation, which is why both close by `linear_combination … * W.C_b_relation` and
neither closes by `ring`.

⚠️ Both consumers named above are **forward references**: they import this file and neither is in
its import closure, so nothing here depends on them.  The lemma needs only
`WeierstrassCurve.b_relation`, which lives in Mathlib's `Weierstrass.lean` — already in this file's
closure — so it costs this leaf no import. -/
lemma C_b_relation {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (4 : R[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
  simpa [map_ofNat] using congrArg C W.b_relation

end WeierstrassCurve
