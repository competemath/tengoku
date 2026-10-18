/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The principal divisor of a torsion point on a Weierstrass curve

For a Weierstrass curve `W` over a field `F` and a point `P` of the `n`-torsion subgroup
`E[n] = W.torsion n`, the divisor `n·(P) − n·(O)` is **principal**: there is a rational function
`f_P ∈ F(W)` whose divisor is `n·(P) − n·(O)`. This is the first construction rung of the
divisor-theoretic Weil pairing (project issue #244): the pairing `e_n(S, T)` is built from such
functions `f_S`.

This file realises that statement **affinely**, through the coordinate-ring class group that Mathlib
already attaches to the group law. Recall (from Mathlib's `EllipticCurve/Affine/Point.lean`):

* `WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup F[W])` sends a point `P`
  to the class of the fractional ideal `⟨X − x, Y − y⟩` — i.e. the class of the divisor `(P) − (O)`
  — and `toClass_eq_zero` says it is *injective on classes* (`toClass P = 0 ↔ P = 0`);
* a nonzero point `(x, y)` gives the invertible fractional ideal
  `CoordinateRing.XYIdeal' h : (FractionalIdeal F[W]⁰ F(W))ˣ`, with
  `toClass (.some x y h) = ClassGroup.mk F(W) (XYIdeal' h)`.

So "`(XYIdeal' h)^n` is principal" is precisely "`n·(P) − n·(O)` is a principal divisor", and it
follows from `n • P = 0` by pushing through the homomorphism `toClass` and the
class-group/principal-ideal dictionary `ClassGroup.mk_eq_one_iff`.

## Design — independent of the normality gap and of the Ward recurrence

`XYIdeal'` and `toClass` are built by Mathlib from the *pointwise* nonsingularity of the group law
and need only `[IsDomain F[W]]` (automatic over a field) — **not** `[IsDedekindDomain F[W]]`. Hence
this rung is independent of the integral-closedness/normality discharge for `F[W]` — which is no
longer outstanding for an elliptic curve
(`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`, a global instance over an arbitrary
field), so the independence now buys generality in `W` rather than freedom from an open problem.
It is likewise independent of the elliptic-net / Ward recurrence.

⚠️ This paragraph used to close with "only *non-degeneracy* of the finished pairing needs the
torsion count `#E[n] = n²`", which is **wrong** and is the claim `#769` retired at eighteen other
sites; this one was missed because it names neither `WeilPairing` nor `#242`. At `n = 2` the count
enters non-degeneracy only inside `fixedFieldTwo_eq_mulByTwoFieldRange` (`MulByTwoGalois`, `#759`),
through `card_torsion_two` — the roots of the `2`-division cubic, which does not go through Ward —
and at `n = 3` likewise through `card_torsion_three`. Ward gates `#E[n] = n²` at **general** `n`
only (`#242`/`#1490`; ⚠️ this used to cite `#251`, which is closed). See
`EllipticCurves.FunctionField.WeilPairing`'s scope section for the canonical account of what
non-degeneracy consumes; the independence claimed above is unaffected either way.

## Main statements

* `WeierstrassCurve.Affine.toClass_nsmul_eq_zero_of_torsion` : `P ∈ E[n]` gives `n • toClass P = 0`
  — the ideal class of `(P) − (O)` is `n`-torsion in the class group.
* `WeierstrassCurve.Affine.XYIdeal'_pow_isPrincipal_of_torsion` : if `.some x y h ∈ E[n]` then the
  fractional ideal `(XYIdeal' h)^n` is principal — the existence of the function `f_P` with
  `div f_P = n·(P) − n·(O)`.
* `WeierstrassCurve.Affine.exists_generator_XYIdeal'_pow_of_torsion` : the explicit generator — a
  **nonzero** rational function `f_P ∈ F(W)` with `(XYIdeal' h)^n = spanSingleton f_P`. This is the
  concrete `f_P` the Weil-pairing construction consumes.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (divisors; a degree-`0` divisor is principal
iff it sums to `O`, Abel's theorem — here realised as the affine class group of `F[W]`) and III.8
(the Weil pairing).
-/

open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- The ideal class of the divisor `(P) − (O)` attached to a point `P` is `n`-torsion in the class
group of `F[W]` whenever `P` lies in the `n`-torsion `E[n]`: pushing `n • P = 0` through the group
homomorphism `toClass : W.Point →+ Additive (ClassGroup F[W])`. -/
theorem toClass_nsmul_eq_zero_of_torsion {n : ℕ} {P : W.Point} (hP : P ∈ W.torsion n) :
    n • Point.toClass P = 0 := by
  rw [← map_nsmul, mem_torsion_iff.mp hP, map_zero]

/-- **The principal-divisor rung of the Weil pairing (issue #244).** For a nonzero point `(x, y)` of
the `n`-torsion `E[n]`, the `n`-th power of the point ideal `⟨X − x, Y − y⟩` is a **principal**
fractional ideal of `F[W]`. Equivalently, the degree-`0` divisor `n·(P) − n·(O)` is principal: there
is a rational function `f_P ∈ F(W)` with `div f_P = n·(P) − n·(O)`, the function the
divisor-theoretic Weil pairing consumes.

This needs only that `F` is a field (so `F[W]` is a domain); it does **not** use Dedekindness /
normality of `F[W]`, nor the elliptic-net (Ward) recurrence. -/
theorem XYIdeal'_pow_isPrincipal_of_torsion {x y : F} (h : W.Nonsingular x y) {n : ℕ}
    (hP : Point.some x y h ∈ W.torsion n) :
    (↑(CoordinateRing.XYIdeal' (W := W) h ^ n) :
      Submodule W.CoordinateRing W.FunctionField).IsPrincipal := by
  have hz : ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h) ^ n = 1 := by
    have h0 := toClass_nsmul_eq_zero_of_torsion hP
    rwa [Point.toClass_some] at h0
  rw [← map_pow] at hz
  exact ClassGroup.mk_eq_one_iff.mp hz

/-- **The explicit principal generator `f_P`.** For a nonzero point `(x, y)` of the `n`-torsion
`E[n]`, there is a **nonzero** rational function `f_P ∈ F(W)` with
`(XYIdeal' h)^n = spanSingleton f_P` as fractional ideals. This is the concrete rational function
whose divisor is `n·(P) − n·(O)` — the input the divisor-theoretic Weil pairing consumes (a
generator of the principal ideal produced by `XYIdeal'_pow_isPrincipal_of_torsion`).

Like that lemma this needs only `[Field F]`; it uses neither Dedekindness/normality of `F[W]` nor
the elliptic-net (Ward) recurrence. -/
theorem exists_generator_XYIdeal'_pow_of_torsion {x y : F} (h : W.Nonsingular x y) {n : ℕ}
    (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      (↑(CoordinateRing.XYIdeal' (W := W) h ^ n) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰ f := by
  haveI := XYIdeal'_pow_isPrincipal_of_torsion h hP
  have hIne : (↑(CoordinateRing.XYIdeal' (W := W) h ^ n) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ≠ 0 :=
    (CoordinateRing.XYIdeal' (W := W) h ^ n).isUnit.ne_zero
  refine ⟨Submodule.IsPrincipal.generator
      ((↑(CoordinateRing.XYIdeal' (W := W) h ^ n) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :
        Submodule W.CoordinateRing W.FunctionField), ?_,
    FractionalIdeal.eq_spanSingleton_of_principal _⟩
  intro hg0
  exact hIne <| by
    rw [FractionalIdeal.eq_spanSingleton_of_principal
      (↑(CoordinateRing.XYIdeal' (W := W) h ^ n) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField), hg0,
      FractionalIdeal.spanSingleton_zero]

end WeierstrassCurve.Affine
