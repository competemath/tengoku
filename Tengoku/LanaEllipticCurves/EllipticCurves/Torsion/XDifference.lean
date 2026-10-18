/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.DivisionPolynomialEval
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.WardHalving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `x`-difference identity for the division polynomials

Ward's `r = 1` relation for the division polynomials `W.ψ` — `WeierstrassCurve.Affine.ψ_rel_one`
of `EllipticCurves.Torsion.WardHalving` — is

```
ψ_{p+q}·ψ_{p−q}·ψ₁² − ψ_{p+1}·ψ_{p−1}·ψ_q² + ψ_{q+1}·ψ_{q−1}·ψ_p² = 0.
```

Since `ψ₁ = 1` and `φₙ = X·ψₙ² − ψ_{n+1}·ψ_{n−1}` *by definition*, the two `ψ_{k±1}` products are
exactly `X·ψ_k² − φ_k`, the `X·ψ_p²·ψ_q²` terms cancel, and the relation becomes

```
ψ_{p+q}·ψ_{p−q} = φ_q·ψ_p² − φ_p·ψ_q².
```

That is `WeierstrassCurve.Affine.ψ_add_mul_ψ_sub`, over an arbitrary `CommRing` and at arbitrary
integer indices, with no hypotheses at all.  Dividing by `ψ_p²·ψ_q²` it reads

```
φ_q/ψ_q² − φ_p/ψ_p² = ψ_{p+q}·ψ_{p−q}/(ψ_p²·ψ_q²),
```

which is the classical **`x`-difference identity** `x(qP) − x(pP) = ψ_{p+q}ψ_{p−q}/(ψ_p²ψ_q²)`
([Silverman, AEC][silverman2009], Exercise 3.7) — *once* one knows `x(nP) = Φₙ(x)/ΨSqₙ(x)`.

⚠️ **This file does not prove that, and does not claim it.**  The multiplication-by-`n` coordinate
formula is issue `#251`, packaged as `WeierstrassCurve.Affine.HasXCoordFormula` in
`EllipticCurves.Torsion.NsmulSurjective`.  ⚠️ **It holds at every index** over a field of
characteristic `≠ 2` — `hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`, which
imports this file — so nothing here can use it, and neither `hasXCoordFormula_two` nor
`hasXCoordFormula_three` is reachable from here either: `…DoublingSurjective` is not in this file's
`6`-module closure.  Everything below is a statement
about the *polynomials* `Φ`, `ΨSq`, `ψ` and their values, never about `n • P` — with the single
exception of `EllipticCurves.Torsion.XDifferencePoint`, which instantiates the point-level reading
at `(p, q) = (3, 2)` where both instances exist.  ⚠️ The order matters there: the identity is
antisymmetric under `p ↔ q`, so `(3, 2)` and `(2, 3)` differ by a sign.  ⚠️ Read `Φₙ/ΨSqₙ` below as
"the division-polynomial `x`-coordinate at `n`", not as `x(n • P)`.

⚠️ Neither `EllipticCurves.Torsion.NsmulSurjective` nor `EllipticCurves.Torsion.XDifferencePoint`
is in this file's import closure, so `HasXCoordFormula`, `hasXCoordFormula_two` and
`hasXCoordFormula_three` are named here and used nowhere below.  `XDifferencePoint` imports this
file, so it is a forward reference; `NsmulSurjective` neither imports this file nor is imported by
it, so it is import-incomparable with it.  ⚠️ The two are not disjoint downstream, though:
**51** of the **423** modules under `EllipticCurves/` have both in their import closure at
`3f61ad7` — the root aggregator `EllipticCurves.lean` imports all 423 directly and so is in every
count of this shape; it is excluded here, as `README.md` `### Import-closure membership` rules.
Exactly **two** of the 51 are minimal — `EllipticCurves.Torsion.XDifferencePoint`, which imports
this file directly and reaches `NsmulSurjective` through
`EllipticCurves.Torsion.TriplingSurjective`, and `EllipticCurves.Torsion.NsmulLadder`, which also
imports this file directly and reaches it through `EllipticCurves.Torsion.DoublingCoords`.  The two
witnesses are import-incomparable with each other, so neither is the join.  ⚠️ **This clause used
to read *"`XDifferencePoint` is the unique module in the tree whose closure contains both"***, and
that is a universal over the tree, not a fact about this file's diff: it is false of the **49**
modules downstream of either witness and false of `NsmulLadder`, which existed when it was written.
A *"unique module"* claim about the import graph is a count, and `README.md`
`### Import-closure membership` asks it to carry one — and to say where the population stops.

## Why this is a Ward corollary and could not be written before

The derivation of `WeierstrassCurve.Affine.ψ_add_mul_ψ_sub` is three lines of `ring` on top of the
`r = 1` relation, and the `r = 1` relation for `normEDS` was, until `WeierstrassCurve.wardGapCore`
was proved in `EllipticCurves.Torsion.WardHalving`, the open half of Mathlib's
`IsEllipticDvdSequence` `TODO`.
The two-term recurrences Mathlib does prove (`normEDS_even`, `normEDS_odd`) do **not** give it,
and they are not the same size: `ψ_odd` relates `ψ_{2m+1}` to the **four** consecutive
`ψ_{m−1}, …, ψ_{m+2}`, while `ψ_even` relates `ψ_{2m}·ψ₂` — with a `ψ₂` on the *left*, which
`ψ_two_mul_mul_ψ_two` below also carries — to the **five** consecutive `ψ_{m−2}, …, ψ_{m+2}`.
Neither carries a `φ`.

⚠️ Issue `#251`'s own split comment named this identity as the thing that, once available, makes
the coordinate formula and Ward's addition formula *each other's content*.  It is now available.
That did not by itself discharge `#251` — the identity is an equation between polynomials, and the
input it does not supply is the geometric one, that `Φₙ/ΨSqₙ` is the `x`-coordinate of a point.
⚠️ **That input is proved too, at every index with `(2 : F) ≠ 0`** —
`hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`, which imports this file) —
so `#251` is closed and nothing here names an open gate.

## Main statements

* `IsEllipticNet.mul_sub_eq_of_rel_one` : the identity for an abstract sequence, from a **single**
  instance of the `r = 1` relator and `W 1 = 1`.  No curve, no elliptic-sequence hypothesis.
* `WeierstrassCurve.Affine.ψ_add_mul_ψ_sub` : `ψ_{p+q}·ψ_{p−q} = φ_q·ψ_p² − φ_p·ψ_q²` in `R[X][Y]`,
  over an arbitrary commutative ring, at arbitrary `p q : ℤ`.
* `WeierstrassCurve.Affine.ψ_two_mul_add_one`, `WeierstrassCurve.Affine.ψ_two_mul_mul_ψ_two` : the
  index-doubling specialisations `(p, q) = (n+1, n)` and `(n+1, n−1)`, which express `ψ_{2n+1}` and
  `ψ_{2n}·ψ₂` through `φ` rather than through Mathlib's four (`ψ_odd`) and five (`ψ_even`)
  consecutive `ψ`.
* `WeierstrassCurve.Affine.ψ_add_mul_ψ_sub_evalEval` : the same at a point of `W`, where the
  right-hand side becomes **univariate** — `Φ_q(x)·ΨSq_p(x) − Φ_p(x)·ΨSq_q(x)`.
* `WeierstrassCurve.Affine.Φ_div_ΨSq_sub_Φ_div_ΨSq` : the quotient form over a field.
* `WeierstrassCurve.Affine.Φ_div_ΨSq_eq_iff` : two division-polynomial `x`-coordinates agree iff
  `ψ_{p+q}·ψ_{p−q}` vanishes at the point.

## References

* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7.
-/

open Polynomial Polynomial.Bivariate

namespace IsEllipticNet

variable {R : Type*} [CommRing R]

/-- **The `x`-difference identity for an abstract normalised sequence.**  A single instance of the
`r = 1` elliptic relator, together with `W 1 = 1`, gives

```
W_{p+q}·W_{p−q} = W_{p+1}·W_{p−1}·W_q² − W_{q+1}·W_{q−1}·W_p².
```

⚠️ The hypothesis is the relator at the **one** pair `(p, q)`, not `IsEllipticSequence W`: nothing
here is an induction, and no other index is touched.  For the division polynomials the two products
`W_{k+1}·W_{k−1}` are `X·W_k² − φ_k`, which is what turns this into a statement about `φ`. -/
theorem mul_sub_eq_of_rel_one {W : ℤ → R} (h1 : W 1 = 1) {p q : ℤ} (h : rel W p q 1 0 = 0) :
    W (p + q) * W (p - q)
      = W (p + 1) * W (p - 1) * W q ^ 2 - W (q + 1) * W (q - 1) * W p ^ 2 := by
  simp only [rel, add_zero, h1, mul_one] at h
  linear_combination h

/-- The `x`-difference identity for an elliptic sequence, at every pair of indices. -/
theorem mul_sub_eq_of_isEllipticSequence {W : ℤ → R} (h1 : W 1 = 1) (h : IsEllipticSequence W)
    (p q : ℤ) :
    W (p + q) * W (p - q)
      = W (p + 1) * W (p - 1) * W q ^ 2 - W (q + 1) * W (q - 1) * W p ^ 2 :=
  mul_sub_eq_of_rel_one h1 (h p q 1)

end IsEllipticNet

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-! ## The identity in `R[X][Y]` -/

/-- **The `x`-difference identity**, in `R[X][Y]`:

```
ψ_{p+q}·ψ_{p−q} = φ_q·ψ_p² − φ_p·ψ_q².
```

Over an arbitrary commutative ring, at arbitrary integer indices, with no hypotheses.  It is Ward's
`r = 1` relation `WeierstrassCurve.Affine.ψ_rel_one` with `ψ₁ = 1` substituted and `φ` folded in;
the `X·ψ_p²·ψ_q²` terms of the two `φ`s cancel.

⚠️ Divided through by `ψ_p²·ψ_q²` this is the classical `x(qP) − x(pP) = ψ_{p+q}ψ_{p−q}/(ψ_p²ψ_q²)`,
but only *given* the coordinate formula `x(nP) = φₙ/ψₙ²`, which is issue `#251`.  ⚠️ It **is**
proved at general `n` — `hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder` —
which imports this file, so it is not reachable here.  Nothing below is about `n • P`. -/
theorem ψ_add_mul_ψ_sub (p q : ℤ) :
    W.ψ (p + q) * W.ψ (p - q) = W.φ q * W.ψ p ^ 2 - W.φ p * W.ψ q ^ 2 := by
  rw [IsEllipticNet.mul_sub_eq_of_rel_one (W := W.ψ) (by simp) (W.ψ_rel_one p q),
    WeierstrassCurve.φ, WeierstrassCurve.φ]
  ring

/-- `ψ_{2n+1} = φ_n·ψ_{n+1}² − φ_{n+1}·ψ_n²`: the odd index-doubling formula in terms of `φ`.

⚠️ Not Mathlib's `normEDS_odd`, which reads `ψ_{2m+1} = ψ_{m+2}·ψ_m³ − ψ_{m−1}·ψ_{m+1}³` and
involves four consecutive `ψ` and no `φ`.  This form is the one a coprimality or torsion argument
wants, because it exhibits `ψ_{2n+1}` in the ideal generated by `ψ_n` and `ψ_{n+1}`. -/
theorem ψ_two_mul_add_one (n : ℤ) :
    W.ψ (2 * n + 1) = W.φ n * W.ψ (n + 1) ^ 2 - W.φ (n + 1) * W.ψ n ^ 2 := by
  have h := W.ψ_add_mul_ψ_sub (n + 1) n
  rw [show n + 1 + n = 2 * n + 1 by ring, show n + 1 - n = 1 by ring, ψ_one, mul_one] at h
  exact h

/-- `ψ_{2n}·ψ₂ = φ_{n−1}·ψ_{n+1}² − φ_{n+1}·ψ_{n−1}²`: the even index-doubling formula in terms of
`φ`.  The `ψ₂` on the left is the same spurious factor that `ψ_mul_Ω` (`ψ₂ₙ·ψ₂ = ψₙ·Ωₙ`) carries,
and for the same reason: `ψ` at an even index is divisible by `ψ₂`, and Mathlib's `normEDS_even`
pins `ψ₂ₙ` only up to that factor.

⚠️ `ψ_mul_Ω` is **not** Mathlib's — it is `EllipticCurves.Torsion.OmegaDivisionPolynomial`'s, and
that module neither imports this file nor is imported by it, so the name is cited here and used
nowhere below.  ⚠️ Nor is the `ψ₂` irremovable in principle: that same module's `preΨ_two_mul`
(`preΨ₂ₙ = preΨₙ·preΩₙ`) is the univariate form with nothing left to cancel, over an arbitrary
`CommRing`.  What is true is narrower — in **this** bivariate statement about `ψ` there is no
`ψ₂`-free form over a general ring, because cancelling it needs `ψ₂` to be a non-zero-divisor. -/
theorem ψ_two_mul_mul_ψ_two (n : ℤ) :
    W.ψ (2 * n) * W.ψ 2 = W.φ (n - 1) * W.ψ (n + 1) ^ 2 - W.φ (n + 1) * W.ψ (n - 1) ^ 2 := by
  have h := W.ψ_add_mul_ψ_sub (n + 1) (n - 1)
  rwa [show n + 1 + (n - 1) = 2 * n by ring, show n + 1 - (n - 1) = 2 by ring] at h

/-! ## The identity at a point, where the right-hand side is univariate -/

variable {W} {x y : R}

/-- **The `x`-difference identity at a point `(x, y)` of `W`.**  The right-hand side involves only
the *univariate* polynomials `Φ` and `ΨSq`, evaluated at the `x`-coordinate:

```
ψ_{p+q}(x, y)·ψ_{p−q}(x, y) = Φ_q(x)·ΨSq_p(x) − Φ_p(x)·ΨSq_q(x).
```

The two factors on the left are genuinely bivariate — `ψ_k` at an even `k` is divisible by
`ψ₂ = 2Y + a₁X + a₃` — but their *product* is not, because `p + q` and `p − q` always have the
**same** parity, so the product is invariant under the hyperelliptic involution and hence lies in
`R[X]` **in the coordinate ring**.

⚠️ That last step is modulo `W.Equation` and not before it.  In `R[X][Y]` itself the product need
not be a polynomial in `x`: at `(p, q) = (2, 0)` on `y² = x³ + 1` it is `ψ₂² = 4Y²`, of `Y`-degree
`2`.  This is exactly why the hypothesis `h : W.Equation x y` is needed below — it is what
`ψ_sq_evalEval` consumes to rewrite `ψ_k²` as `ΨSq_k`. -/
theorem ψ_add_mul_ψ_sub_evalEval (h : W.Equation x y) (p q : ℤ) :
    (W.ψ (p + q)).evalEval x y * (W.ψ (p - q)).evalEval x y
      = (W.Φ q).eval x * (W.ΨSq p).eval x - (W.Φ p).eval x * (W.ΨSq q).eval x := by
  have H := congrArg (fun g : R[X][Y] => g.evalEval x y) (W.ψ_add_mul_ψ_sub p q)
  simp only [evalEval_mul, evalEval_sub, evalEval_pow] at H
  rw [H, φ_evalEval h, φ_evalEval h, ψ_sq_evalEval h, ψ_sq_evalEval h]

section Field

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The quotient form of the `x`-difference identity**, over a field, at a point of `W` at which
neither `ΨSq_p` nor `ΨSq_q` vanishes:

```
Φ_q(x)/ΨSq_q(x) − Φ_p(x)/ΨSq_p(x) = ψ_{p+q}(x, y)·ψ_{p−q}(x, y)/(ΨSq_p(x)·ΨSq_q(x)).
```

⚠️ `Φₙ/ΨSqₙ` is the *division-polynomial* `x`-coordinate at `n`.  Identifying it with `x(n • P)` is
`WeierstrassCurve.Affine.HasXCoordFormula` — issue `#251` — which holds at every index over a field
of characteristic `≠ 2` (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`,
downstream of this file); see `EllipticCurves.Torsion.XDifferencePoint` for the point-level reading
at `(p, q) = (3, 2)`. -/
theorem Φ_div_ΨSq_sub_Φ_div_ΨSq (h : W.Equation x y) {p q : ℤ}
    (hp : (W.ΨSq p).eval x ≠ 0) (hq : (W.ΨSq q).eval x ≠ 0) :
    (W.Φ q).eval x / (W.ΨSq q).eval x - (W.Φ p).eval x / (W.ΨSq p).eval x
      = (W.ψ (p + q)).evalEval x y * (W.ψ (p - q)).evalEval x y
          / ((W.ΨSq p).eval x * (W.ΨSq q).eval x) := by
  rw [ψ_add_mul_ψ_sub_evalEval h, div_sub_div _ _ hq hp, div_eq_div_iff (mul_ne_zero hq hp)
    (mul_ne_zero hp hq)]
  ring

/-- **Two division-polynomial `x`-coordinates agree exactly when `ψ_{p+q}·ψ_{p−q}` vanishes at the
point.**  This is the form a torsion or coprimality argument consumes: over a field the product
vanishes iff one factor does, so `Φ_p/ΨSq_p = Φ_q/ΨSq_q` iff `ψ_{p+q}(x, y) = 0` or
`ψ_{p−q}(x, y) = 0`. -/
theorem Φ_div_ΨSq_eq_iff (h : W.Equation x y) {p q : ℤ}
    (hp : (W.ΨSq p).eval x ≠ 0) (hq : (W.ΨSq q).eval x ≠ 0) :
    (W.Φ q).eval x / (W.ΨSq q).eval x = (W.Φ p).eval x / (W.ΨSq p).eval x
      ↔ (W.ψ (p + q)).evalEval x y = 0 ∨ (W.ψ (p - q)).evalEval x y = 0 := by
  rw [← sub_eq_zero, Φ_div_ΨSq_sub_Φ_div_ΨSq h hp hq,
    div_eq_zero_iff, mul_eq_zero, mul_eq_zero]
  simp [hp, hq]

end Field

end WeierstrassCurve.Affine
