/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.NumberTheory.EllipticDivisibilitySequence
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.DivisionPolynomialEval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base elliptic-net relators for a normalised elliptic divisibility sequence

Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` provides the *elliptic relator*
`IsEllipticNet.rel W p q r s` of a sequence `W : ℤ → R`, together with the two evaluated forms

* `IsEllipticNet.rel_even m : rel W (m+1) (m-1) 1 0 = W(2m)·W 2·W 1² − W(m-1)²·W m·W(m+2)
  + W(m-2)·W m·W(m+1)²`, and
* `IsEllipticNet.rel_odd  m : rel W (m+1) m 1 0 = W(2m+1)·W 1³ − W(m+2)·W m³ + W(m-1)·W(m+1)³`,

for an *arbitrary* sequence `W`. For the canonical normalised elliptic divisibility sequence
`normEDS b c d` these two right-hand sides vanish identically — they are precisely the two-term
recurrences `normEDS_even` and `normEDS_odd` (using `normEDS 1 = 1` and `normEDS 2 = b`). This file
records the resulting *base* elliptic-net relators

* `normEDS_rel_even : rel (normEDS b c d) (m+1) (m-1) 1 0 = 0`, and
* `normEDS_rel_odd  : rel (normEDS b c d) (m+1) m 1 0 = 0`,

and specialises them to the division polynomials `W.ψ` of a Weierstrass curve, both as identities in
`R[X][Y]` and — via the evaluation-at-a-point homomorphism of
`EllipticCurves/Torsion/DivisionPolynomialEval.lean` — as identities among the values `ψₙ(x, y)` at
an affine point of `W`.

These are the base cases of the general four-term / elliptic-net recurrence
`rel (normEDS b c d) p q r 0 = 0` for *all* `p, q, r` (Ward's theorem), which is a standing Mathlib
`TODO` (`prove that normEDS satisfies IsEllipticDvdSequence`) and is developed separately.

⚠️ That general statement is Mathlib's `IsEllipticSequence`, and it is **equivalent to its `r = 1`
slice alone**: for any odd `W`, `IsEllipticNet.one_sq_mul_rel_zero`
(`EllipticCurves.Torsion.WardR1`, downstream of this file) writes `W 1 ^ 2 * rel W p q r 0` as a
`W(·)²`-combination of three `r = 1` relators, by `ring`. So the two relators recorded here are
base cases of a statement with no content beyond `∀ p q, rel W p q 1 0 = 0`.

## Main statements

* `normEDS_rel_even`, `normEDS_rel_odd` : the base relators of `normEDS b c d`.
* `WeierstrassCurve.Affine.ψ_rel_even`, `WeierstrassCurve.Affine.ψ_rel_odd` : the same for the
  division polynomials `W.ψ`, in `R[X][Y]`.
* `WeierstrassCurve.Affine.ψ_rel_even_evalEval`, `WeierstrassCurve.Affine.ψ_rel_odd_evalEval` : the
  base relators among the point-values `n ↦ (W.ψ n).evalEval x y`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4.
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
-/

open Polynomial
open scoped Polynomial.Bivariate

/-! ### Base relators for `normEDS` -/

section NormEDS

variable {R : Type*} [CommRing R] (b c d : R)

/-- The base *even* elliptic-net relator of the canonical normalised elliptic divisibility sequence
vanishes: `rel (normEDS b c d) (m + 1) (m - 1) 1 0 = 0`. This is the two-term recurrence
`normEDS_even` rephrased through `IsEllipticNet.rel_even`. -/
lemma normEDS_rel_even (m : ℤ) :
    IsEllipticNet.rel (normEDS b c d) (m + 1) (m - 1) 1 0 = 0 := by
  rw [IsEllipticNet.rel_even, normEDS_one, normEDS_two]
  linear_combination normEDS_even b c d m

/-- The base *odd* elliptic-net relator of the canonical normalised elliptic divisibility sequence
vanishes: `rel (normEDS b c d) (m + 1) m 1 0 = 0`. This is the two-term recurrence `normEDS_odd`
rephrased through `IsEllipticNet.rel_odd`. -/
lemma normEDS_rel_odd (m : ℤ) :
    IsEllipticNet.rel (normEDS b c d) (m + 1) m 1 0 = 0 := by
  rw [IsEllipticNet.rel_odd, normEDS_one]
  linear_combination normEDS_odd b c d m

end NormEDS

/-! ### Base relators for the division polynomials `W.ψ` -/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- The base *even* elliptic-net relator of the division polynomials `W.ψ`, as an identity in
`R[X][Y]`: `rel W.ψ (m + 1) (m - 1) 1 0 = 0`. Instance of `normEDS_rel_even` at
`b = W.ψ₂`, `c = C W.Ψ₃`, `d = C W.preΨ₄`, since `W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`. -/
lemma ψ_rel_even (m : ℤ) : IsEllipticNet.rel W.ψ (m + 1) (m - 1) 1 0 = 0 :=
  normEDS_rel_even W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) m

/-- The base *odd* elliptic-net relator of the division polynomials `W.ψ`, as an identity in
`R[X][Y]`: `rel W.ψ (m + 1) m 1 0 = 0`. -/
lemma ψ_rel_odd (m : ℤ) : IsEllipticNet.rel W.ψ (m + 1) m 1 0 = 0 :=
  normEDS_rel_odd W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) m

variable {x y : R}

/-- The base *even* elliptic-net relator among the point-values of the division polynomials at an
affine point `(x, y)` of `W`: `rel (fun n ↦ (W.ψ n).evalEval x y) (m + 1) (m - 1) 1 0 = 0`.
Obtained from `ψ_rel_even` by pushing it through the evaluation ring hom `evalEvalRingHom x y`. -/
lemma ψ_rel_even_evalEval (m : ℤ) :
    IsEllipticNet.rel (fun n ↦ (W.ψ n).evalEval x y) (m + 1) (m - 1) 1 0 = 0 := by
  have h := IsEllipticNet.map_rel W.ψ (evalEvalRingHom x y) (m + 1) (m - 1) 1 0
  rw [ψ_rel_even, map_zero] at h
  exact h.symm

/-- The base *odd* elliptic-net relator among the point-values of the division polynomials at an
affine point `(x, y)` of `W`: `rel (fun n ↦ (W.ψ n).evalEval x y) (m + 1) m 1 0 = 0`. -/
lemma ψ_rel_odd_evalEval (m : ℤ) :
    IsEllipticNet.rel (fun n ↦ (W.ψ n).evalEval x y) (m + 1) m 1 0 = 0 := by
  have h := IsEllipticNet.map_rel W.ψ (evalEvalRingHom x y) (m + 1) m 1 0
  rw [ψ_rel_odd, map_zero] at h
  exact h.symm

end WeierstrassCurve.Affine
