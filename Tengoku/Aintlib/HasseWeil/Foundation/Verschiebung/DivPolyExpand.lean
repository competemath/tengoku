/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.Algebra.Polynomial.Expand
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generic-CommRing division polynomial expand-range membership

For a Weierstrass curve `W : WeierstrassCurve R` over a commutative ring `R`
with `[CharP R p]` (`p` prime), the division polynomials `Φ_p, Ψ_p², Ψ_p` lie
in the image of `Polynomial.expand R p`. This is the **base case** of
Silverman III.6.2 for `q = p`.

This file contains generic-CommRing forms (works for any `[CharP R p]`,
including K-level `[Field K] [CharP K p]` and universal-MvPolynomial-level
`URing p = MvPolynomial AVar (ZMod p)`). The K-level versions in
`Verschiebung/QthRoots.lean` and the universal-level corollaries in
`Verschiebung/Route2Universal.lean` are direct one-line specialisations.

## Main results

* `Φ_two_mem_expand_two_charP`, `ΨSq_two_mem_expand_two_charP` — base case
  for `q = 2` (any `[CharP R 2]`).
* `b_relation_of_charP_three` — `b₈ = b₂ b₆ - b₄²` in `[CharP R 3]`.
* `Ψ₃_mem_expand_three_charP`, `ΨSq_three_mem_expand_three_charP`,
  `Φ_three_mem_expand_three_charP` — base case for `q = 3`
  (any `[CharP R 3]`).

## References

Silverman, *The Arithmetic of Elliptic Curves*, III.6.2.
-/

namespace HasseWeil

variable {R : Type*} [CommRing R]

/-- **Char-3 b-relation, generic in `R`**: `b₈ = b₂ · b₆ - b₄²`.
    Specialisation of mathlib's `WeierstrassCurve.b_relation` (`4·b₈ = b₂·b₆ - b₄²`)
    via `4 = 1` in char 3.
@isnad1 id=eq.0h2v.s6.fa6cf86d5682 from=translated src=- shape=463655c4 vocab=3f465ae7
-/
theorem b_relation_of_charP_three [CharP R 3] (W : WeierstrassCurve R) :
    W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3

end HasseWeil
