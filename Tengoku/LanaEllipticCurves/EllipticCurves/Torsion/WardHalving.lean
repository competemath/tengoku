/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.EllipticNetSlices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ward's theorem for `normEDS`: the `r = 1` addition formula, unconditionally

This file discharges `WeierstrassCurve.WardGapCore` and with it Ward's `r = 1` addition formula

```
IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0     for all p q : ℤ,
```

over an arbitrary `CommRing`, and hence `IsEllipticSequence (normEDS b c d)` — the elliptic-net
half of the standing Mathlib `TODO` *"prove that `normEDS` satisfies `IsEllipticDvdSequence`"*.

⚠️ **Only one of the two conjuncts.** `IsEllipticDvdSequence` is
`IsEllipticSequence W ∧ IsDvdSequence W`. The second conjunct, `IsDvdSequence (normEDS b c d)`, is
proved neither in Mathlib nor here, so the `TODO` is **half** closed, not closed.

## The induction, and why it is not the one that was tried

`EllipticCurves.Torsion.WardR1Core` reduces everything to the gap `≥ 3` case, and searches for a
uniform certificate along the **gap** axis — derive the band `|p − q| = g` from the bands
`|p − q| < g` at the *same* index — are recorded there as having failed. They are not this
induction. The one that works **halves the index**, which is the recursion `normEDS` is actually
defined by (`normEDSRec`, `preNormEDS'_even` / `preNormEDS'_odd`): for each of the four parity
classes of `(p, q)` there is a formal identity

```
W 2 ^ j * rel W (2m + ε) (2n + δ) 1 0
  = Σ cᵢ · (two-term relator)  +  Σ dⱼ · rel W Pⱼ Qⱼ 1 0
```

with integer polynomial cofactors, where the two-term relators are `normEDS_rel_odd` and
`normEDS_rel_even` — identically zero — and every `(Pⱼ, Qⱼ)` is drawn from
`{(m + i, n + j)}` together with `(m + n, m − n)` and `(m + n + 1, m − n ∓ 1)`, all of measure
`|P| + |Q|` **strictly smaller** than `|2m + ε| + |2n + δ|` on the range where the step is used.
Those are `cert_ee`, `cert_eo`, `cert_oe`, `cert_oo` below, with `j = 3, 1, 1, 2`.

⚠️ **The multiplier `W 2 ^ j` is not an optimisation; without it no such identity exists.** It is
forced by `normEDS_even`, which pins `normEDS b c d (2 * m)` only up to the factor
`normEDS b c d 2 = b`. Cancelling it needs an integral domain in which `W 2 ≠ 0`, which is exactly
what the universal ring `UnivEDS = ℤ[X₀, X₁, X₂]` and `normEDS_univ_ne_zero` of
`EllipticCurves.Torsion.WardR1` supply; the transfer to an arbitrary `CommRing` is
`WardR1Core`'s existing `aeval` step.

## The base cases: three come from the tree, two are re-derived inline

The induction runs on `|p| + |q|`, after the sign and swap symmetries (`rel_one_neg_left`,
`rel_one_neg_right`, `rel_one_swap`, all measure-preserving) reduce to `0 ≤ q ≤ p`. The four
parity certificates are used only when `q ≥ 2` and `p ≥ q + 3`; everything else is a base case, and
the five split in two:

* `p = q`, `p = q + 1` and `p = q + 2` are **hypotheses** of `rel_one_of_rec` (`hdiag`, `hrec1`,
  `hrec2`), discharged at `normEDS` by `normEDS_rel_one_univ_diag` of
  `EllipticCurves.Torsion.WardR1Core` and by the two-term recurrences `normEDS_rel_odd` /
  `normEDS_rel_even` of `EllipticCurves.Torsion.EllipticNetRel`.
* `q = 0` and `q = 1` are **re-derived inline**, as `hq0` and `hq1`, from `hzero`, `h1` and `hodd`
  alone. They have to be: `rel_one_of_rec` is stated for an arbitrary sequence over a domain and
  mentions no curve and no `normEDS`, so it cannot invoke
  `normEDS_rel_one_zero` / `normEDS_rel_one_one` of `EllipticCurves.Torsion.WardR1`. Those two do
  exist in the tree — this file simply does not reference them.

## Main statements

* `IsEllipticNet.rel_one_of_rec` : the induction, for **any** sequence over an integral domain that
  is odd, normalised, satisfies the two two-term relators and the diagonal slice, and has
  `W 2 ≠ 0`. It mentions no curve and no `normEDS`.
* `WeierstrassCurve.normEDS_rel_one_univ` : Ward's `r = 1` formula over `UnivEDS`.
* `WeierstrassCurve.wardGapCore` : `WardGapCore` holds.
* `WeierstrassCurve.normEDS_rel_one`, `normEDS_isEllipticSequence` : the formula and
  `IsEllipticSequence` over an arbitrary `CommRing`.
* `WeierstrassCurve.normEDS_isEllipticNet` : the **full** elliptic-net relation `rel … p q r s = 0`
  at every `s`, not only at `s = 0`, via `EllipticCurves.Torsion.EllipticNetSlices`.
* `WeierstrassCurve.Affine.ψ_rel_one`, `ψ_isEllipticSequence`, `ψ_isEllipticNet`, and their
  `evalEval` companions : the same for the division polynomials of a Weierstrass curve.

## References

* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4 (Exercise 3.7).
-/

namespace IsEllipticNet

variable {R : Type*} [CommRing R]

/-! ### The four parity certificates

Each is a formal identity, valid for **any** `W : ℤ → R` with `W 1 = 1`: no recurrence, no
`normEDS` and no curve. They are what the induction below runs on. -/

set_option maxHeartbeats 4000000 in
-- 138 summands in ~35 distinct atoms: `ring_nf` needs well over the
-- default budget to normalise both sides.
set_option maxRecDepth 40000 in
private lemma cert_ee {W : ℤ → R} (h1 : W 1 = 1) (m n : ℤ) :
    W 2 ^ 3 * rel W (2*m) (2*n) 1 0 =
      - W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n + 2) * W (m + n) *
          W (m + n + 1) * (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W (m + n) *
          W (m + n + 1) * (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n) * W (m - n + 1) * W (m + n - 1) *
          W (m + n + 2) * (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n + 1) * W (m - n + 2) * W (m + n - 1) *
          W (m + n) * (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 ^ 2 * W (n - 2) * W n * W (2*n) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n + 1) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 ^ 2 * W (n - 1) ^ 2 * W (2*n) * W (m - n - 1) * W m * W (m + 2) * W (m + n + 1) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 ^ 2 * W n * W (n + 2) * W (2*n) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n - 1) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 ^ 3 * W (2*n) ^ 2 * W (2*m + 1) * (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n - 2) * W (m - n + 1) * W (m + n - 1) *
          W (m + n) * (rel W (m + 1) m 1 0)
      + W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n - 2) * W (m - n + 1) * W (m + n - 1) *
          W (m + n) * (rel W (m + 1) m 1 0)
      + W 2 ^ 2 * W (n - 2) * W n * W (2*n) * W (m - n - 1) * W (m - 1) ^ 2 * W (m + n + 1) *
          (rel W (m + 1) m 1 0)
      - W 2 ^ 2 * W (n - 1) ^ 2 * W (2*n) * W (m - n - 1) * W (m - 2) * W m * W (m + n + 1) *
          (rel W (m + 1) m 1 0)
      + W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W (m + n - 1) *
          W (m + n + 1) * (rel W (m + 1) (m - 1) 1 0)
      + W 2 * W (n - 2) * W n * W (2*n + 1) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n - 1) *
          (rel W (m + 1) (m - 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (2*n - 1) * W (m - n - 2) * W (m + 1) ^ 2 * W (m + n) *
          (rel W (m + 1) (m - 1) 1 0)
      - 2 * W 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W (m - n) * W (m + 1) ^ 2 * W (m + n - 2) *
          (rel W (m + 1) (m - 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 1) * W (m + n - 1) *
          W (m + n + 1) * (rel W (m + 1) (m - 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W (2*n + 1) * W (m - n - 1) * W m * W (m + 2) * W (m + n - 1) *
          (rel W (m + 1) (m - 1) 1 0)
      + W 2 * W n ^ 2 * W (2*n + 1) * W (m - n) * W m * W (m + 2) * W (m + n - 2) *
          (rel W (m + 1) (m - 1) 1 0)
      - W 2 ^ 2 * W (n - 2) * W n * W (2*n) * W (m - n - 1) * W m ^ 2 * W (m + n + 1) *
          (rel W (m + 1) (m - 1) 1 0)
      + W 2 ^ 2 * W (n - 1) * W (n + 1) * W (2*n) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n - 1) *
          (rel W (m + 1) (m - 1) 1 0)
      + W 2 ^ 2 * W (n - 1) ^ 2 * W (2*n) * W (m - n - 1) * W (m - 1) * W (m + 1) * W (m + n + 1) *
          (rel W (m + 1) (m - 1) 1 0)
      + W 2 ^ 2 * W (2*n - 1) * W (2*n + 1) * W (2*m) * (rel W (m + 1) (m - 1) 1 0)
      + W 2 * W (m - n - 2) * W (m - n - 1) * W m * W (m + 1) ^ 2 * W (m + 2) * W (m + n - 1) *
          W (m + n) * (rel W ((n - 1) + 1) (n - 1) 1 0)
      - W 2 * W (m - n - 2) * W (m - n + 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W ((n - 1) + 1) (n - 1) 1 0)
      + W 2 ^ 2 * W n * W (n + 2) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n - 1) * W (2*m) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      - 2 * W 2 ^ 2 * W (2*n + 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (2*m) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      + W 2 ^ 2 * W (2*n + 1) * W (m - 1) ^ 2 * W m * W (m + 2) * W (2*m) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      + W 2 * W (m - n - 1) * W (m - n) * W m * W (m + 1) ^ 2 * W (m + 2) * W (m + n - 2) *
          W (m + n - 1) * (rel W (n + 1) n 1 0)
      + W 2 * W (m - n - 1) * W (m - n + 2) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W (n + 1) n 1 0)
      - W 2 * W (m - n - 1) * W (m - n + 2) * W (m - 1) ^ 2 * W m * W (m + 2) * W (m + n - 1) *
          W (m + n) * (rel W (n + 1) n 1 0)
      - 2 * W 2 * W (m - n) * W (m - n + 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n - 2) *
          W (m + n + 1) * (rel W (n + 1) n 1 0)
      + W 2 * W (m - n) * W (m - n + 1) * W (m - 1) ^ 2 * W m * W (m + 2) * W (m + n - 2) *
          W (m + n + 1) * (rel W (n + 1) n 1 0)
      + W 2 ^ 2 * W (n - 2) * W n * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n - 1) * W (2*m) *
          (rel W (n + 1) n 1 0)
      + W 2 ^ 2 * W (2*n - 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (2*m) * (rel W (n + 1) n 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 2) * W m ^ 2 * W (m + n) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 1) * W (m - 1) ^ 2 * W (m + n + 1) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n + 1) * W (2*m - 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n - 2) * W (m - 1) * W (m + 1) * W (m + n) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n - 1) * W (m - 2) * W m * W (m + n + 1) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n - 1) * W m * W (m + 2) * W (m + n + 1) * W (2*m - 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n) * W m ^ 2 * W (m + n - 2) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n - 1) * W (2*m - 1) *
          (rel W (n + 1) (n - 1) 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n) * W (m - 1) * W (m + 1) * W (m + n - 2) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 * W (m - n - 2) * W (m - n + 1) * W (m - 1) * W (m + 1) ^ 3 * W (m + n - 1) *
          W (m + n) * (rel W (n + 1) (n - 1) 1 0)
      - W 2 * W (m - n - 1) ^ 2 * W m * W (m + 1) ^ 2 * W (m + 2) * W (m + n - 1) ^ 2 *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 ^ 2 * W (n - 2) * W n * W (m - n - 1) * W m ^ 2 * W (m + n + 1) * W (2*m) *
          (rel W (n + 1) (n - 1) 1 0)
      - W 2 ^ 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n - 1) * W (2*m) *
          (rel W (n + 1) (n - 1) 1 0)
      - W 2 ^ 2 * W (n - 1) ^ 2 * W (m - n - 1) * W (m - 1) * W (m + 1) * W (m + n + 1) * W (2*m) *
          (rel W (n + 1) (n - 1) 1 0)
      + W 2 ^ 2 * W (2*n) * W (m - 2) * W m ^ 3 * W (2*m + 1) * (rel W (n + 1) (n - 1) 1 0)
      - W 2 ^ 2 * W (2*n) * W (m - 1) ^ 3 * W (m + 1) * W (2*m + 1) * (rel W (n + 1) (n - 1) 1 0)
      + W 2 ^ 2 * W (2*m - 2*n) * (rel W ((m + n) + 1) ((m + n) - 1) 1 0)
      - W 2 * W (m + n - 2) * W (m + n) * W (m + n + 1) ^ 2 *
          (rel W ((m - n) + 1) ((m - n) - 1) 1 0)
      + W 2 * W (m + n - 1) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W ((m - n) + 1) ((m - n) - 1) 1 0)
      + W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n - 1) * W (m + n + 1) * W (2*m + 1) *
          (rel W (m - 1) (n - 1) 1 0)
      + 2 * W 2 * W (n - 1) * W (n + 1) * W (m - n - 2) * W (m - n + 1) * W (m + 1) ^ 2 *
          W (m + n) * W (m + n + 1) * (rel W (m - 1) (n - 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n) * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n + 2) * (rel W (m - 1) (n - 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n - 1) * W (m + n + 1) * W (2*m + 1) *
          (rel W (m - 1) (n - 1) 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n + 1) * (rel W (m - 1) (n - 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W m ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m - 1) (n - 1) 1 0)
      - W 2 * W n ^ 2 * W (m - n - 2) * W (m - n + 1) * W m * W (m + 2) * W (m + n) *
          W (m + n + 1) * (rel W (m - 1) (n - 1) 1 0)
      + W 2 * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W m * W (m + 2) * W (m + n - 1) *
          W (m + n + 1) * (rel W (m - 1) (n - 1) 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n + 2) * W (m - 1) * W (m + 1) * W (m + n) *
          W (m + n + 1) * (rel W (m - 1) (n - 1) 1 0)
      + W 2 * W (m - n - 2) * W (m - n + 1) ^ 2 * W (m + n) * W (m + n + 1) ^ 2 *
          (rel W (m - 1) (n - 1) 1 0)
      + 2 * W 2 ^ 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W (m + 1) ^ 2 * W (2*m) *
          (rel W (m - 1) (n - 1) 1 0)
      - W 2 ^ 2 * W n * W (n + 2) * W (2*n) * W m ^ 2 * W (2*m + 1) * (rel W (m - 1) (n - 1) 1 0)
      - W 2 ^ 2 * W n ^ 2 * W (2*n + 1) * W m * W (m + 2) * W (2*m) * (rel W (m - 1) (n - 1) 1 0)
      + W 2 ^ 2 * W (n + 1) ^ 2 * W (2*n) * W (m - 1) * W (m + 1) * W (2*m + 1) *
          (rel W (m - 1) (n - 1) 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 2) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m - 1) n 1 0)
      + W 2 * W (n - 2) * W n * W (m - n - 1) * W (m - n) * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n + 2) * (rel W (m - 1) n 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W (m - 1) n 1 0)
      + 2 * W 2 * W n * W (n + 2) * W (m - n) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n - 2) *
          W (m + n + 1) * (rel W (m - 1) n 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n) * W (m - n + 1) * W m * W (m + 2) * W (m + n - 2) *
          W (m + n + 1) * (rel W (m - 1) n 1 0)
      - W 2 * W (2*n - 1) * W (m - n - 2) * W m * W (m + 1) ^ 2 * W (m + 2) * W (m + n) *
          (rel W (m - 1) n 1 0)
      - W 2 * W (2*n + 1) * W (m - n) * W m * W (m + 1) ^ 2 * W (m + 2) * W (m + n - 2) *
          (rel W (m - 1) n 1 0)
      + W 2 * W (m - n - 1) * W (m - n) * W (m - n + 2) * W (m + n - 1) * W (m + n) *
          W (m + n + 2) * (rel W (m - 1) n 1 0)
      - 2 * W 2 ^ 2 * W (n - 2) * W n * W (2*n + 1) * W (m + 1) ^ 2 * W (2*m) *
          (rel W (m - 1) n 1 0)
      + W 2 ^ 2 * W (n - 1) ^ 2 * W (2*n + 1) * W m * W (m + 2) * W (2*m) * (rel W (m - 1) n 1 0)
      - W 2 ^ 2 * W n * W (n + 2) * W (2*n - 1) * W (m + 1) ^ 2 * W (2*m) * (rel W (m - 1) n 1 0)
      + W 2 ^ 2 * W (2*n) * W (m - n - 1) * W m * W (m + 1) ^ 2 * W (m + 2) * W (m + n - 1) *
          (rel W (m - 1) n 1 0)
      + W 2 * W (n - 2) * W n * W (m - n - 1) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n + 1) * (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 1) * W (m - n + 2) * W m ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W (n - 2) * W n * W (m - n) * W (m - n + 1) * W m ^ 2 * W (m + n - 1) *
          W (m + n + 2) * (rel W (m - 1) (n + 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n + 2) * W (m + 1) ^ 2 *
          W (m + n - 1) * W (m + n) * (rel W (m - 1) (n + 1) 1 0)
      - 2 * W 2 * W (n - 1) * W (n + 1) * W (m - n) * W (m - n + 1) * W (m + 1) ^ 2 *
          W (m + n - 2) * W (m + n + 1) * (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W m * W (m + 2) * W (m + n - 1) *
          W (m + n + 1) * (rel W (m - 1) (n + 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n - 1) * W (m - n + 2) * W (m - 1) * W (m + 1) * W (m + n) *
          W (m + n + 1) * (rel W (m - 1) (n + 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n + 1) * W (m - n + 2) * W m ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W (m - 1) (n + 1) 1 0)
      + W 2 * W n ^ 2 * W (m - n) * W (m - n + 1) * W m * W (m + 2) * W (m + n - 2) *
          W (m + n + 1) * (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W (m - n) * W (m - n + 1) ^ 2 * W (m + n - 1) ^ 2 * W (m + n + 2) *
          (rel W (m - 1) (n + 1) 1 0)
      + W 2 ^ 2 * W (n - 2) * W n * W (2*n) * W m ^ 2 * W (2*m + 1) * (rel W (m - 1) (n + 1) 1 0)
      + W 2 ^ 2 * W (n - 1) * W (n + 1) * W (2*n - 1) * W (m + 1) ^ 2 * W (2*m) *
          (rel W (m - 1) (n + 1) 1 0)
      - W 2 ^ 2 * W (n - 1) ^ 2 * W (2*n) * W (m - 1) * W (m + 1) * W (2*m + 1) *
          (rel W (m - 1) (n + 1) 1 0)
      - W 2 ^ 2 * W (2*n) * W (m - n + 1) * W (m - 1) * W (m + 1) ^ 3 * W (m + n - 1) *
          (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n) * W m ^ 2 * W (m + n) * W (m + n + 1) *
          (rel W m (n - 2) 1 0)
      + W 2 * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n) * W (m - 1) * W (m + 1) * W (m + n) *
          W (m + n + 1) * (rel W m (n - 2) 1 0)
      - W 2 * W (m - n - 1) ^ 2 * W (m - n) * W (m + n) * W (m + n + 1) ^ 2 *
          (rel W m (n - 2) 1 0)
      + W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n - 2) * W (m + n) * W (2*m + 1) *
          (rel W m (n - 1) 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 2) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W m (n - 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n - 2) * W (m + n) * W (2*m + 1) *
          (rel W m (n - 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n - 2) * W (m - n - 1) * W m * W (m + 2) * W (m + n) *
          W (m + n + 1) * (rel W m (n - 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n) * W (m - n + 1) * W (m - 1) ^ 2 * W (m + n - 1) *
          W (m + n + 2) * (rel W m (n - 1) 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n) * W (m - n + 1) * W (m - 2) * W m * W (m + n - 1) *
          W (m + n + 2) * (rel W m (n - 1) 1 0)
      - W 2 ^ 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n - 1) * W (m + n + 1) * W (2*m) *
          (rel W m (n - 1) 1 0)
      + W 2 ^ 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n - 1) * W (m + n + 1) * W (2*m) *
          (rel W m (n - 1) 1 0)
      + W 2 * W (n - 3) * W (n - 1) * W (m - n - 1) * W (m - n) * W m ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W m (n + 1) 1 0)
      - W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n) * W (m + n - 2) * W (2*m + 1) *
          (rel W m (n + 1) 1 0)
      - W 2 * W (n - 2) ^ 2 * W (m - n - 1) * W (m - n) * W (m - 1) * W (m + 1) * W (m + n) *
          W (m + n + 1) * (rel W m (n + 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n) * W (m + n - 2) * W (2*m + 1) *
          (rel W m (n + 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n) * W (m - n + 1) * W (m - 2) * W m * W (m + n - 1) *
          W (m + n + 2) * (rel W m (n + 1) 1 0)
      - W 2 * W n * W (n + 2) * W (m - n + 1) * W (m - n + 2) * W (m - 1) ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W m (n + 1) 1 0)
      + W 2 ^ 2 * W (2*n) * W (m - n + 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n - 1) *
          (rel W m (n + 1) 1 0)
      + W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n - 1) * W (m + n + 1) * W (2*m - 1) *
          (rel W (m + 1) (n - 1) 1 0)
      + W 2 * W (n - 2) * W n * W (m - n - 2) * W (m - n - 1) * W m ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 2) * W (m - n - 1) * W (m + 1) ^ 2 *
          W (m + n - 1) * W (m + n) * (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n - 1) * W (m + n + 1) * W (2*m - 1) *
          (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W (m - n - 2) * W (m - n - 1) * W (m - 1) * W (m + 1) * W (m + n) *
          W (m + n + 1) * (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n + 1) * W (m + n - 1) * W (2*m - 1) *
          (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 2) * W (m - n + 1) * W m ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W (m + 1) (n - 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n - 1) ^ 2 * W (m + 1) ^ 2 * W (m + n - 1) ^ 2 *
          (rel W (m + 1) (n - 1) 1 0)
      + W 2 * W n ^ 2 * W (m - n - 1) * W (m - n) * W (m - 2) * W m * W (m + n - 1) *
          W (m + n + 2) * (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W (2*n + 1) * W (m - n - 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n - 1) *
          (rel W (m + 1) (n - 1) 1 0)
      + W 2 * W (2*n + 1) * W (m - n - 1) * W (m - 1) ^ 2 * W m * W (m + 2) * W (m + n - 1) *
          (rel W (m + 1) (n - 1) 1 0)
      + W 2 * W (n - 2) * W n * W (m - n - 2) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W (m + 1) n 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 2) * W (m - n + 1) * W (m - 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m + 1) n 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n - 2) * W (m - n + 1) * W (m - 2) * W m * W (m + n) *
          W (m + n + 1) * (rel W (m + 1) n 1 0)
      - W 2 * W (n - 1) ^ 2 * W (m - n - 1) * W (m - n) * W (m - 2) * W m * W (m + n - 1) *
          W (m + n + 2) * (rel W (m + 1) n 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n) * W (m + 1) ^ 2 * W (m + n - 2) *
          W (m + n - 1) * (rel W (m + 1) n 1 0)
      + W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W (m - 1) ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W (m + 1) n 1 0)
      + W 2 * W (2*n - 1) * W (m - n - 2) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n) *
          (rel W (m + 1) n 1 0)
      + 2 * W 2 * W (2*n + 1) * W (m - n) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n - 2) *
          (rel W (m + 1) n 1 0)
      - W 2 * W (2*n + 1) * W (m - n) * W (m - 1) ^ 2 * W m * W (m + 2) * W (m + n - 2) *
          (rel W (m + 1) n 1 0)
      - W 2 ^ 2 * W (2*n) * W (m - n - 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n - 1) *
          (rel W (m + 1) n 1 0)
      + W 2 * W (n - 2) * W n * W (m - n - 2) * W (m - n + 1) * W m ^ 2 * W (m + n - 1) *
          W (m + n) * (rel W (m + 1) (n + 1) 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 1) ^ 2 * W (m + 1) ^ 2 * W (m + n - 1) ^ 2 *
          (rel W (m + 1) (n + 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n) * W (m + 1) ^ 2 * W (m + n - 2) *
          W (m + n - 1) * (rel W (m + 1) (n + 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n + 2) * W (m - 1) ^ 2 *
          W (m + n - 1) * W (m + n) * (rel W (m + 1) (n + 1) 1 0)
      + W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n + 1) * W (m + n - 1) * W (2*m - 1) *
          (rel W (m + 1) (n + 1) 1 0) := by
  simp only [rel]
  ring_nf
  simp only [h1, one_pow, mul_one]
  ring_nf

set_option maxHeartbeats 4000000 in
-- 94 summands in ~35 distinct atoms: `ring_nf` needs well over the
-- default budget to normalise both sides.
set_option maxRecDepth 40000 in
private lemma cert_eo {W : ℤ → R} (h1 : W 1 = 1) (m n : ℤ) :
    W 2 * rel W (2*m) (2*n + 1) 1 0 =
      - W 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n + 1) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) ^ 3 * W (2*n + 1) * W (2*m + 1) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) ^ 3 * W (m - n) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 * W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n) * W (m - n + 1) * W (m + n) *
          W (m + n + 1) * (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W n * W (n + 2) * W (2*n + 1) * W (m - n) * W (m + 1) ^ 2 * W (m + n) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W n ^ 2 * W (2*n + 1) * W (m - n - 1) * W m * W (m + 2) * W (m + n + 1) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      + 2 * W 2 * W n ^ 3 * W (n + 2) * W (2*n + 1) * W (2*m + 1) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W n ^ 3 * W (n + 2) * W (m - n - 1) * W (m - n + 1) * W (m + n + 1) ^ 2 *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 * W n ^ 3 * W (n + 2) * W (m - n) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W 2 * W (2*n + 1) ^ 2 * W (2*m + 1) * (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W (n - 1) * W n ^ 2 * W (n + 1) * W (m - n - 2) * W (m - n - 1) * W (m + n) *
          W (m + n + 1) * (rel W (m + 1) m 1 0)
      + W 2 * W (n - 1) * W (n + 1) ^ 3 * W (2*n + 1) * W (2*m - 1) * (rel W (m + 1) m 1 0)
      + W 2 * W n ^ 2 * W (2*n + 1) * W (m - n - 1) * W (m - 2) * W m * W (m + n + 1) *
          (rel W (m + 1) m 1 0)
      - 2 * W 2 * W n ^ 3 * W (n + 2) * W (2*n + 1) * W (2*m - 1) * (rel W (m + 1) m 1 0)
      - W 2 * W n ^ 3 * W (n + 2) * W (m - n - 2) * W (m - n) * W (m + n) ^ 2 *
          (rel W (m + 1) m 1 0)
      - W 2 * W (n - 1) * W n ^ 2 * W (n + 1) * W (m - n - 1) ^ 2 * W (m + n + 1) ^ 2 *
          (rel W (m + 1) (m - 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W (m - n - 1) * W m ^ 2 * W (m + n + 1) *
          (rel W (m + 1) (m - 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) ^ 3 * W (m - n - 1) * W (m - n) * W (m + n) * W (m + n + 1) *
          (rel W (m + 1) (m - 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n) * W m ^ 2 * W (m + n + 2) * W (2*m - 1) *
          (rel W (n + 1) n 1 0)
      - W 2 * W n * W (n + 2) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) * W (2*m - 1) *
          (rel W (n + 1) n 1 0)
      - W 2 * W n ^ 2 * W (m - n - 2) * W (m - 1) * W (m + 1) * W (m + n) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      - W 2 * W n ^ 2 * W (m - n) * W (m - 1) * W (m + 1) * W (m + n + 2) * W (2*m - 1) *
          (rel W (n + 1) n 1 0)
      + W 2 * W (2*n + 1) * W (m - 2) * W m ^ 3 * W (2*m + 1) * (rel W (n + 1) n 1 0)
      - W 2 * W (2*n + 1) * W (m - 1) ^ 3 * W (m + 1) * W (2*m + 1) * (rel W (n + 1) n 1 0)
      - W 2 * W (m - n - 2) * W (m - n) * W (m - 1) * W (m + 1) ^ 3 * W (m + n) ^ 2 *
          (rel W (n + 1) n 1 0)
      - W 2 * W (m - n - 1) * W (m - n) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (n + 1) n 1 0)
      + W 2 * W (m - n - 1) * W (m - n) * W (m - 1) ^ 2 * W m * W (m + 2) * W (m + n) *
          W (m + n + 1) * (rel W (n + 1) n 1 0)
      + W 2 * W (m - n - 1) ^ 2 * W (m - 1) * W (m + 1) ^ 3 * W (m + n - 1) * W (m + n + 1) *
          (rel W (n + 1) n 1 0)
      + W 2 ^ 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W m ^ 2 * W (m + n + 1) * W (2*m) *
          (rel W (n + 1) n 1 0)
      + W 2 * W (2*m - 2*n - 1) * (rel W ((m + n) + 1) (m + n) 1 0)
      - W 2 * W (m + n - 1) * W (m + n + 1) ^ 3 * (rel W ((m - n - 1) + 1) (m - n - 1) 1 0)
      + W 2 * W (m + n) ^ 3 * W (m + n + 2) * (rel W ((m - n - 1) + 1) (m - n - 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n) * W m ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W (m - 1) n 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) ^ 2 * W (m + 1) ^ 2 * W (m + n + 1) ^ 2 *
          (rel W (m - 1) n 1 0)
      + W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n) * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m - 1) n 1 0)
      + W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) ^ 2 *
          (rel W (m - 1) n 1 0)
      - W 2 * W n * W (n + 2) * W (m - n) ^ 2 * W m ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W (m - 1) n 1 0)
      - W 2 * W n ^ 2 * W (m - n - 1) * W (m - n) * W (m - 1) * W (m + 1) * W (m + n + 1) *
          W (m + n + 2) * (rel W (m - 1) n 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W (m - 1) * W (m + 1) *
          W (m + n + 1) ^ 2 * (rel W (m - 1) n 1 0)
      + W 2 * W (n + 1) ^ 2 * W (m - n) ^ 2 * W (m - 1) * W (m + 1) * W (m + n) * W (m + n + 2) *
          (rel W (m - 1) n 1 0)
      - W 2 * W (2*n + 1) * W (m - n - 1) * W (m - 1) * W (m + 1) ^ 3 * W (m + n + 1) *
          (rel W (m - 1) n 1 0)
      + W 2 * W (m - n - 1) * W (m - n) ^ 2 * W (m + n) * W (m + n + 1) * W (m + n + 2) *
          (rel W (m - 1) n 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) ^ 2 *
          (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W n * W (n + 2) * W (m - n) * W (m - n + 1) * W m ^ 2 * W (m + n) * W (m + n + 1) *
          (rel W (m - 1) (n + 1) 1 0)
      + W 2 * W n ^ 2 * W (2*n + 1) * W (m - 1) * W (m + 1) * W (2*m + 1) *
          (rel W (m - 1) (n + 1) 1 0)
      + W 2 * W (2*n + 1) * W (m - n) * W (m - 1) * W (m + 1) ^ 3 * W (m + n) *
          (rel W (m - 1) (n + 1) 1 0)
      + W 2 * W (m - n - 1) * W (m - n) * W (m - n + 1) * W (m + n) * W (m + n + 1) ^ 2 *
          (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W (m - n) ^ 3 * W (m + n) ^ 2 * W (m + n + 2) * (rel W (m - 1) (n + 1) 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) ^ 2 * W m ^ 2 * W (m + n + 1) ^ 2 *
          (rel W m (n - 1) 1 0)
      + W 2 * W (n + 1) ^ 2 * W (m - n - 1) ^ 2 * W (m - 1) * W (m + 1) * W (m + n + 1) ^ 2 *
          (rel W m (n - 1) 1 0)
      - W 2 * W (m - n - 1) ^ 3 * W (m + n + 1) ^ 3 * (rel W m (n - 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 2) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W m n 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n) * W (m - 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W m n 1 0)
      - W 2 * W (n - 1) * W (n + 1) ^ 3 * W (m - n) * W (m + n + 2) * W (2*m - 1) *
          (rel W m n 1 0)
      + W 2 * W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n + 1) * W (m + n + 1) * W (2*m - 1) *
          (rel W m n 1 0)
      - W 2 * W n * W (n + 2) * W (2*n + 1) * W (m + 1) ^ 2 * W (2*m - 1) * (rel W m n 1 0)
      + W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n) * W m ^ 2 * W (m + n - 1) *
          W (m + n + 2) * (rel W m n 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n + 1) * W (m - 1) ^ 2 * W (m + n + 1) ^ 2 *
          (rel W m n 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) ^ 2 * W (m + 1) ^ 2 * W (m + n - 1) * W (m + n + 1) *
          (rel W m n 1 0)
      + W 2 * W n * W (n + 2) * W (m - n) ^ 2 * W (m - 1) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W m n 1 0)
      + W 2 * W n ^ 2 * W (m - n - 1) * W (m - n) * W (m - 2) * W m * W (m + n + 1) *
          W (m + n + 2) * (rel W m n 1 0)
      + W 2 * W n ^ 3 * W (n + 2) * W (m - n - 2) * W (m + n) * W (2*m + 1) * (rel W m n 1 0)
      + W 2 * W n ^ 3 * W (n + 2) * W (m - n) * W (m + n + 2) * W (2*m - 1) * (rel W m n 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n) * W (m - 1) * W (m + 1) * W (m + n - 1) *
          W (m + n + 2) * (rel W m n 1 0)
      + W 2 * W (n + 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W (m - 2) * W m * W (m + n + 1) ^ 2 *
          (rel W m n 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n) ^ 2 * W (m - 2) * W m * W (m + n) * W (m + n + 2) *
          (rel W m n 1 0)
      + 2 * W 2 * W (2*n + 1) * W (m - n - 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n + 1) *
          (rel W m n 1 0)
      - W 2 * W (2*n + 1) * W (m - n - 1) * W (m - 1) ^ 2 * W m * W (m + 2) * W (m + n + 1) *
          (rel W m n 1 0)
      - W 2 ^ 2 * W (n - 1) * W (n + 1) ^ 3 * W (m - n - 1) * W (m + n + 1) * W (2*m) *
          (rel W m n 1 0)
      + W 2 * W (n - 2) * W n * W (m - n - 1) ^ 2 * W m ^ 2 * W (m + n + 1) ^ 2 *
          (rel W m (n + 1) 1 0)
      - W 2 * W (n - 1) * W n ^ 2 * W (n + 1) * W (m - n - 2) * W (m + n) * W (2*m + 1) *
          (rel W m (n + 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W (m + 1) ^ 2 * W (2*m - 1) *
          (rel W m (n + 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 2) * W (m - n) * W (m + 1) ^ 2 * W (m + n) ^ 2 *
          (rel W m (n + 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n) * W m ^ 2 * W (m + n - 1) *
          W (m + n + 2) * (rel W m (n + 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n + 1) * W (m - 1) ^ 2 *
          W (m + n + 1) ^ 2 * (rel W m (n + 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) ^ 2 * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n + 1) * (rel W m (n + 1) 1 0)
      - W 2 * W (n - 1) ^ 2 * W (m - n - 1) ^ 2 * W (m - 1) * W (m + 1) * W (m + n + 1) ^ 2 *
          (rel W m (n + 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n) * W (m - n + 1) * W (m - 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W m (n + 1) 1 0)
      - W 2 * W n ^ 2 * W (2*n + 1) * W (m - 2) * W m * W (2*m + 1) * (rel W m (n + 1) 1 0)
      - W 2 * W n ^ 2 * W (2*n + 1) * W m * W (m + 2) * W (2*m - 1) * (rel W m (n + 1) 1 0)
      + W 2 * W n ^ 2 * W (m - n - 1) * W (m - n) * W (m - 1) * W (m + 1) * W (m + n - 1) *
          W (m + n + 2) * (rel W m (n + 1) 1 0)
      - W 2 * W n ^ 3 * W (n + 2) * W (m - n + 1) * W (m + n + 1) * W (2*m - 1) *
          (rel W m (n + 1) 1 0)
      - W 2 * W (2*n + 1) * W (m - n) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n) *
          (rel W m (n + 1) 1 0)
      + W 2 ^ 2 * W (n - 1) * W n ^ 2 * W (n + 1) * W (m - n - 1) * W (m + n + 1) * W (2*m) *
          (rel W m (n + 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 2) * W (m - n - 1) * W m ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m + 1) n 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) ^ 2 * W (m - 1) ^ 2 * W (m + n + 1) ^ 2 *
          (rel W (m + 1) n 1 0)
      + W 2 * W n * W (n + 2) * W (2*n + 1) * W m ^ 2 * W (2*m - 1) * (rel W (m + 1) n 1 0)
      + W 2 * W n * W (n + 2) * W (m - n - 2) * W (m - n) * W m ^ 2 * W (m + n) ^ 2 *
          (rel W (m + 1) n 1 0)
      - W 2 * W n * W (n + 2) * W (m - n - 1) * W (m - n) * W (m - 1) ^ 2 * W (m + n) *
          W (m + n + 1) * (rel W (m + 1) n 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W m ^ 2 * W (2*m - 1) *
          (rel W (m + 1) (n + 1) 1 0)
      + W 2 * W n ^ 2 * W (2*n + 1) * W (m - 1) * W (m + 1) * W (2*m - 1) *
          (rel W (m + 1) (n + 1) 1 0)
      - W 2 * W (m - n - 2) * W (m - n) * W (m + n + 1) ^ 2 * (rel W (m + n) (m - n) 1 0)
      + W 2 * W (m - n - 1) ^ 2 * W (m + n) * W (m + n + 2) * (rel W (m + n) (m - n) 1 0)
      + W 2 * W (2*n) * W (2*m) * (rel W (m + n + 1) (m - n - 1) 1 0) := by
  simp only [rel]
  ring_nf
  simp only [h1, one_pow, mul_one]
  ring_nf

set_option maxHeartbeats 4000000 in
-- 49 summands in ~35 distinct atoms: `ring_nf` needs well over the
-- default budget to normalise both sides.
set_option maxRecDepth 40000 in
private lemma cert_oe {W : ℤ → R} (h1 : W 1 = 1) (m n : ℤ) :
    W 2 * rel W (2*m + 1) (2*n) 1 0 =
      W 2 * W (n - 2) * W n ^ 3 * W (m - n - 1) * W (m - n + 1) * W (m + n + 1) ^ 2 *
          (rel W (m + 1) m 1 0)
      - W 2 * W (n - 2) * W n ^ 3 * W (m - n) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) m 1 0)
      - W 2 * W (n - 1) ^ 3 * W (n + 1) * W (m - n - 1) * W (m - n + 1) * W (m + n + 1) ^ 2 *
          (rel W (m + 1) m 1 0)
      + W 2 * W (n - 1) ^ 3 * W (n + 1) * W (m - n) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) m 1 0)
      + W 2 * W (2*n - 1) * W (2*n + 1) * W (2*m + 1) * (rel W (m + 1) m 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n) * W m ^ 2 * W (m + n + 2) * W (2*m + 1) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      + W 2 * W n * W (n + 2) * W (m - n) * W (m + 1) ^ 2 * W (m + n) * W (2*m + 1) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      + W 2 * W n ^ 2 * W (m - n) * W (m - 1) * W (m + 1) * W (m + n + 2) * W (2*m + 1) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      - W 2 * W (n + 1) ^ 2 * W (m - n) * W m * W (m + 2) * W (m + n) * W (2*m + 1) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      - W 2 * W (2*n + 1) * W (m - 1) * W (m + 1) ^ 3 * W (2*m + 1) *
          (rel W ((n - 1) + 1) (n - 1) 1 0)
      + W 2 * W (2*n + 1) * W m ^ 3 * W (m + 2) * W (2*m + 1) * (rel W ((n - 1) + 1) (n - 1) 1 0)
      + W 2 * W (n - 2) * W n * W (m - n) * W (m + 1) ^ 2 * W (m + n) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      - W 2 * W (n - 2) * W n * W (m - n + 1) * W m ^ 2 * W (m + n + 1) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      - W 2 * W (n - 1) ^ 2 * W (m - n) * W m * W (m + 2) * W (m + n) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n + 1) * W (m - 1) * W (m + 1) * W (m + n + 1) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      + W 2 * W (2*m - 2*n + 1) * (rel W ((m + n) + 1) (m + n) 1 0)
      - W 2 * W (m + n - 1) * W (m + n + 1) ^ 3 * (rel W ((m - n) + 1) (m - n) 1 0)
      + W 2 * W (m + n) ^ 3 * W (m + n + 2) * (rel W ((m - n) + 1) (m - n) 1 0)
      + W 2 * W (m - n - 1) * W (m - n + 1) ^ 2 * W (m + n + 1) ^ 3 * (rel W m (n - 1) 1 0)
      - W 2 * W (m - n) ^ 2 * W (m - n + 1) * W (m + n) * W (m + n + 1) * W (m + n + 2) *
          (rel W m (n - 1) 1 0)
      + W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n + 1) * W (m + n + 1) * W (2*m + 1) *
          (rel W m n 1 0)
      - W 2 * W (n - 2) * W n * W (2*n + 1) * W (m + 1) ^ 2 * W (2*m + 1) * (rel W m n 1 0)
      + W 2 * W (n - 2) * W n ^ 3 * W (m - n) * W (m + n + 2) * W (2*m + 1) * (rel W m n 1 0)
      - W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n + 1) * W (m + n + 1) * W (2*m + 1) *
          (rel W m n 1 0)
      + W 2 * W (n - 1) ^ 2 * W (2*n + 1) * W m * W (m + 2) * W (2*m + 1) * (rel W m n 1 0)
      - W 2 * W (n - 1) ^ 3 * W (n + 1) * W (m - n) * W (m + n + 2) * W (2*m + 1) *
          (rel W m n 1 0)
      - W 2 * W n * W (n + 2) * W (2*n - 1) * W (m + 1) ^ 2 * W (2*m + 1) * (rel W m n 1 0)
      + W 2 * W (n + 1) ^ 2 * W (2*n - 1) * W m * W (m + 2) * W (2*m + 1) * (rel W m n 1 0)
      - W 2 * W (m - n - 1) * W (m - n + 1) * W (m - n + 2) * W (m + n) * W (m + n + 1) ^ 2 *
          (rel W m n 1 0)
      + W 2 * W (m - n) ^ 2 * W (m - n + 2) * W (m + n) ^ 2 * W (m + n + 2) * (rel W m n 1 0)
      - W 2 * W (n - 2) * W n ^ 3 * W (m - n + 1) * W (m + n + 1) * W (2*m + 1) *
          (rel W m (n + 1) 1 0)
      + W 2 * W (n - 1) ^ 3 * W (n + 1) * W (m - n + 1) * W (m + n + 1) * W (2*m + 1) *
          (rel W m (n + 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) ^ 2 *
          (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n) ^ 2 * W m ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W n ^ 2 * W (m - n - 1) * W (m - n + 1) * W (m - 1) * W (m + 1) * W (m + n + 1) ^ 2 *
          (rel W (m + 1) (n - 1) 1 0)
      + W 2 * W n ^ 2 * W (m - n) ^ 2 * W (m - 1) * W (m + 1) * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W (n - 2) * W n * W (n + 1) ^ 2 * W (m - n) * W (m + n) * W (2*m + 1) *
          (rel W (m + 1) n 1 0)
      + W 2 * W (n - 2) * W n * W (2*n + 1) * W m ^ 2 * W (2*m + 1) * (rel W (m + 1) n 1 0)
      - W 2 * W (n - 2) * W n * W (m - n - 1) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) ^ 2 *
          (rel W (m + 1) n 1 0)
      + W 2 * W (n - 2) * W n * W (m - n) ^ 2 * W m ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) n 1 0)
      + W 2 * W (n - 1) ^ 2 * W n * W (n + 2) * W (m - n) * W (m + n) * W (2*m + 1) *
          (rel W (m + 1) n 1 0)
      - W 2 * W (n - 1) ^ 2 * W (2*n + 1) * W (m - 1) * W (m + 1) * W (2*m + 1) *
          (rel W (m + 1) n 1 0)
      + W 2 * W (n - 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W (m - 1) * W (m + 1) *
          W (m + n + 1) ^ 2 * (rel W (m + 1) n 1 0)
      - W 2 * W (n - 1) ^ 2 * W (m - n) ^ 2 * W (m - 1) * W (m + 1) * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) n 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (2*n - 1) * W m ^ 2 * W (2*m + 1) *
          (rel W (m + 1) (n + 1) 1 0)
      - W 2 * W n ^ 2 * W (2*n - 1) * W (m - 1) * W (m + 1) * W (2*m + 1) *
          (rel W (m + 1) (n + 1) 1 0)
      + W 2 * W (m - n) * W (m - n + 2) * W (m + n + 1) ^ 2 * (rel W (m + n) (m - n) 1 0)
      - W 2 * W (m - n + 1) ^ 2 * W (m + n) * W (m + n + 2) * (rel W (m + n) (m - n) 1 0)
      - W 2 * W (2*n) * W (2*m) * (rel W (m + n + 1) (m - n + 1) 1 0) := by
  simp only [rel]
  ring_nf
  simp only [h1, one_pow, mul_one]
  ring_nf

set_option maxHeartbeats 4000000 in
-- 110 summands in ~35 distinct atoms: `ring_nf` needs well over the
-- default budget to normalise both sides.
set_option maxRecDepth 40000 in
private lemma cert_oo {W : ℤ → R} (h1 : W 1 = 1) (m n : ℤ) :
    W 2 ^ 2 * rel W (2*m + 1) (2*n + 1) 1 0 =
      - W (n - 1) * W (n + 1) * W (2*n + 1) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n + 3) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W (n - 1) * W (n + 1) ^ 3 * W (m - n + 1) ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W n ^ 2 * W (2*n + 1) * W (m - n + 1) * W m * W (m + 2) * W (m + n + 3) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      - W n ^ 3 * W (n + 2) * W (m - n + 1) ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W ((m - 1) + 1) (m - 1) 1 0)
      + W 2 * W (n + 1) * W (n + 3) * W (2*n) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) *
          (rel W (m + 1) m 1 0)
      - W 2 * W (n + 2) ^ 2 * W (2*n) * W (m - n + 1) * W (m - 1) * W (m + 1) * W (m + n + 1) *
          (rel W (m + 1) m 1 0)
      + W 2 ^ 2 * W (2*n) * W (2*n + 2) * W (2*m + 1) * (rel W (m + 1) m 1 0)
      - W (n - 2) * W n ^ 3 * W (m - n - 1) ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W (m + 1) m 1 0)
      - W (n - 1) * W (n + 1) * W (2*n + 1) * W (m - n + 1) * W (m - 1) ^ 2 * W (m + n + 3) *
          (rel W (m + 1) m 1 0)
      + W (n - 1) ^ 3 * W (n + 1) * W (m - n - 1) ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W (m + 1) m 1 0)
      - W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W (m + n - 1) *
          W (m + n + 2) * (rel W (m + 1) m 1 0)
      + W n * W (n + 2) * W (2*n + 1) * W (m - n + 2) * W (m - 1) ^ 2 * W (m + n + 2) *
          (rel W (m + 1) m 1 0)
      + W n ^ 2 * W (2*n + 1) * W (m - n + 1) * W (m - 2) * W m * W (m + n + 3) *
          (rel W (m + 1) m 1 0)
      + W n ^ 3 * W (n + 2) * W (m - n - 2) * W (m - n + 2) * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) m 1 0)
      - W 2 * W (n - 1) * W (n + 1) ^ 3 * W (2*n + 1) * W (2*m + 2) * (rel W (m + 1) (m - 1) 1 0)
      + W 2 * W n ^ 3 * W (n + 2) * W (2*n + 1) * W (2*m + 2) * (rel W (m + 1) (m - 1) 1 0)
      - W 2 * W (2*n + 1) ^ 2 * W (2*m + 2) * (rel W (m + 1) (m - 1) 1 0)
      + W (n - 1) * W (n + 1) * W (2*n + 1) * W (m - n + 1) * W m ^ 2 * W (m + n + 3) *
          (rel W (m + 1) (m - 1) 1 0)
      - W (n - 1) * W (n + 1) ^ 3 * W (m - n - 1) * W (m - n + 2) * W (m + n + 1) * W (m + n + 2) *
          (rel W (m + 1) (m - 1) 1 0)
      + W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n) * W (m - n + 2) * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) (m - 1) 1 0)
      - W n * W (n + 2) * W (2*n + 1) * W (m - n + 2) * W m ^ 2 * W (m + n + 2) *
          (rel W (m + 1) (m - 1) 1 0)
      - W n ^ 2 * W (2*n + 1) * W (m - n + 1) * W (m - 1) * W (m + 1) * W (m + n + 3) *
          (rel W (m + 1) (m - 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) ^ 3 * W (2*n + 1) * W (2*m) *
          (rel W ((m + 1) + 1) ((m + 1) - 1) 1 0)
      - W 2 * W n ^ 3 * W (n + 2) * W (2*n + 1) * W (2*m) *
          (rel W ((m + 1) + 1) ((m + 1) - 1) 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m + 2) ^ 2 * W (m + n + 1) * W (2*m) *
          (rel W (n + 1) n 1 0)
      + W 2 * W n * W (n + 2) * W (m - n + 2) * W m ^ 2 * W (m + n + 2) * W (2*m) *
          (rel W (n + 1) n 1 0)
      + W 2 * W n ^ 2 * W (m - n - 1) * W (m + 1) * W (m + 3) * W (m + n + 1) * W (2*m) *
          (rel W (n + 1) n 1 0)
      + W 2 * W (2*n + 1) * W (m - 2) * W m * W (m + 1) ^ 2 * W (2*m + 2) * (rel W (n + 1) n 1 0)
      - W 2 * W (2*n + 1) * W (m - 1) ^ 2 * W m * W (m + 2) * W (2*m + 2) * (rel W (n + 1) n 1 0)
      + W (n - 1) * W (n + 1) * W (m - n + 1) * W (m - 1) ^ 2 * W (m + n + 3) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      + W (n - 1) * W (n + 1) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n + 3) * W (2*m - 1) *
          (rel W (n + 1) n 1 0)
      - W n * W (n + 2) * W (m - n + 2) * W (m - 1) ^ 2 * W (m + n + 2) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      - W n ^ 2 * W (m - n + 1) * W (m - 2) * W m * W (m + n + 3) * W (2*m + 1) *
          (rel W (n + 1) n 1 0)
      - W n ^ 2 * W (m - n + 1) * W m * W (m + 2) * W (m + n + 3) * W (2*m - 1) *
          (rel W (n + 1) n 1 0)
      + W (m - n - 2) * W (m - n + 2) * W (m - 1) * W (m + 1) ^ 3 * W (m + n) * W (m + n + 2) *
          (rel W (n + 1) n 1 0)
      - W (m - n - 1) * W (m - n + 2) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W (n + 1) n 1 0)
      - W (n - 1) * W (n + 1) * W (m - n - 1) * W m ^ 2 * W (m + n + 3) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W n ^ 2 * W (m - n - 1) * W (m - 1) * W (m + 1) * W (m + n + 3) * W (2*m + 1) *
          (rel W (n + 1) (n - 1) 1 0)
      + W (m - n - 2) * W (m - n + 1) * W (m - 1) * W (m + 1) ^ 3 * W (m + n + 1) * W (m + n + 2) *
          (rel W (n + 1) (n - 1) 1 0)
      - W (m - n - 2) * W (m - n + 1) * W m ^ 3 * W (m + 2) * W (m + n + 1) * W (m + n + 2) *
          (rel W (n + 1) (n - 1) 1 0)
      - W 2 * W (2*n) * W (m - 1) * W (m + 1) ^ 3 * W (2*m + 1) *
          (rel W ((n + 1) + 1) ((n + 1) - 1) 1 0)
      + W 2 * W (2*n) * W m ^ 3 * W (m + 2) * W (2*m + 1) *
          (rel W ((n + 1) + 1) ((n + 1) - 1) 1 0)
      + W 2 * W (2*m - 2*n) * (rel W ((m + n + 1) + 1) ((m + n + 1) - 1) 1 0)
      - W (m + n - 1) * W (m + n + 1) * W (m + n + 2) ^ 2 *
          (rel W ((m - n) + 1) ((m - n) - 1) 1 0)
      + W (m + n) ^ 2 * W (m + n + 1) * W (m + n + 3) * (rel W ((m - n) + 1) ((m - n) - 1) 1 0)
      - W (n - 1) * W (n + 1) ^ 3 * W (m - n + 1) * W (m + n + 3) * W (2*m + 1) *
          (rel W (m - 1) n 1 0)
      + W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n + 2) * W (m + n + 2) * W (2*m + 1) *
          (rel W (m - 1) n 1 0)
      + W n * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W (m + 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W (m - 1) n 1 0)
      - W n * W (n + 2) * W (m - n) * W (m - n + 2) * W m ^ 2 * W (m + n + 2) ^ 2 *
          (rel W (m - 1) n 1 0)
      - W n * W (n + 2) * W (m - n + 1) ^ 2 * W m ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W (m - 1) n 1 0)
      + W n ^ 3 * W (n + 2) * W (m - n + 1) * W (m + n + 3) * W (2*m + 1) * (rel W (m - 1) n 1 0)
      + W (n + 1) ^ 2 * W (m - n + 1) ^ 2 * W (m - 1) * W (m + 1) * W (m + n + 1) * W (m + n + 3) *
          (rel W (m - 1) n 1 0)
      - W (m - n - 1) * W (m - n) * W (m - n + 2) * W (m + n + 1) * W (m + n + 2) ^ 2 *
          (rel W (m - 1) n 1 0)
      - 2 * W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n + 2) * W (m + 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W (m - 1) (n + 1) 1 0)
      + W (n - 1) * W (n + 1) * W (m - n + 1) ^ 2 * W m ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W (m - 1) (n + 1) 1 0)
      + W n * W (n + 2) * W (m - n) * W (m - n + 2) * W (m + 1) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W (m - 1) (n + 1) 1 0)
      + W n ^ 2 * W (m - n) * W (m - n + 2) * W (m - 1) * W (m + 1) * W (m + n + 2) ^ 2 *
          (rel W (m - 1) (n + 1) 1 0)
      - W n ^ 2 * W (m - n + 1) ^ 2 * W (m - 1) * W (m + 1) * W (m + n + 1) * W (m + n + 3) *
          (rel W (m - 1) (n + 1) 1 0)
      - W n ^ 3 * W (n + 2) * W (m - n + 2) * W (m + n + 2) * W (2*m + 1) *
          (rel W (m - 1) (n + 1) 1 0)
      - W (2*n + 1) * W (m - n + 2) * W (m - 1) * W (m + 1) ^ 3 * W (m + n + 2) *
          (rel W (m - 1) (n + 1) 1 0)
      + W (n - 1) * W (n + 1) ^ 3 * W (m - n - 1) * W (m + n + 3) * W (2*m + 1) *
          (rel W m (n - 1) 1 0)
      - W n * W (n + 2) * W (m - n - 2) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W m (n - 1) 1 0)
      + W n * W (n + 2) * W (m - n - 1) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W m (n - 1) 1 0)
      - W n ^ 3 * W (n + 2) * W (m - n - 1) * W (m + n + 3) * W (2*m + 1) * (rel W m (n - 1) 1 0)
      + W (n + 1) ^ 2 * W (m - n - 2) * W (m - n + 1) * W m * W (m + 2) * W (m + n + 1) *
          W (m + n + 2) * (rel W m (n - 1) 1 0)
      - W (n + 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W (m - 1) * W (m + 1) * W (m + n + 1) *
          W (m + n + 3) * (rel W m (n - 1) 1 0)
      - W 2 * W n * W (n + 1) ^ 2 * W (n + 2) * W (m - n + 2) * W (m + n + 2) * W (2*m) *
          (rel W m n 1 0)
      - W n * W (n + 2) * W (m - n - 2) * W (m - n + 2) * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 2) * (rel W m n 1 0)
      + W n * W (n + 2) * W (m - n) * W (m - n + 2) * W (m - 1) ^ 2 * W (m + n + 2) ^ 2 *
          (rel W m n 1 0)
      - W (m - n - 2) * W (m - n + 1) ^ 2 * W (m + n) * W (m + n + 1) * W (m + n + 3) *
          (rel W m n 1 0)
      + W (m - n - 1) ^ 2 * W (m - n + 2) * W (m + n) * W (m + n + 1) * W (m + n + 3) *
          (rel W m n 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W (m + 2) ^ 2 * W (2*m) *
          (rel W m (n + 1) 1 0)
      - W 2 * W n ^ 2 * W (2*n + 1) * W (m + 1) * W (m + 3) * W (2*m) * (rel W m (n + 1) 1 0)
      + W 2 * W n ^ 3 * W (n + 2) * W (m - n + 2) * W (m + n + 2) * W (2*m) *
          (rel W m (n + 1) 1 0)
      + W (n - 2) * W n * W (m - n - 2) * W (m - n + 1) * W (m + 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W m (n + 1) 1 0)
      - W (n - 2) * W n * W (m - n - 1) * W (m - n + 1) * W m ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W m (n + 1) 1 0)
      + W (n - 2) * W n ^ 3 * W (m - n - 1) * W (m + n + 3) * W (2*m + 1) * (rel W m (n + 1) 1 0)
      + W (n - 1) * W (n + 1) * W (m - n - 2) * W (m - n + 2) * W (m + 1) ^ 2 * W (m + n) *
          W (m + n + 2) * (rel W m (n + 1) 1 0)
      - W (n - 1) ^ 2 * W (m - n - 2) * W (m - n + 1) * W m * W (m + 2) * W (m + n + 1) *
          W (m + n + 2) * (rel W m (n + 1) 1 0)
      + W (n - 1) ^ 2 * W (m - n - 1) * W (m - n + 1) * W (m - 1) * W (m + 1) * W (m + n + 1) *
          W (m + n + 3) * (rel W m (n + 1) 1 0)
      - W (n - 1) ^ 3 * W (n + 1) * W (m - n - 1) * W (m + n + 3) * W (2*m + 1) *
          (rel W m (n + 1) 1 0)
      - W n * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W (m + 1) ^ 2 * W (m + n - 1) *
          W (m + n + 2) * (rel W m (n + 1) 1 0)
      + W n ^ 2 * W (m - n - 2) * W (m - n + 2) * W m * W (m + 2) * W (m + n) * W (m + n + 2) *
          (rel W m (n + 1) 1 0)
      - W n ^ 2 * W (m - n) * W (m - n + 2) * W (m - 2) * W m * W (m + n + 2) ^ 2 *
          (rel W m (n + 1) 1 0)
      + W (2*n + 1) * W (m - n + 2) * W (m - 2) * W m * W (m + 1) ^ 2 * W (m + n + 2) *
          (rel W m (n + 1) 1 0)
      - W 2 * W (2*n) * W (m - n + 1) * W (m - 1) * W (m + 1) ^ 3 * W (m + n + 1) *
          (rel W m (n + 2) 1 0)
      + W 2 * W (2*n) * W (m - n + 1) * W m ^ 3 * W (m + 2) * W (m + n + 1) *
          (rel W m (n + 2) 1 0)
      + W (n - 1) * W (n + 1) * W (m - n - 2) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W (m + 1) (n - 1) 1 0)
      - W (n - 1) * W (n + 1) * W (m - n - 1) ^ 2 * W m ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W (m + 1) (n - 1) 1 0)
      - W n ^ 2 * W (m - n - 2) * W (m - n - 1) * W m * W (m + 2) * W (m + n + 1) * W (m + n + 2) *
          (rel W (m + 1) (n - 1) 1 0)
      + W n ^ 2 * W (m - n - 1) ^ 2 * W (m - 1) * W (m + 1) * W (m + n + 1) * W (m + n + 3) *
          (rel W (m + 1) (n - 1) 1 0)
      - W 2 * W (n + 1) * W (n + 3) * W (2*n) * W m ^ 2 * W (2*m + 1) * (rel W (m + 1) n 1 0)
      + W 2 * W (n + 2) ^ 2 * W (2*n) * W (m - 1) * W (m + 1) * W (2*m + 1) *
          (rel W (m + 1) n 1 0)
      - W (n - 2) * W n * W (m - n - 2) * W (m - n - 1) * W (m + 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W (m + 1) n 1 0)
      + W (n - 2) * W n * W (m - n - 1) ^ 2 * W m ^ 2 * W (m + n + 1) * W (m + n + 3) *
          (rel W (m + 1) n 1 0)
      - W (n - 1) * W (n + 1) ^ 3 * W (m - n + 1) * W (m + n + 3) * W (2*m - 1) *
          (rel W (m + 1) n 1 0)
      + W (n - 1) ^ 2 * W (m - n - 2) * W (m - n - 1) * W m * W (m + 2) * W (m + n + 1) *
          W (m + n + 2) * (rel W (m + 1) n 1 0)
      - W (n - 1) ^ 2 * W (m - n - 1) ^ 2 * W (m - 1) * W (m + 1) * W (m + n + 1) * W (m + n + 3) *
          (rel W (m + 1) n 1 0)
      + W n ^ 3 * W (n + 2) * W (m - n + 1) * W (m + n + 3) * W (2*m - 1) * (rel W (m + 1) n 1 0)
      + W (n - 1) * W (n + 1) * W (m - n - 1) * W (m - n + 2) * W (m - 1) ^ 2 * W (m + n + 1) *
          W (m + n + 2) * (rel W (m + 1) (n + 1) 1 0)
      + W n * W (n + 2) * W (m - n - 1) * W (m - n + 2) * W m ^ 2 * W (m + n - 1) * W (m + n + 2) *
          (rel W (m + 1) (n + 1) 1 0)
      - W n * W (n + 2) * W (m - n) * W (m - n + 2) * W (m - 1) ^ 2 * W (m + n) * W (m + n + 2) *
          (rel W (m + 1) (n + 1) 1 0)
      - W n ^ 2 * W (m - n - 2) * W (m - n + 2) * W (m - 1) * W (m + 1) * W (m + n) *
          W (m + n + 2) * (rel W (m + 1) (n + 1) 1 0)
      + W (m - n - 2) * W (m - n + 1) ^ 2 * W (m + n - 1) * W (m + n + 1) * W (m + n + 2) *
          (rel W (m + 1) (n + 1) 1 0)
      + W 2 * W (n - 1) * W (n + 1) * W (2*n) * W m ^ 2 * W (2*m + 1) *
          (rel W (m + 1) (n + 2) 1 0)
      - W 2 * W n ^ 2 * W (2*n) * W (m - 1) * W (m + 1) * W (2*m + 1) *
          (rel W (m + 1) (n + 2) 1 0)
      + W 2 * W (n - 1) * W (n + 1) ^ 3 * W (m - n - 1) * W (m + n + 1) * W (2*m) *
          (rel W (m + 2) n 1 0)
      - W 2 * W n ^ 3 * W (n + 2) * W (m - n - 1) * W (m + n + 1) * W (2*m) *
          (rel W (m + 2) n 1 0)
      - W 2 * W (n - 1) * W (n + 1) * W (2*n + 1) * W m ^ 2 * W (2*m) *
          (rel W (m + 2) (n + 1) 1 0)
      + W 2 * W n ^ 2 * W (2*n + 1) * W (m - 1) * W (m + 1) * W (2*m) *
          (rel W (m + 2) (n + 1) 1 0) := by
  simp only [rel]
  ring_nf
  simp only [h1, one_pow, mul_one]
  ring_nf

/-! ### The induction -/

/-- Move an arbitrary index pair to `0 ≤ q ≤ p` without changing `|p| + |q|`, using the sign and
swap symmetries of the `r = 1` relator. -/
private lemma rel_one_of_le {W : ℤ → R} (hodd : W.Odd) (M : ℕ)
    (h : ∀ p q : ℤ, 0 ≤ q → q ≤ p → p.natAbs + q.natAbs ≤ M → rel W p q 1 0 = 0)
    (P Q : ℤ) (hPQ : P.natAbs + Q.natAbs ≤ M) : rel W P Q 1 0 = 0 := by
  have habs : rel W P Q 1 0 = rel W (P.natAbs : ℤ) (Q.natAbs : ℤ) 1 0 := by
    rcases Int.natAbs_eq P with hP | hP <;> rcases Int.natAbs_eq Q with hQ | hQ
    · rw [← hP, ← hQ]
    · rw [← hP]; nth_rewrite 1 [hQ]; rw [rel_one_neg_right W hodd]
    · nth_rewrite 1 [hP]; rw [← hQ, rel_one_neg_left W hodd]
    · nth_rewrite 1 [hP]; nth_rewrite 1 [hQ]
      rw [rel_one_neg_left W hodd, rel_one_neg_right W hodd]
  rw [habs]
  rcases le_total (Q.natAbs : ℤ) (P.natAbs : ℤ) with hle | hle
  · exact h _ _ (by positivity) hle (by simp [Int.natAbs_abs]; omega)
  · rw [rel_one_swap W hodd, h _ _ (by positivity) hle (by simp [Int.natAbs_abs]; omega), neg_zero]

/-- **Ward's `r = 1` addition formula, from the two two-term relators alone.**

Over an integral domain, a sequence that is odd, has `W 0 = 0`, `W 1 = 1` and `W 2 ≠ 0`, and
satisfies the two two-term relators together with the diagonal slice, satisfies the whole `r = 1`
relation. Proved by strong induction on `|p| + |q|`, using the four parity certificates above; the
factor `W 2 ^ j` each certificate carries is cancelled in the domain, which is the only place
`IsDomain` and `W 2 ≠ 0` are used. -/
theorem rel_one_of_rec [IsDomain R] {W : ℤ → R}
    (hodd : W.Odd) (hzero : W 0 = 0) (h1 : W 1 = 1) (h2 : W 2 ≠ 0)
    (hrec1 : ∀ m : ℤ, rel W (m + 1) m 1 0 = 0)
    (hrec2 : ∀ m : ℤ, rel W (m + 1) (m - 1) 1 0 = 0)
    (hdiag : ∀ x : ℤ, rel W x x 1 0 = 0)
    (p q : ℤ) : rel W p q 1 0 = 0 := by
  have hm1 : W (-1) = -1 := by rw [hodd 1, h1]
  have hq0 : ∀ x : ℤ, rel W x 0 1 0 = 0 := by
    intro x
    simp only [rel, add_zero, sub_zero, zero_add, zero_sub, hzero, h1, hm1]
    ring
  have hq1 : ∀ x : ℤ, rel W x 1 1 0 = 0 := by
    intro x
    simp only [rel, add_zero]
    rw [show (1 : ℤ) - 1 = 0 by ring, hzero]
    ring
  suffices key : ∀ N : ℕ, ∀ a b : ℤ, 0 ≤ b → b ≤ a → a.natAbs + b.natAbs ≤ N →
      rel W a b 1 0 = 0 by
    exact rel_one_of_le hodd _ (key (p.natAbs + q.natAbs)) p q le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro a b hb0 hba hN
  have ihAll : ∀ P Q : ℤ, P.natAbs + Q.natAbs < a.natAbs + b.natAbs → rel W P Q 1 0 = 0 := by
    intro P Q hPQ
    refine rel_one_of_le hodd (P.natAbs + Q.natAbs) ?_ P Q le_rfl
    exact fun x y hx hxy hle => ihN (P.natAbs + Q.natAbs) (by omega) x y hx hxy hle
  rcases eq_or_lt_of_le hb0 with hb | hb
  · rw [← hb]; exact hq0 a
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ b by omega) with hb1 | hb1
  · rw [← hb1]; exact hq1 a
  have hb2 : 2 ≤ b := by omega
  rcases eq_or_lt_of_le hba with hab | hab
  · rw [← hab]; exact hdiag b
  rcases eq_or_lt_of_le (show b + 1 ≤ a by omega) with hg1 | hg1
  · rw [← hg1]; exact hrec1 b
  rcases eq_or_lt_of_le (show b + 2 ≤ a by omega) with hg2 | hg2
  · rw [← hg2]
    have hh := hrec2 (b + 1)
    rw [show b + 1 + 1 = b + 2 by ring, show b + 1 - 1 = b by ring] at hh
    exact hh
  have hgap : b + 3 ≤ a := by omega
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' a
  · obtain ⟨n, hn | hn⟩ := Int.even_or_odd' b
    · subst hm; subst hn
      have hc := cert_ee (W := W) h1 m n
      have g1 : rel W (m - 1) (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g2 : rel W (m - 1) n 1 0 = 0 := ihAll _ _ (by omega)
      have g3 : rel W (m - 1) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g4 : rel W m (n - 2) 1 0 = 0 := ihAll _ _ (by omega)
      have g5 : rel W m (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g6 : rel W m (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g7 : rel W (m + 1) (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g8 : rel W (m + 1) n 1 0 = 0 := ihAll _ _ (by omega)
      have g9 : rel W (m + 1) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      simp only [hrec1, hrec2, g1, g2, g3, g4, g5, g6, g7, g8, g9, mul_zero, sub_zero,
        add_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ h2)
    · subst hm; subst hn
      have hc := cert_eo (W := W) h1 m n
      have g1 : rel W (m - 1) n 1 0 = 0 := ihAll _ _ (by omega)
      have g2 : rel W (m - 1) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g3 : rel W m (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g4 : rel W m n 1 0 = 0 := ihAll _ _ (by omega)
      have g5 : rel W m (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g6 : rel W (m + 1) n 1 0 = 0 := ihAll _ _ (by omega)
      have g7 : rel W (m + 1) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g8 : rel W (m + n) (m - n) 1 0 = 0 := ihAll _ _ (by omega)
      have g9 : rel W (m + n + 1) (m - n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      simp only [hrec1, hrec2, g1, g2, g3, g4, g5, g6, g7, g8, g9, mul_zero, sub_zero,
        add_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left h2
  · obtain ⟨n, hn | hn⟩ := Int.even_or_odd' b
    · subst hm; subst hn
      have hc := cert_oe (W := W) h1 m n
      have g1 : rel W m (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g2 : rel W m n 1 0 = 0 := ihAll _ _ (by omega)
      have g3 : rel W m (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g4 : rel W (m + 1) (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g5 : rel W (m + 1) n 1 0 = 0 := ihAll _ _ (by omega)
      have g6 : rel W (m + 1) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g7 : rel W (m + n) (m - n) 1 0 = 0 := ihAll _ _ (by omega)
      have g8 : rel W (m + n + 1) (m - n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      simp only [hrec1, g1, g2, g3, g4, g5, g6, g7, g8, mul_zero, sub_zero, add_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left h2
    · subst hm; subst hn
      have hc := cert_oo (W := W) h1 m n
      have g1 : rel W (m - 1) n 1 0 = 0 := ihAll _ _ (by omega)
      have g2 : rel W (m - 1) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g3 : rel W m (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g4 : rel W m n 1 0 = 0 := ihAll _ _ (by omega)
      have g5 : rel W m (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g6 : rel W m (n + 2) 1 0 = 0 := ihAll _ _ (by omega)
      have g7 : rel W (m + 1) (n - 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g8 : rel W (m + 1) n 1 0 = 0 := ihAll _ _ (by omega)
      have g9 : rel W (m + 1) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      have g10 : rel W (m + 1) (n + 2) 1 0 = 0 := ihAll _ _ (by omega)
      have g11 : rel W (m + 2) n 1 0 = 0 := ihAll _ _ (by omega)
      have g12 : rel W (m + 2) (n + 1) 1 0 = 0 := ihAll _ _ (by omega)
      simp only [hrec1, hrec2, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, mul_zero,
        sub_zero, add_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ h2)

end IsEllipticNet

namespace WeierstrassCurve

open MvPolynomial

/-- `normEDS X₀ X₁ X₂ 2 = X₀ ≠ 0` in `UnivEDS`: the multiplier the certificates carry is cancellable
there, which is the whole reason the induction is run over the universal ring. -/
private lemma normEDS_univ_two_ne_zero : normEDS (X 0 : UnivEDS) (X 1) (X 2) 2 ≠ 0 := by simp

/-- **Ward's `r = 1` addition formula over the universal ring `UnivEDS = ℤ[X₀, X₁, X₂]`,
unconditionally.** -/
theorem normEDS_rel_one_univ (p q : ℤ) :
    IsEllipticNet.rel (normEDS (X 0 : UnivEDS) (X 1) (X 2)) p q 1 0 = 0 :=
  IsEllipticNet.rel_one_of_rec (normEDS_odd_fun (X 0 : UnivEDS) (X 1) (X 2))
    (normEDS_zero (X 0 : UnivEDS) (X 1) (X 2)) (normEDS_one (X 0 : UnivEDS) (X 1) (X 2))
    normEDS_univ_two_ne_zero (normEDS_rel_odd (X 0 : UnivEDS) (X 1) (X 2))
    (normEDS_rel_even (X 0 : UnivEDS) (X 1) (X 2)) normEDS_rel_one_univ_diag p q

/-- **`WardGapCore` holds.** The gap `≥ 3` core isolated by
`EllipticCurves.Torsion.WardR1Core` is discharged; every statement in that file conditional on it
is therefore unconditional, and the versions below are those statements with the hypothesis fed
in. -/
theorem wardGapCore : WardGapCore := fun a b _ _ => normEDS_rel_one_univ (a : ℤ) (b : ℤ)

section Transfer

variable {R : Type*} [CommRing R] (b c d : R)

/-- **Ward's `r = 1` addition formula over an arbitrary `CommRing`, unconditionally.** -/
theorem normEDS_rel_one (p q : ℤ) : IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0 :=
  normEDS_rel_one_of_gapCore b c d wardGapCore p q

/-- **`normEDS b c d` is an elliptic sequence**, at every `r`, over an arbitrary `CommRing`. This is
the `IsEllipticSequence` half of Mathlib's `IsEllipticDvdSequence` `TODO`; the `IsDvdSequence` half
is not proved here. -/
theorem normEDS_isEllipticSequence : IsEllipticSequence (normEDS b c d) :=
  normEDS_isEllipticSequence_of_gapCore b c d wardGapCore

/-- **`normEDS b c d` is an elliptic net**: `rel (normEDS b c d) p q r s = 0` at every `s`, not only
at `s = 0`.  The `s ≠ 0` layer is `EllipticCurves.Torsion.EllipticNetSlices`, which shows it is not
additional content once the `s = 0` layer is available. -/
theorem normEDS_isEllipticNet : IsEllipticNet (normEDS b c d) :=
  normEDS_isEllipticNet_of_gapCore b c d wardGapCore

end Transfer

namespace Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- Ward's `r = 1` addition formula for the division polynomials `W.ψ`, in `R[X][Y]`. -/
theorem ψ_rel_one (p q : ℤ) : IsEllipticNet.rel W.ψ p q 1 0 = 0 :=
  ψ_rel_one_of_gapCore W wardGapCore p q

/-- **The division polynomials of a Weierstrass curve form an elliptic sequence.** -/
theorem ψ_isEllipticSequence : IsEllipticSequence W.ψ :=
  ψ_isEllipticSequence_of_gapCore W wardGapCore

/-- **The division polynomials of a Weierstrass curve form an elliptic net**, at every `s`. -/
theorem ψ_isEllipticNet : IsEllipticNet W.ψ :=
  ψ_isEllipticNet_of_gapCore W wardGapCore

variable {x y : R}

/-- Ward's `r = 1` addition formula among the point-values `n ↦ ψₙ(x, y)`. -/
theorem ψ_rel_one_evalEval (p q : ℤ) :
    IsEllipticNet.rel (fun n ↦ (W.ψ n).evalEval x y) p q 1 0 = 0 :=
  ψ_rel_one_evalEval_of_gapCore W wardGapCore p q

/-- **The point-values of the division polynomials form an elliptic sequence.** -/
theorem ψ_isEllipticSequence_evalEval :
    IsEllipticSequence (fun n ↦ (W.ψ n).evalEval x y) :=
  ψ_isEllipticSequence_evalEval_of_gapCore W wardGapCore

/-- **The point-values of the division polynomials form an elliptic net**, at every `s`. -/
theorem ψ_isEllipticNet_evalEval : IsEllipticNet (fun n ↦ (W.ψ n).evalEval x y) :=
  ψ_isEllipticNet_evalEval_of_gapCore W wardGapCore

end Affine

end WeierstrassCurve
