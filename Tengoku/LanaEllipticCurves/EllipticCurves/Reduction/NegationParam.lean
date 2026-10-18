/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.KernelSection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local parameter of a negated point: the affine formula for the formal inverse

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and `W : WeierstrassCurve K`
an elliptic curve with an integral model.  On `E₁(K)` (the points reducing to the origin) the local
parameter is `z(P) = -x/y`.  Negation on the affine curve fixes the `x`-coordinate and sends `y` to
`negY x y = -y - a₁x - a₃`, so it maps the pole branch to itself and

```
z(-P) = -x / negY x y.
```

Rewriting the recovered coordinates `x(z) = z/w(z)`, `y(z) = -1/w(z)` turns this into the **affine
formula for the formal inverse**

```
z(-P) = -z / (1 - a₁ z - a₃ w(z)),
```

the exact numeric analogue of the formal inverse series `i(T)` of the formal group (the denominator
`1 - a₁ z - a₃ w` is the formal-group `den` specialised to the negation line `w = z/x`).  This is
the coordinate groundwork for the **inverse case** of the additivity crux (issue #367): when
`Q = -P` the affine sum `P + Q` collapses to `O`, so `z(P + Q) = 0`, and closing the additivity
identity there amounts to matching this `z(-P)` against the formal negation `⊖ (z P)` in `Ê(𝔪)`.

## Main results

* `WeierstrassCurve.localParam_neg_some` — `z(-P) = -x / negY x y` on the pole branch.
* `WeierstrassCurve.wParam_mul_negY_xParam_yParam` —
  `w(z) · negY (x(z)) (y(z)) = 1 - a₁ z - a₃ w(z)`.
* `WeierstrassCurve.localParam_neg_pointOfParam` —
  `z(-(pointOfParam z)) = -z / (1 - a₁ z - a₃ w(z))`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The local parameter of `-P` -/

/-- **The local parameter of a negated point on the pole branch.**  Negation fixes the
`x`-coordinate, so `-P = (x, negY x y)` still has `1 < v x` and takes the genuine `-x/y` branch of
`localParam`, giving `z(-P) = -x / negY x y`.

⚠️ **This statement used to carry `[IsIntegral R W]` and it was dead** — the instance occurred in
neither the remainder of the type nor the proof term, measured on the elaborated environment at
`2e44940` (`#1272`).  `localParam` itself takes no integrality hypothesis, and the proof is
`Affine.Point.neg_some` followed by `localParam_some` and the `if_pos` on the same branch
condition.  ⚠️ The integral model is still what makes the *statement interesting* — it is where
`1 < v x` comes from in practice — and every other declaration in this file that mentions a
reduction keeps it. -/
theorem localParam_neg_some (W : WeierstrassCurve K)
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : 1 < valuation K (maximalIdeal R) x) :
    localParam R W (-(.some x y h)) = -x / W.toAffine.negY x y := by
  rw [Affine.Point.neg_some, localParam_some, ite_eq_left hx]

variable [IsAdicComplete (maximalIdeal R).asIdeal R]

/-! ### The affine formula for the formal inverse -/

/-- The negation denominator on the recovered coordinates: clearing the `w(z)` poles,
`w(z) · negY (x(z)) (y(z)) = 1 - a₁ z - a₃ w(z)`.  This is the numeric `den` of the formal group
specialised to the negation line. -/
theorem wParam_mul_negY_xParam_yParam (W : WeierstrassCurve K) [IsIntegral R W] {z : R}
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    algebraMap R K (wParam R W hz) *
        W.toAffine.negY (xParam R W hz) (yParam R W hz)
      = 1 - W.a₁ * algebraMap R K z - W.a₃ * algebraMap R K (wParam R W hz) := by
  have hwne : algebraMap R K (wParam R W hz) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz hz0)
  simp only [Affine.negY, xParam, yParam]
  field_simp

/-- **The affine formula for the formal inverse.**  The local parameter of the negation of the
recovered point `pointOfParam z` is `z(-P) = -z / (1 - a₁ z - a₃ w(z))`.  Combined with the
formal-group negation `⊖`, this is the coordinate input for the inverse case of the additivity crux
(issue #367). -/
theorem localParam_neg_pointOfParam (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    {z : R} (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0) :
    localParam R W (-(pointOfParam R W hz hz0))
      = -algebraMap R K z /
          (1 - W.a₁ * algebraMap R K z - W.a₃ * algebraMap R K (wParam R W hz)) := by
  rw [pointOfParam,
    localParam_neg_some R W _ (one_lt_valuation_xParam R W hz hz0),
    ← wParam_mul_negY_xParam_yParam R W hz hz0, xParam, neg_div, neg_div, div_div]

end WeierstrassCurve
