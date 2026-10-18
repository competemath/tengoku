/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Finite
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `3`-torsion subgroup `E[3]`

For a Weierstrass curve `W : Affine F` over a field `F`, this file identifies the `3`-torsion
points of `W` as the points lying above the roots of the `3`-division polynomial
`Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and deduces — away from characteristic `3` — that `E[3]` is
finite with

```
Nat.card (W.torsion 3) ≤ 9.
```

This is the `n = 3` instance of the bound `#E[n] ≤ n²` (Silverman, *AEC*, III.6, Corollary 6.4).
Like the `n = 2` computation, it is **independent of the elliptic-net recurrence and of the
multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**: for `n = 3` the whole content
is the tangent-line doubling formula, available in closed form in Mathlib.  ⚠️ The independence
claim is unchanged; only its trailing *"which gate the general case"* was dropped, because the
coordinate formula is now proved at every index with `(2 : F) ≠ 0`
(`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`).

## The mechanism

A point `P` is killed by `3` exactly when `P + P = -P`. For an affine point `P = (x, y)`:

* if `y = W.negY x y` then `P + P = 0`, hence `3 • P = P ≠ 0`; so a nonzero `3`-torsion point
  automatically satisfies `y ≠ W.negY x y`, i.e. `2y + a₁x + a₃ ≠ 0`
  (`ne_negY_of_mem_torsion_three`);
* otherwise `P + P` is computed by the tangent-line formula with slope
  `ℓ = W.slope x x y y = (3x² + 2a₂x + a₄ - a₁y) / (2y + a₁x + a₃)`, and `-P = (x, W.negY x y)`, so
  `P + P = -P` is equivalent to `W.addX x x ℓ = x` — the converse implication using Mathlib's
  `Point.X_eq_iff`, since the alternative `P + P = P` would force `P = 0`.

The bridge to `Ψ₃` is the algebraic identity `Ψ₃_eval_eq_neg` below: writing
`N = 3x² + 2a₂x + a₄ - a₁y` and `d = 2y + a₁x + a₃`, the Weierstrass equation at `(x, y)` gives

```
N² + a₁ N d - (a₂ + 3x) d² = -W.Ψ₃.eval x,
```

and since `ℓ = N / d` and `W.addX x x ℓ - x = ℓ² + a₁ℓ - a₂ - 3x` this says precisely

```
W.addX x x (W.slope x x y y) - x = -W.Ψ₃.eval x / (2y + a₁x + a₃) ^ 2       (`addX_self_sub`),
```

whence `W.addX x x ℓ = x ↔ W.Ψ₃.eval x = 0` (`addX_self_eq_iff`).

For the count, `Ψ₃` has degree at most `4` and is nonzero as soon as `(3 : F) ≠ 0`, so it has at
most four roots; the counting engine `ncard_le_of_xCoords` of `EllipticCurves.Torsion.Finite` — at
most two points above each `x`, plus the point at infinity — turns this into `#E[3] ≤ 2 * 4 + 1`.

The *sharp* count `#E[3] = 9` and the structure `E[3] ≃+ ZMod 3 × ZMod 3` need `Ψ₃` to have four
**distinct** roots, i.e. the discriminant of a quartic, and are not proved here.

## Main statements

* `WeierstrassCurve.Affine.Ψ₃_eval_eq_neg`: the algebraic identity displayed above.
* `WeierstrassCurve.Affine.addX_self_eq_iff`: `W.addX x x (W.slope x x y y) = x ↔ W.Ψ₃.eval x = 0`.
* `WeierstrassCurve.Affine.mem_torsion_three_some_iff`: `(x, y) ∈ E[3] ↔ W.Ψ₃.eval x = 0`, for an
  affine point with `y ≠ W.negY x y`.
* `WeierstrassCurve.Affine.Ψ₃_eval_eq_zero_of_mem_torsion_three`: the unconditional forward half.
* `WeierstrassCurve.Affine.finite_torsion_three`, `WeierstrassCurve.Affine.card_torsion_three_le`:
  `E[3]` is finite with at most `9` elements, away from characteristic `3`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 (the description of the
  torsion points by the division polynomials) and III.6, Corollary 6.4.
-/

open Polynomial

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `3`-division polynomial and the tangent at a point -/

/-- **The algebraic heart of the `3`-torsion description.** At a point `(x, y)` of `W`, the
numerator and denominator `N = 3x² + 2a₂x + a₄ - a₁y` and `d = 2y + a₁x + a₃` of the tangent slope
satisfy `N² + a₁ N d - (a₂ + 3x) d² = -Ψ₃(x)`.

The left-hand side is `(ℓ² + a₁ℓ - a₂ - 3x) d²` for `ℓ = N / d`, i.e. `d²` times the defect of
`W.addX x x ℓ = x`; see `addX_self_sub`. -/
lemma Ψ₃_eval_eq_neg {x y : F} (h : W.Equation x y) :
    (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
        + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
        - (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = -W.Ψ₃.eval x := by
  rw [equation_iff'] at h
  simp only [Ψ₃, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  linear_combination (-(W.a₁ ^ 2 + 4 * W.a₂) - 12 * x) * h

/-- A point is fixed by negation exactly when the `2`-division polynomial `2y + a₁x + a₃` vanishes
at it; so `y ≠ W.negY x y` is the nonvanishing of the tangent denominator. -/
lemma two_mul_add_ne_zero_of_Y_ne {x y : F} (hy : y ≠ W.negY x y) :
    2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
  rw [negY] at hy
  intro hd
  exact hy (by linear_combination hd)

/-! ## The roots of the `3`-division polynomial -/

variable (W) in
/-- Away from characteristic `3` the quartic `Ψ₃` is nonzero, so its root set is finite. -/
lemma finite_setOf_Ψ₃_root (h3 : (3 : F) ≠ 0) : {x : F | W.Ψ₃.eval x = 0}.Finite :=
  Polynomial.finite_setOfPred_isRoot (W.Ψ₃_ne_zero h3)

variable (W) in
/-- Away from characteristic `3` the quartic `Ψ₃` has at most four roots. -/
lemma ncard_setOf_Ψ₃_root_le (h3 : (3 : F) ≠ 0) : {x : F | W.Ψ₃.eval x = 0}.ncard ≤ 4 := by
  classical
  have hne : W.Ψ₃ ≠ 0 := W.Ψ₃_ne_zero h3
  have hset : {x : F | W.Ψ₃.eval x = 0} = ↑W.Ψ₃.roots.toFinset := by
    ext x
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hne, IsRoot]
  rw [hset, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans W.natDegree_Ψ₃_le)

variable [DecidableEq F]

/-- The tangent slope at `(x, y)`, cleared of its denominator. -/
lemma slope_self_mul {x y : F} (hy : y ≠ W.negY x y) :
    W.slope x x y y * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
  rw [slope_of_Y_ne rfl hy, div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hy), negY]
  ring

/-- The defect of the doubling identity `x(2P) = x(P)` at an affine point `P = (x, y)` with
`y ≠ W.negY x y`: it is `-Ψ₃(x)` divided by the square of `2y + a₁x + a₃`. -/
lemma addX_self_sub {x y : F} (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) - x = -W.Ψ₃.eval x / (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 (two_mul_add_ne_zero_of_Y_ne hy)), addX]
  linear_combination Ψ₃_eval_eq_neg h + (W.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
    + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * slope_self_mul hy

/-- **The doubling criterion.** For an affine point `(x, y)` of `W` not fixed by negation, the
`x`-coordinate of `2 • (x, y)` equals `x` exactly when `x` is a root of `Ψ₃`. -/
lemma addX_self_eq_iff {x y : F} (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) = x ↔ W.Ψ₃.eval x = 0 := by
  rw [← sub_eq_zero, addX_self_sub h hy, div_eq_zero_iff, neg_eq_zero]
  simp [pow_eq_zero_iff, two_mul_add_ne_zero_of_Y_ne hy]

/-! ## The `3`-torsion subgroup -/

/-- A point is killed by `3` exactly when doubling it gives its negative.

⚠️ As at `n = 2`, this is not the normal form the `FunctionField/` consumers take as a hypothesis
binder; that is `P ⊕ P ⊕ P = O`, i.e. `add_add_self_eq_zero_of_mem_torsion_three`
(`EllipticCurves.Torsion.Defs`). -/
lemma mem_torsion_three_iff_add_self_eq_neg {P : W.Point} : P ∈ W.torsion 3 ↔ P + P = -P := by
  rw [mem_torsion_iff, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul,
    add_eq_zero_iff_eq_neg]

/-- A nonzero `3`-torsion point is never fixed by negation: if it were, doubling would already kill
it, so `3 • P = P`, forcing `P = 0`. -/
lemma ne_negY_of_mem_torsion_three {x y : F} {h : W.Nonsingular x y}
    (hP : Point.some x y h ∈ W.torsion 3) : y ≠ W.negY x y := by
  intro hy
  refine Point.some_ne_zero h ?_
  have h3 := mem_torsion_three_iff_add_self_eq_neg.mp hP
  rw [Point.add_self_of_Y_eq hy] at h3
  rw [← neg_eq_zero, ← h3]

/-- **The `3`-torsion points are the points above the roots of `Ψ₃`.** An affine point `(x, y)` not
fixed by negation is `3`-torsion exactly when `x` is a root of the `3`-division polynomial. -/
lemma mem_torsion_three_some_iff {x y : F} {h : W.Nonsingular x y} (hy : y ≠ W.negY x y) :
    Point.some x y h ∈ W.torsion 3 ↔ W.Ψ₃.eval x = 0 := by
  rw [mem_torsion_three_iff_add_self_eq_neg, Point.add_self_of_Y_ne hy, Point.neg_some]
  constructor
  · intro hc
    rw [Point.some.injEq] at hc
    exact (addX_self_eq_iff h.left hy).mp hc.left
  · intro hx
    rcases Point.X_eq_iff.mp ((addX_self_eq_iff h.left hy).mpr hx) with hc | hc
    · refine absurd ?_ (Point.some_ne_zero h)
      have hPP : (Point.some x y h : W.Point) + Point.some x y h = Point.some x y h := by
        rw [Point.add_self_of_Y_ne hy]; exact hc
      exact add_right_cancel (hPP.trans (zero_add _).symm)
    · rw [hc, Point.neg_some]

/-- The `x`-coordinate of a nonzero `3`-torsion point is a root of `Ψ₃`. -/
lemma Ψ₃_eval_eq_zero_of_mem_torsion_three {x y : F} {h : W.Nonsingular x y}
    (hP : Point.some x y h ∈ W.torsion 3) : W.Ψ₃.eval x = 0 :=
  (mem_torsion_three_some_iff (ne_negY_of_mem_torsion_three hP)).mp hP

/-! ## Finiteness and the bound `#E[3] ≤ 9` -/

variable (W) in
/-- Away from characteristic `3` the `3`-torsion subgroup is finite. -/
lemma finite_torsion_three (h3 : (3 : F) ≠ 0) : Finite (W.torsion 3) :=
  W.finite_torsion_of_xCoords (W.finite_setOf_Ψ₃_root h3)
    fun _ _ _ hP => Ψ₃_eval_eq_zero_of_mem_torsion_three hP

variable (W) in
/-- **`#E[3] ≤ 9`** away from characteristic `3`: the `3`-torsion points lie above the at most four
roots of `Ψ₃`, with at most two points above each, plus the point at infinity.

This is the `n = 3` instance of the bound `#E[n] ≤ n²` (Silverman, *AEC*, III.6, Corollary 6.4),
proved here without the multiplication-by-`n` coordinate formula. -/
theorem card_torsion_three_le (h3 : (3 : F) ≠ 0) : Nat.card (W.torsion 3) ≤ 9 :=
  (W.card_torsion_le_of_xCoords (W.finite_setOf_Ψ₃_root h3)
      fun _ _ _ hP => Ψ₃_eval_eq_zero_of_mem_torsion_three hP).trans <| by
    have := W.ncard_setOf_Ψ₃_root_le h3
    omega

end WeierstrassCurve.Affine
