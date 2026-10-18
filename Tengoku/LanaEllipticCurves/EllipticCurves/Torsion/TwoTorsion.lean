/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Fixtures
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.AbelianStructure
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.DivisionPolynomialEval
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Finite
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `2`-torsion subgroup `E[2]`

For an elliptic curve `W : Affine F` over a field `F` of characteristic `≠ 2` **over which the
`2`-torsion cubic `Ψ₂Sq` splits**, this file computes the `2`-torsion subgroup completely:

```
Nat.card (W.torsion 2) = 4        and        W.torsion 2 ≃+ ZMod 2 × ZMod 2.
```

An algebraically closed field is the special case in which the splitting hypothesis is free, and
the `_of_splits` forms below are stated first for exactly that reason: the closure was never used
for anything else here (see `card_roots_Ψ₂Sq_of_splits`), and a field such as `ℚ` over which a
*named* curve has split `2`-torsion is enough.  The `Nonvacuity` section at the end certifies both
conclusions over `ℚ`, with no hypothesis at all, on `y² = x(x + 1)(x + 4)`.

This is the `n = 2` instance of the structure theorem `E[n] ≅ (ℤ/nℤ)²`
(Silverman, *AEC*, III.6, Corollary 6.4), and the first actual computation of a torsion group in
this development. Unlike the general case it is **independent of the elliptic-net recurrence and of
the multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**: for `n = 2` everything
reduces to the fact that the Weierstrass equation is quadratic in `y`, together with the
discriminant of a cubic.

## The mechanism

A point `P` is killed by `2` exactly when `P = -P`. For an affine point `P = (x, y)` negation acts
by `y ↦ negY x y = -y - a₁x - a₃`, so

```
2 • P = 0  ↔  2y + a₁x + a₃ = 0  ↔  ψ₂(x, y) = 0.
```

Mathlib's congruence `ψ₂² ≡ Ψ₂Sq (mod W)` — transported to an honest identity at a point of `W` by
`WeierstrassCurve.Affine.ψ_sq_evalEval` — turns this into the pointwise identity

```
W.Ψ₂Sq.eval x = (2y + a₁x + a₃) ^ 2                for every `(x, y)` on `W`,
```

recorded below as `Ψ₂Sq_eval_eq_sq`. Consequently:

* a nonzero `2`-torsion point has an `x`-coordinate which is a root of the cubic `Ψ₂Sq`;
* conversely, if `(2 : F) ≠ 0` and `x` is a root of `Ψ₂Sq`, then the *unique* candidate
  `y = -(a₁x + a₃)/2` (`twoTorsionY`) already satisfies the Weierstrass equation, because the
  displayed identity forces `4 · W.polynomial.evalEval x y = 0`.

So `E[2]` is the point at infinity together with the roots of `Ψ₂Sq` (`torsionTwoEquiv`). Since
`Ψ₂Sq` is Mathlib's `twoTorsionPolynomial`, a cubic with leading coefficient `4` and discriminant
`16Δ`, over an algebraically closed field of characteristic `≠ 2` it has exactly three distinct
roots, whence `#E[2] = 1 + 3 = 4`.

The group structure then follows from the finite-abelian-group classification core
`AddCommGroup.equiv_zmod_sq_of_card_sq` of `EllipticCurves.Torsion.AbelianStructure`.

## Main definitions

* `WeierstrassCurve.Affine.twoTorsionY`: the `y`-coordinate `-(a₁x + a₃)/2` of the unique point of
  `W` above `x` that is fixed by negation.
* `WeierstrassCurve.Affine.torsionTwoOfRoot`: the `2`-torsion point attached to a root of `Ψ₂Sq`,
  with `none` sent to the point at infinity.
* `WeierstrassCurve.Affine.torsionTwoEquiv`: the bijection
  `E[2] ≃ Option {x // W.Ψ₂Sq.eval x = 0}`.

## Main statements

* `WeierstrassCurve.Affine.Ψ₂Sq_eval_eq_sq`: `W.Ψ₂Sq.eval x = (2y + a₁x + a₃)²` at a point of `W`.
* `WeierstrassCurve.Affine.mem_torsion_two_some_iff`: `(x, y) ∈ E[2] ↔ 2y + a₁x + a₃ = 0`.
* `WeierstrassCurve.Affine.card_roots_Ψ₂Sq_of_splits`: the cubic `Ψ₂Sq` has exactly three roots
  over any field of characteristic `≠ 2` over which it splits;
  `WeierstrassCurve.Affine.card_roots_Ψ₂Sq` is the algebraically closed case, and
  `WeierstrassCurve.Affine.card_roots_Ψ₂Sq_le` is the inequality `≤ 3`, valid unconditionally.
* `WeierstrassCurve.Affine.card_torsion_two_le`: `#E[2] ≤ 4` over any field of characteristic `≠ 2`.
* `WeierstrassCurve.Affine.card_torsion_two_of_splits`: `#E[2] = 4` whenever `Ψ₂Sq` splits;
  `WeierstrassCurve.Affine.card_torsion_two` is the algebraically closed case.
* `WeierstrassCurve.Affine.nonempty_torsionTwo_addEquiv_of_splits`: `E[2] ≃+ ZMod 2 × ZMod 2`
  whenever `Ψ₂Sq` splits; `WeierstrassCurve.Affine.nonempty_torsionTwo_addEquiv` is the
  algebraically closed case.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 (the description of `E[2]`
  by the roots of the `2`-division polynomial) and III.6, Corollary 6.4.
-/

open Polynomial

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

private lemma four_ne_zero_of_two_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

variable {F : Type*} [Field F] {W : Affine F}

/-! ## The `2`-division polynomial at a point -/

/-- The square of the `2`-division polynomial at a point `(x, y)` of `W` is the value at `x` of the
univariate cubic `Ψ₂Sq`: `W.Ψ₂Sq.eval x = (2y + a₁x + a₃)²`.

This is the `n = 2` case of `WeierstrassCurve.Affine.ψ_sq_evalEval`, and it is the sole input to
the description of `E[2]` by the roots of `Ψ₂Sq`. -/
lemma Ψ₂Sq_eval_eq_sq {x y : F} (h : W.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [← ΨSq_two, ← ψ_sq_evalEval h 2, ψ_two_evalEval]

/-- **The converse construction.** Away from characteristic `2`, a root `x` of `Ψ₂Sq` together with
the unique `y` satisfying `2y + a₁x + a₃ = 0` gives a point of `W`: multiplying the Weierstrass
equation by `4` turns it into `(2y + a₁x + a₃)² - W.Ψ₂Sq.eval x = 0`. -/
lemma equation_of_Ψ₂Sq_eval_eq_zero (h2 : (2 : F) ≠ 0) {x y : F}
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) (hx : W.Ψ₂Sq.eval x = 0) : W.Equation x y := by
  have h4 : (4 : F) ≠ 0 := four_ne_zero_of_two_ne_zero h2
  rw [equation_iff']
  apply mul_left_cancel₀ h4
  rw [mul_zero]
  simp only [Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx
  linear_combination (2 * y + W.a₁ * x + W.a₃) * hy - hx

variable (W) in
/-- The `y`-coordinate `-(a₁x + a₃)/2` of the unique point of `W` above `x` fixed by negation.

Away from characteristic `2` this is the only possible `y`-coordinate of a `2`-torsion point with
`x`-coordinate `x`. -/
def twoTorsionY (x : F) : F :=
  -(W.a₁ * x + W.a₃) / 2

/-- The defining property of `twoTorsionY`: it is the unique root of `2y + a₁x + a₃`. -/
lemma two_mul_twoTorsionY_add (h2 : (2 : F) ≠ 0) (x : F) :
    2 * W.twoTorsionY x + W.a₁ * x + W.a₃ = 0 := by
  rw [twoTorsionY]
  field_simp
  ring

/-- Above a root of `Ψ₂Sq`, the point `(x, twoTorsionY x)` lies on `W`. -/
lemma equation_twoTorsionY (h2 : (2 : F) ≠ 0) {x : F} (hx : W.Ψ₂Sq.eval x = 0) :
    W.Equation x (W.twoTorsionY x) :=
  equation_of_Ψ₂Sq_eval_eq_zero h2 (two_mul_twoTorsionY_add h2 x) hx

/-- On an elliptic curve every point of the Weierstrass equation is nonsingular, so above a root of
`Ψ₂Sq` the point `(x, twoTorsionY x)` is a genuine point of `W.Point`. -/
lemma nonsingular_twoTorsionY [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₂Sq.eval x = 0) : W.Nonsingular x (W.twoTorsionY x) :=
  equation_iff_nonsingular.mp (equation_twoTorsionY h2 hx)

/-! ## The roots of the `2`-torsion cubic -/

/-- The leading coefficient of the `2`-torsion cubic is `4`, nonzero away from characteristic `2`.
-/
lemma twoTorsionPolynomial_a_ne_zero (h2 : (2 : F) ≠ 0) : W.twoTorsionPolynomial.a ≠ 0 := by
  rw [twoTorsionPolynomial, show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

variable (W) in
/-- The roots of `Ψ₂Sq`, as a subtype, are exactly the members of its root finset. -/
def rootsEquiv [DecidableEq F] (h2 : (2 : F) ≠ 0) :
    {x : F // W.Ψ₂Sq.eval x = 0} ≃ {x : F // x ∈ W.Ψ₂Sq.roots.toFinset} :=
  Equiv.subtypeEquivRight fun x => by
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (W.Ψ₂Sq_ne_zero (four_ne_zero_of_two_ne_zero h2))]
    exact Iff.rfl

/-- Away from characteristic `2` the cubic `Ψ₂Sq` is nonzero, so its root set is finite. -/
lemma finite_roots_Ψ₂Sq (h2 : (2 : F) ≠ 0) : Finite {x : F // W.Ψ₂Sq.eval x = 0} := by
  classical
  exact Finite.of_equiv _ (W.rootsEquiv h2).symm

/-- The cubic `Ψ₂Sq` has at most three roots over any field of characteristic `≠ 2`. -/
lemma card_roots_Ψ₂Sq_le (h2 : (2 : F) ≠ 0) :
    Nat.card {x : F // W.Ψ₂Sq.eval x = 0} ≤ 3 := by
  classical
  haveI := W.finite_roots_Ψ₂Sq h2
  rw [Nat.card_congr (W.rootsEquiv h2), Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans W.natDegree_Ψ₂Sq_le)

/-- **The `2`-torsion cubic has exactly three roots** over any field of characteristic `≠ 2` over
which it *splits*: it is a cubic with leading coefficient `4` and discriminant `16Δ`, both units
for an elliptic curve away from characteristic `2`, so it has no repeated root.

⚠️ The splitting hypothesis is the **only** thing the algebraically closed form `card_roots_Ψ₂Sq`
below ever used its closure for: `twoTorsionPolynomial_a_ne_zero` needs only `h2`,
`twoTorsionPolynomial_discr_ne_zero_of_isElliptic` needs only `[W.IsElliptic]`, and Mathlib's
`Cubic.card_roots_of_discr_ne_zero` takes `Splits` as a hypothesis rather than deriving it. -/
lemma card_roots_Ψ₂Sq_of_splits [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hsplits : W.Ψ₂Sq.Splits) :
    Nat.card {x : F // W.Ψ₂Sq.eval x = 0} = 3 := by
  classical
  have ha : W.twoTorsionPolynomial.a ≠ 0 := W.twoTorsionPolynomial_a_ne_zero h2
  have hd : W.twoTorsionPolynomial.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic h2.isUnit
  have hsplits' : (W.twoTorsionPolynomial.toPoly.map (RingHom.id F)).Splits := by
    rw [Polynomial.map_id, ← Ψ₂Sq_eq]
    exact hsplits
  have hcard := Cubic.card_roots_of_discr_ne_zero (φ := RingHom.id F) ha hsplits' hd
  have hmap : Cubic.map (RingHom.id F) W.twoTorsionPolynomial = W.twoTorsionPolynomial := rfl
  rw [hmap, Cubic.roots, ← Ψ₂Sq_eq] at hcard
  rw [Nat.card_congr (W.rootsEquiv h2), Nat.card_eq_fintype_card, Fintype.card_coe]
  exact hcard

/-- **The `2`-torsion cubic has exactly three roots** over an algebraically closed field of
characteristic `≠ 2`: it is a cubic with leading coefficient `4` and discriminant `16Δ`, both units
for an elliptic curve away from characteristic `2`.

The splitting hypothesis of `card_roots_Ψ₂Sq_of_splits`, discharged by `IsAlgClosed.splits`. -/
lemma card_roots_Ψ₂Sq [W.IsElliptic] [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Nat.card {x : F // W.Ψ₂Sq.eval x = 0} = 3 :=
  card_roots_Ψ₂Sq_of_splits h2 (IsAlgClosed.splits _)

/-! ## The `2`-torsion subgroup -/

section Torsion

variable [DecidableEq F]

/-- A point is killed by `2` exactly when it is fixed by negation.

⚠️ This is one of two normal forms for `E[2]` membership and **not** the one the `FunctionField/`
consumers want: they take `P ⊕ P = O` as a hypothesis binder, which is
`add_self_eq_zero_of_mem_torsion_two` (`EllipticCurves.Torsion.Defs`).  Reaching that form from
this one costs an extra `add_eq_zero_iff_eq_neg`, which is why three files once carried private
copies of it instead. -/
lemma mem_torsion_two_iff_eq_neg {P : W.Point} : P ∈ W.torsion 2 ↔ P = -P := by
  rw [mem_torsion_iff, two_nsmul, add_eq_zero_iff_eq_neg]

/-- An affine point `(x, y)` is `2`-torsion exactly when the `2`-division polynomial
`ψ₂ = 2y + a₁x + a₃` vanishes at it. -/
lemma mem_torsion_two_some_iff {x y : F} (h : W.Nonsingular x y) :
    Point.some x y h ∈ W.torsion 2 ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [mem_torsion_two_iff_eq_neg, Point.neg_some, Point.some.injEq]
  simp only [negY, true_and]
  constructor <;> intro hy <;> linear_combination hy

/-- The `y`-coordinate of an affine `2`-torsion point is forced: it is `twoTorsionY x`. -/
lemma eq_twoTorsionY_of_mem_torsion_two (h2 : (2 : F) ≠ 0) {x y : F} {h : W.Nonsingular x y}
    (hP : Point.some x y h ∈ W.torsion 2) : y = W.twoTorsionY x := by
  have hy := (mem_torsion_two_some_iff h).mp hP
  rw [twoTorsionY, eq_div_iff h2]
  linear_combination hy

/-- The `x`-coordinate of an affine `2`-torsion point is a root of the cubic `Ψ₂Sq`. -/
lemma Ψ₂Sq_eval_eq_zero_of_mem_torsion_two {x y : F} {h : W.Nonsingular x y}
    (hP : Point.some x y h ∈ W.torsion 2) : W.Ψ₂Sq.eval x = 0 := by
  rw [Ψ₂Sq_eval_eq_sq h.1, (mem_torsion_two_some_iff h).mp hP]
  ring

variable [W.IsElliptic]

/-- The `2`-torsion point attached to a root of `Ψ₂Sq`, with `none` sent to the point at infinity.
-/
def torsionTwoOfRoot (h2 : (2 : F) ≠ 0) :
    Option {x : F // W.Ψ₂Sq.eval x = 0} → W.torsion 2
  | none => 0
  | some x => ⟨Point.some x (W.twoTorsionY x) (nonsingular_twoTorsionY h2 x.2),
      (mem_torsion_two_some_iff _).mpr (two_mul_twoTorsionY_add h2 x)⟩

lemma torsionTwoOfRoot_bijective (h2 : (2 : F) ≠ 0) :
    Function.Bijective (torsionTwoOfRoot (W := W) h2) := by
  constructor
  · rintro (_ | ⟨x₁, hx₁⟩) (_ | ⟨x₂, hx₂⟩) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
    · exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
    · have hx := congrArg Subtype.val hab
      rw [torsionTwoOfRoot, torsionTwoOfRoot, Point.some.injEq] at hx
      exact congrArg _ (Subtype.ext hx.1)
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨x, Ψ₂Sq_eval_eq_zero_of_mem_torsion_two hP⟩,
        Subtype.ext (by
          rw [torsionTwoOfRoot]
          simp only [Point.some.injEq]
          exact ⟨trivial, (eq_twoTorsionY_of_mem_torsion_two h2 hP).symm⟩)⟩

/-- **`E[2]` is the point at infinity together with the roots of `Ψ₂Sq`.** -/
noncomputable def torsionTwoEquiv (h2 : (2 : F) ≠ 0) :
    W.torsion 2 ≃ Option {x : F // W.Ψ₂Sq.eval x = 0} :=
  (Equiv.ofBijective _ (torsionTwoOfRoot_bijective h2)).symm

/-- Away from characteristic `2` the `2`-torsion subgroup of an elliptic curve is finite. -/
lemma finite_torsion_two (h2 : (2 : F) ≠ 0) : Finite (W.torsion 2) :=
  haveI := W.finite_roots_Ψ₂Sq h2
  Finite.of_equiv _ (torsionTwoEquiv h2).symm

/-- **`#E[2] ≤ 4`** for an elliptic curve over *any* field of characteristic `≠ 2`: the point at
infinity together with the at most three roots of the `2`-torsion cubic.

This is the inequality half of `card_torsion_two`, and unlike it needs no algebraic closure; it is
the `p = 2` base case of the multiplicative bound of `EllipticCurves.Torsion.Multiplicative`. -/
theorem card_torsion_two_le (h2 : (2 : F) ≠ 0) : Nat.card (W.torsion 2) ≤ 4 := by
  haveI := W.finite_roots_Ψ₂Sq h2
  rw [Nat.card_congr (torsionTwoEquiv h2), Finite.card_option]
  have := W.card_roots_Ψ₂Sq_le h2
  omega

/-- **`#E[2] = 4`** for an elliptic curve over *any* field of characteristic `≠ 2` over which the
`2`-torsion cubic **splits**: the point at infinity together with its three roots.

This is the finite-level form of `card_torsion_two`, and it is what a caller over a field that is
not algebraically closed wants — the hypothesis is a statement about one explicit cubic, and it is
checkable on a named curve.  ⚠️ Over a splitting field `L` of `Ψ₂Sq` it holds by construction, but
transporting the conclusion back down to `F` is a **descent** problem and is not this lemma's
business.

⚠️ Callers building a `ℚ` certificate should use this rather than exhibiting an injection
`Fin 4 → E[2]` by hand: `card_torsion_two_le` plus four named points proves the same thing, but the
splitting hypothesis is one polynomial identity instead of a case split over sixteen pairs. -/
theorem card_torsion_two_of_splits (h2 : (2 : F) ≠ 0) (hsplits : W.Ψ₂Sq.Splits) :
    Nat.card (W.torsion 2) = 4 := by
  haveI := W.finite_roots_Ψ₂Sq h2
  rw [Nat.card_congr (torsionTwoEquiv h2), Finite.card_option,
    card_roots_Ψ₂Sq_of_splits h2 hsplits]

/-- **`#E[2] = 4`** for an elliptic curve over an algebraically closed field of characteristic
`≠ 2`: the point at infinity together with the three roots of the `2`-torsion cubic.

The splitting hypothesis of `card_torsion_two_of_splits`, discharged by `IsAlgClosed.splits`. -/
theorem card_torsion_two [IsAlgClosed F] (h2 : (2 : F) ≠ 0) : Nat.card (W.torsion 2) = 4 :=
  card_torsion_two_of_splits h2 (IsAlgClosed.splits _)

/-- **The structure theorem for `E[2]`, over any field over which the `2`-torsion cubic splits.**
Away from characteristic `2`, the `2`-torsion subgroup of an elliptic curve is isomorphic to
`ℤ/2ℤ × ℤ/2ℤ` as soon as `Ψ₂Sq` splits — no algebraic closure is involved.

This is the `n = 2` instance of `E[n] ≅ (ℤ/nℤ)²`, obtained by feeding the count `#E[2] = 4` into
the finite-abelian-group classification core `AddCommGroup.equiv_zmod_sq_of_card_sq`. -/
theorem nonempty_torsionTwo_addEquiv_of_splits (h2 : (2 : F) ≠ 0) (hsplits : W.Ψ₂Sq.Splits) :
    Nonempty (W.torsion 2 ≃+ ZMod 2 × ZMod 2) := by
  haveI := W.finite_torsion_two h2
  have hcard : Nat.card (W.torsion 2) = 2 ^ 2 := by
    rw [card_torsion_two_of_splits h2 hsplits]
    norm_num
  refine AddCommGroup.equiv_zmod_sq_of_card_sq two_pos (fun a => nsmul_mem_torsion a) hcard ?_
  intro p hp
  calc Nat.card {a : W.torsion 2 // p • a = 0}
      ≤ Nat.card (W.torsion 2) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 ^ 2 := hcard
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2

/-- **The structure theorem for `E[2]`.** Over an algebraically closed field of characteristic
`≠ 2`, the `2`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/2ℤ × ℤ/2ℤ`.

The splitting hypothesis of `nonempty_torsionTwo_addEquiv_of_splits`, discharged by
`IsAlgClosed.splits`. -/
theorem nonempty_torsionTwo_addEquiv [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Nonempty (W.torsion 2 ≃+ ZMod 2 × ZMod 2) :=
  nonempty_torsionTwo_addEquiv_of_splits h2 (IsAlgClosed.splits _)

end Torsion

/-! ### Non-vacuity: the splitting hypothesis on a named curve over `ℚ`

⚠️ The certificate below **must** be over a field that is not algebraically closed, or it certifies
`card_torsion_two` instead of anything this file adds.

`y² = x³ + 5x² + 4x = x(x + 1)(x + 4)` over `ℚ`, i.e. `⟨0, 5, 0, 4, 0⟩`, has `b₂ = 20`, `b₄ = 8`,
`b₆ = 0` and `Δ = -b₂²b₈ - 8b₄³ = 6400 - 4096 = 2304 ≠ 0`, so it is elliptic; its `2`-torsion cubic
is `Ψ₂Sq = 4X³ + 20X² + 16X = 4·X·(X + 1)·(X + 4)`, which splits over `ℚ` by inspection.  So
`#E[2] = 4` and `E[2] ≃+ ZMod 2 × ZMod 2` hold over `ℚ` for this curve with **no hypothesis at
all**, and neither statement mentions an algebraic closure.

⚠️ **This is the block a `ℚ` certificate elsewhere should be able to replace itself by.**  The
alternative route to `#E[2] = 4` on a concrete curve — `card_torsion_two_le` for `≤ 4`, plus an
explicit `Fin 4 → W.torsion 2` and its injectivity for `≥ 4` — is correct but costs a case split
over sixteen pairs and four separate `Nonsingular`/`mem_torsion` obligations.  Here the whole
lower bound is one polynomial identity.

⚠️ The three roots must be **distinct** for the count to be `4`, and nothing in the `Splits`
hypothesis says so: it is the discriminant, i.e. `[W.IsElliptic]`, that rules out a repeated root,
inside `card_roots_Ψ₂Sq_of_splits`.  A singular Weierstrass curve with a split but repeated `Ψ₂Sq`
would have fewer than four `2`-torsion points, and this file would not see it. -/

section Nonvacuity

/-! The certificate curve is the shared `EllipticCurves.Fixture.y2EqX3Add5X2Add4X` at `R = ℚ`:
`y² = x³ + 5x² + 4x = x(x + 1)(x + 4)`, of discriminant `2304`.  ⚠️ **What this block tests is that
the cubic splits over `ℚ`** — its three roots `0`, `−1`, `−4` are distinct and rational, so all
three nontrivial `2`-torsion points are rational and `Splits` is discharged with no algebraic
closure anywhere.  Substituting a curve whose cubic is irreducible over `ℚ` would leave everything
below green and say nothing; the shared docstring records the same constraint, and the local lemma
names below were renamed to the fixture so that no name here points at a curve that is gone.

`(y2EqX3Add5X2Add4X ℚ).IsElliptic` comes from the single `[CharZero F]` instance in `Fixtures`. -/

open EllipticCurves.Fixture

end Nonvacuity

end WeierstrassCurve.Affine
