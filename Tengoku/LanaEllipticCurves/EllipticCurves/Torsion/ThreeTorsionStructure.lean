/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.ThreeTorsion
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.TwoTorsion
import Tengoku.Seed.Algebra.Polynomial.FieldDivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The structure of the `3`-torsion subgroup `E[3]`

`EllipticCurves.Torsion.ThreeTorsion` describes `E[3]` as the points lying above the roots of the
`3`-division polynomial `Ψ₃` and deduces `Finite (W.torsion 3)` and `#E[3] ≤ 9` over an arbitrary
field of characteristic `≠ 3`.  This file sharpens that bound to an equality and identifies the
group: for an elliptic curve `W : Affine F` over a field `F` of characteristic `≠ 2` and `≠ 3`
**over which `Ψ₃` splits and `Ψ₂Sq` takes a square value at each root of `Ψ₃`**,

```
Nat.card (W.torsion 3) = 9        and        W.torsion 3 ≃+ ZMod 3 × ZMod 3.
```

⚠️ **Those two conditions are exactly what the algebraic closure was being used for, and an
algebraically closed field is the special case in which both are free.**  The `_of_splits` forms
below carry them and the closed forms are their corollaries, which is the shape
`EllipticCurves.Torsion.TwoTorsion` already has at `n = 2`.

⚠️ **The two conditions are not one condition, and that is the difference from `n = 2`.**  At
`n = 2` a torsion point *is* its `x`-coordinate, so `card_torsion_two_of_splits` needs the
`2`-division cubic to split and nothing more.  At `n = 3` the description of `E[3]`
(`torsionThreeEquiv`) is a **sigma** over the roots of `Ψ₃` rather than an `Option` of them:
splitting `Ψ₃` fixes the base and says nothing about the fibres, each of which is a quadratic in
`y` of discriminant `Ψ₂Sq.eval x`.  So the second condition is about a **different polynomial** and
no amount of splitting `Ψ₃` supplies it.

This is the `n = 3` instance of the structure theorem `E[n] ≅ (ℤ/nℤ)²`
(Silverman, *AEC*, III.6, Corollary 6.4), the analogue for `n = 3` of the `n = 2` computation in
`EllipticCurves.Torsion.TwoTorsion`.  Like those files it is **independent of the elliptic-net
recurrence and of the multiplication-by-`n` coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`**.

## The two missing ingredients

Over an arbitrary field the description of `E[3]` in `ThreeTorsion` leaves two gaps, both closed
here.

**1. Each root of `Ψ₃` really does carry two `3`-torsion points.**  The `⇐` direction of
`mem_torsion_three_some_iff` carries the side condition `y ≠ W.negY x y`.  It is automatic:
writing `d = 2y + a₁x + a₃` and `n = 3x² + 2a₂x + a₄ - a₁y` for the values of `∂W/∂Y` and `-∂W/∂X`,
the doubling defect `Ψ₃_eval_eq_neg` says `n² + a₁nd - (a₂ + 3x)d² = -Ψ₃(x)`, so at a root of `Ψ₃`
with `d = 0` one gets `n = 0` too, and both partial derivatives of the Weierstrass polynomial would
vanish (`Y_ne_negY_of_Ψ₃_eval_eq_zero`).  Hence `Ψ₂Sq.eval x = d² ≠ 0`, the Weierstrass equation is
a *separable* quadratic in `y`, and it has exactly two roots as soon as that discriminant is a
**square** (`card_setOf_equation_eq_two_of_isSquare`) — free over an algebraically closed field
(`card_setOf_equation_eq_two`), and the second of this file's two conditions otherwise.  ⚠️ This is
the *only* place either statement below uses a square root, and it is the half with no `n = 2`
counterpart.

**2. `Ψ₃` is separable.**  Its formal derivative is `3Ψ₂Sq` (`derivative_Ψ₃`), so a repeated root
of `Ψ₃` would be a common root of `Ψ₃` and `Ψ₂Sq` — excluded by the previous paragraph, ⚠️ and
excluded there with **no algebraic closure at all** (`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`), since the
point above `x` that the argument consumes is `twoTorsionY` itself.  As `Ψ₃` has degree `4` away
from characteristic `3`, it has exactly four distinct roots as soon as it **splits**
(`card_roots_Ψ₃_of_splits`), hence over an algebraically closed field (`card_roots_Ψ₃`).  No
quartic discriminant is needed.

Combining, `E[3]` is the point at infinity together with two points above each of four roots, so
`#E[3] = 1 + 2 · 4 = 9`, and the group structure follows from the classification core
`AddCommGroup.equiv_zmod_sq_of_card_sq` of `EllipticCurves.Torsion.AbelianStructure`.  The rank
hypothesis of that core at the prime `2` is *not* automatic here (unlike in the `n = 2` case): it
uses instead that an element killed by both `2` and `3` is killed by `1`.

## Main definitions

* `WeierstrassCurve.Affine.torsionThreeOfPair`: the `3`-torsion point attached to a root of `Ψ₃`
  together with a `y`-coordinate above it, with `none` sent to the point at infinity.
* `WeierstrassCurve.Affine.torsionThreeEquiv`: the bijection
  `E[3] ≃ Option ((x : {x // W.Ψ₃.eval x = 0}) × {y // W.Equation x y})`.

## Main statements

* `WeierstrassCurve.Affine.Y_ne_negY_of_Ψ₃_eval_eq_zero`: above a root of `Ψ₃` no point of `W` is
  fixed by negation.
* `WeierstrassCurve.Affine.derivative_Ψ₃`: `Ψ₃' = 3 · Ψ₂Sq`.
* `WeierstrassCurve.Affine.exists_equation_of_isSquare`: a point of `W` lies above `x` as soon as
  `Ψ₂Sq.eval x` is a square, over any field of characteristic `≠ 2`;
  `WeierstrassCurve.Affine.exists_equation` is the algebraically closed case.
* `WeierstrassCurve.Affine.card_setOf_equation_eq_two_of_isSquare`: exactly two points lie above a
  value of `x` at which `Ψ₂Sq` is a nonzero square, over any field of characteristic `≠ 2`;
  `WeierstrassCurve.Affine.card_setOf_equation_eq_two` is the algebraically closed case.
* `WeierstrassCurve.Affine.Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`: a root of `Ψ₃` is not a root of `Ψ₂Sq`.
* `WeierstrassCurve.Affine.card_roots_Ψ₃_of_splits`: `Ψ₃` has exactly four roots over any field of
  characteristic `≠ 2, 3` over which it splits; `WeierstrassCurve.Affine.card_roots_Ψ₃` is the
  algebraically closed case.
* `WeierstrassCurve.Affine.card_torsion_three_of_splits`: `#E[3] = 9` under the two conditions;
  `WeierstrassCurve.Affine.card_torsion_three` is the algebraically closed case.
* `WeierstrassCurve.Affine.nonempty_torsionThree_addEquiv_of_splits`: `E[3] ≃+ ZMod 3 × ZMod 3`
  under the same two; `WeierstrassCurve.Affine.nonempty_torsionThree_addEquiv` is the algebraically
  closed case.

**The hypotheses the bullets omit.**  ⚠️ `Y_ne_negY_of_Ψ₃_eval_eq_zero` takes **neither**
`[W.IsElliptic]` nor a characteristic condition: what it takes is the point-level hypothesis
`(h : W.Nonsingular x y)`, and the nonsingularity of a point *above* `x` is what stands in there
for the discriminant.  `derivative_Ψ₃` takes nothing at all.  Every other bullet takes
`(2 : F) ≠ 0`; `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, `card_roots_Ψ₃_of_splits`, `card_roots_Ψ₃` and the
four statements about `W.torsion 3` take `[W.IsElliptic]` as well — the last four from
`section Count`'s `variable` line rather than from their own signatures; from
`card_roots_Ψ₃_of_splits` on there is additionally `(3 : F) ≠ 0`, and the four statements about
`W.torsion 3` take `[DecidableEq F]`.  The two conditions written out are
`hsplits : W.Ψ₃.Splits` and `hsq : ∀ x, W.Ψ₃.eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)`.

## What is *not* here

* ⚠️ **The `3`-division field.**  Nothing below constructs a field satisfying the two conditions,
  and — unlike at `n = 2` — no single polynomial's splitting field does: the second condition is
  about `Ψ₂Sq` at the roots of `Ψ₃`, so the field is `Ψ₃`'s splitting field followed by a tower of
  quadratics.  That is a strictly larger job than `EllipticCurves.Torsion.TwoTorsionSplittingField`
  was, and this file states no `IsGalois`, no `IsSplittingField` and no normal closure.  What is
  delivered here is the layer such a construction would consume, exactly as
  `card_torsion_two_of_splits` is the layer `TwoTorsionSplittingField` consumes.  ⚠️ **Partial
  rather than false, so the words stay and this pointer is added**: of the four clauses above,
  **three** carry a scope to this file in their own words — *"Nothing below"*, *"this file"* and
  *"delivered here"* — and the fourth, *"no single polynomial's splitting field does"*, is about
  the mathematics and not about the tree.  **All four are still true**, and the one a later landing
  could most cheaply have falsified is checkable in one pass: every occurrence of the three names in
  this file is inside this docstring, so **0** of the declarations from `Ψ₂Sq_eval` onward mentions
  any of them.  ⚠️ **The split is recorded here rather than left in a review** (`#2087`): a count
  of the scope-carrying clauses that reads **two** has dropped *"delivered here"*, which scopes to
  this file exactly as *"Nothing below"* does.  But the heading they sit under is read tree-wide
  (`#1982`), and the construction is
  no longer absent from the tree.  It is `EllipticCurves.Torsion.ThreeDivisionField`, which builds
  exactly the two-step tower described above — `threeDivisionField`, `Ψ₃`'s splitting field
  followed by the quadratic tower — and discharges both conditions at it, as
  `card_torsion_three_threeDivisionField` and `nonempty_torsionThree_addEquiv_threeDivisionField`,
  with `isSeparable_threeDivisionField` beside them and `isGalois_threeDivisionGaloisField` one
  construction further on — ⚠️ `isGalois_tower_top` is `IsGalois L₁ L₂` and says nothing about
  `L₂ / F`, which is the whole reason `threeDivisionGaloisField` exists.  ⚠️ **The three
  negatives are answered at two different commits and not at one, and in
  `ThreeDivisionField.lean` rather than here or tree-wide**: that file carried `IsGalois` and
  `IsSplittingField` from `44272f7` (`#2172`), which created it with **0** occurrences of
  `normalClosure` in it, and `normalClosure` only from `231becd` (`#2189`), as
  `threeDivisionGaloisField`.  ⚠️ **Tree-wide all three predate `44272f7`** — at its parent
  `EllipticCurves/*.lean` reads `IsGalois` **202** in 32 files, `IsSplittingField` **20** in 5 and
  `normalClosure` **13** in 1 — so those two shas date the file and not the tree.  ⚠️ **And
  *"the layer such a construction would consume"* is what this file turned out to be, checkably
  rather than rhetorically**: that file imports this one directly, and its proofs cite
  `card_torsion_three_of_splits`, `nonempty_torsionThree_addEquiv_of_splits`,
  `card_roots_Ψ₃_of_splits` and `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`.  `### Reach clauses`'
  *"false or merely partial"* test therefore returns **partial**, so `### Retired claims` does not
  bind and nothing here is quoted as retired.
* ⚠️ **A certificate over a field that is not algebraically closed**, and the reason is worth
  recording rather than leaving as an omission: the two conditions together say `E[3] ⊆ E(F)`, and
  the Weil pairing `e₃` is surjective and Galois-equivariant, so they **force `μ₃ ⊆ F`**.  Over `ℚ`
  they are therefore jointly unsatisfiable for every elliptic curve, and no rational fixture can
  certify the statements below the way `y2EqX3Add5X2Add4X` certifies their `n = 2` analogues.  ⚠️
  That argument is classical and is **not** formalised here; no statement below depends on it.  A
  certificate wants a base containing a primitive cube root of unity — `y² = x³ + 2` over `ZMod 7`
  satisfies both conditions, with `Ψ₃` splitting at `{0, 3, 5, 6}` and `Ψ₂Sq` taking the values
  `{1, 4, 4, 4}` there.  ⚠️ That base is not available in this module's import closure
  (`Field (ZMod 7)` is not synthesisable from it), and pulling a finite-field import into a module
  eight files import directly is the trade `EllipticCurves.Fixtures` rules against in terms, so the
  certificate belongs in its own module and is filed rather than shipped here.
* **`n = 2`.**  `EllipticCurves.Torsion.TwoTorsion` and
  `EllipticCurves.Torsion.TwoTorsionSplittingField` are untouched, and nothing below is stated at a
  general `n`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 (the `3`-torsion points as
  the inflection points of the cubic) and III.6, Corollary 6.4.
-/

open Polynomial

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## No `3`-torsion `x`-coordinate is fixed by negation -/

/-- The value of the `2`-division polynomial `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`. -/
lemma Ψ₂Sq_eval (x : F) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X]

/-- **Above a root of `Ψ₃` no point of `W` is fixed by negation.**  If `2y + a₁x + a₃` vanished at a
point above a root of `Ψ₃`, the doubling defect `Ψ₃_eval_eq_neg` would force
`3x² + 2a₂x + a₄ - a₁y = 0` as well, so both partial derivatives of the Weierstrass polynomial would
vanish, contradicting nonsingularity. -/
lemma Y_ne_negY_of_Ψ₃_eval_eq_zero {x y : F} (h : W.Nonsingular x y) (hx : W.Ψ₃.eval x = 0) :
    y ≠ W.negY x y := by
  intro hy
  have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    rw [negY] at hy
    linear_combination hy
  have key := Ψ₃_eval_eq_neg h.1
  rw [hx, hd, neg_zero] at key
  have hn : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination key)
  rcases h.2 with hX | hY
  · exact hX (by rw [evalEval_polynomialX]; linear_combination -hn)
  · exact hY (by rw [evalEval_polynomialY]; exact hd)

/-- A root of `Ψ₃` is never a root of `Ψ₂Sq`: the `2`- and `3`-torsion `x`-coordinates are
disjoint. -/
lemma Ψ₂Sq_eval_ne_zero_of_Ψ₃_eval_eq_zero {x y : F} (h : W.Nonsingular x y)
    (hx : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  rw [Ψ₂Sq_eval_eq_sq h.1]
  exact pow_ne_zero 2 (two_mul_add_ne_zero_of_Y_ne (Y_ne_negY_of_Ψ₃_eval_eq_zero h hx))

/-- **The side-condition-free membership criterion.**  An affine point of an elliptic curve is
`3`-torsion exactly when its `x`-coordinate is a root of `Ψ₃`; the hypothesis `y ≠ W.negY x y` of
`mem_torsion_three_some_iff` is automatic on both sides. -/
lemma mem_torsion_three_some_iff' [DecidableEq F] {x y : F} {h : W.Nonsingular x y} :
    Point.some x y h ∈ W.torsion 3 ↔ W.Ψ₃.eval x = 0 :=
  ⟨Ψ₃_eval_eq_zero_of_mem_torsion_three,
    fun hx => (mem_torsion_three_some_iff (Y_ne_negY_of_Ψ₃_eval_eq_zero h hx)).mpr hx⟩

/-! ## The fibres of the `x`-coordinate map -/

/-- Away from characteristic `2`, the Weierstrass equation at `(x, y)` says exactly that the
`2`-division value `2y + a₁x + a₃` is a square root of `Ψ₂Sq.eval x`. -/
lemma equation_iff_sq (h2 : (2 : F) ≠ 0) (x y : F) :
    W.Equation x y ↔ (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
  refine ⟨fun h => (Ψ₂Sq_eval_eq_sq h).symm, fun h => ?_⟩
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [equation_iff']
  refine mul_left_cancel₀ h4 ?_
  rw [mul_zero, Ψ₂Sq_eval] at *
  simp only [b₂, b₄, b₆] at h
  linear_combination h

/-- **Exactly two points of `W` lie above a value of `x` at which `Ψ₂Sq` is a nonzero square**,
over any field of characteristic `≠ 2`: the two square roots of `Ψ₂Sq.eval x` give the two
solutions `y` of the (quadratic) Weierstrass equation, and they are distinct because the square is
nonzero.

⚠️ **The two hypotheses are independent and both are needed**: `hsq` produces the roots and `hx`
keeps them apart.  Over an algebraically closed field `hsq` is free — that is
`card_setOf_equation_eq_two` below — and over a field that is not closed it is the *second* of the
two conditions an `#E[3] = 9` count has to carry, which is why `card_torsion_three_of_splits` takes
more than a splitting hypothesis.

⚠️ The hypothesis is `IsSquare`, not `∃ s, s ^ 2 = _`, matching `exists_equation_of_isSquare`
below: the two lemmas are the count and the existence half of the same quadratic, and a caller
should not have to hold the same fact in two shapes. -/
lemma card_setOf_equation_eq_two_of_isSquare (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₂Sq.eval x ≠ 0) (hsq : IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card {y : F // W.Equation x y} = 2 := by
  obtain ⟨s, hs'⟩ := hsq
  have hs : s ^ 2 = W.Ψ₂Sq.eval x := by rw [hs']; ring
  have hs0 : s ≠ 0 := fun h => hx (by rw [← hs, h]; ring)
  have hmem : ∀ y : F, W.Equation x y ↔
      y = (s - W.a₁ * x - W.a₃) / 2 ∨ y = (-s - W.a₁ * x - W.a₃) / 2 := by
    intro y
    rw [equation_iff_sq h2, ← hs]
    constructor
    · intro h
      have h' : (2 * y + W.a₁ * x + W.a₃ - s) * (2 * y + W.a₁ * x + W.a₃ + s) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact Or.inl (by rw [eq_div_iff h2]; linear_combination h'')
      · exact Or.inr (by rw [eq_div_iff h2]; linear_combination h'')
    · rintro (rfl | rfl) <;> field_simp <;> ring
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hne : (s - W.a₁ * x - W.a₃) / 2 ≠ (-s - W.a₁ * x - W.a₃) / 2 := by
    intro h
    rw [div_eq_div_iff h2 h2] at h
    exact hs0 ((mul_eq_zero.mp (show (4 : F) * s = 0 by linear_combination h)).resolve_left h4)
  have hset : {y : F | W.Equation x y}
      = {(s - W.a₁ * x - W.a₃) / 2, (-s - W.a₁ * x - W.a₃) / 2} := by
    ext y
    simpa using hmem y
  have hcard : Nat.card {y : F // W.Equation x y} = ({y : F | W.Equation x y}).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_pair hne]

/-- Over an algebraically closed field every value of `Ψ₂Sq` is a square.  This is the one thing
the closed forms below use their closure for, named once rather than obtained three times. -/
private lemma isSquare_eval_Ψ₂Sq [IsAlgClosed F] (x : F) : IsSquare (W.Ψ₂Sq.eval x) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (W.Ψ₂Sq.eval x) (n := 2) two_pos
  exact ⟨s, by rw [← hs]; ring⟩

/-- **Exactly two points of `W` lie above a value of `x` which is not a root of `Ψ₂Sq`**, over an
algebraically closed field of characteristic `≠ 2`: the two square roots of `Ψ₂Sq.eval x` give the
two solutions `y` of the (quadratic) Weierstrass equation.

The squareness hypothesis of `card_setOf_equation_eq_two_of_isSquare`, discharged by
`IsAlgClosed.exists_pow_nat_eq`. -/
lemma card_setOf_equation_eq_two [IsAlgClosed F] (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₂Sq.eval x ≠ 0) : Nat.card {y : F // W.Equation x y} = 2 :=
  card_setOf_equation_eq_two_of_isSquare h2 hx (isSquare_eval_Ψ₂Sq x)

/-- **A point above `x` exists as soon as `Ψ₂Sq.eval x` is a square**, over any field of
characteristic `≠ 2`.

Away from characteristic `2` the Weierstrass equation at `x` is a quadratic in `y` with
discriminant `Ψ₂Sq.eval x` (`equation_iff_sq`), so a square root `s` of that value produces the
point `y = (s - a₁x - a₃)/2` by the quadratic formula.  ⚠️ This is the **only** thing
`exists_equation` below ever used its algebraic closure for.

⚠️ The hypothesis is `IsSquare`, not `∃ s, s ^ 2 = _`.  `IsSquare a` unfolds to `∃ r, a = r * r`,
which is what `equation_iff_sq` wants after a single rewrite and what a caller over a field such as
`ℚ` discharges by exhibiting the root; the `^ 2` form would cost a `sq` rewrite at every call site.

⚠️ **RETIRED.**  This docstring used to close *"`card_setOf_equation_eq_two` above has the same
closure use and is deliberately **not** generalised alongside this: it is a count rather than an
existence, so its finite-level form would need the square to be nonzero as well, and no consumer in
this tree wants that statement."*  That generalisation is `card_setOf_equation_eq_two_of_isSquare`
above; the extra condition the clause names is exactly its `hx`, and at a root of `Ψ₃` it is free
by `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃` below.  The consumer that appeared is
`card_torsion_three_of_splits`: `#962`'s `n = 3` ledger asks for `#E[3] = 9` over a field that is
not algebraically closed, and `#2029` step 4 asks the same question one prime down. -/
lemma exists_equation_of_isSquare (h2 : (2 : F) ≠ 0) {x : F}
    (hsq : IsSquare (W.Ψ₂Sq.eval x)) : ∃ y : F, W.Equation x y := by
  obtain ⟨s, hs⟩ := hsq
  refine ⟨(s - W.a₁ * x - W.a₃) / 2, ?_⟩
  rw [equation_iff_sq h2, hs]
  field_simp
  ring

/-- Over an algebraically closed field of characteristic `≠ 2` every value of `x` is the
`x`-coordinate of a point of `W`: the Weierstrass equation is a quadratic in `y` whose discriminant
`Ψ₂Sq.eval x` always has a square root.

The squareness hypothesis of `exists_equation_of_isSquare`, discharged by
`IsAlgClosed.exists_pow_nat_eq`. -/
lemma exists_equation [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (x : F) : ∃ y : F, W.Equation x y :=
  exists_equation_of_isSquare h2
    (by obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (W.Ψ₂Sq.eval x) (n := 2) two_pos
        exact ⟨s, by rw [← hs]; ring⟩)

/-- A root of `Ψ₃` is never a root of `Ψ₂Sq`, stated without reference to a point above it.

⚠️ **This needs no algebraic closure, and it used to take one.**  The point above `x` that the
argument consumes does not have to come from `exists_equation`: under the hypothesis being
contradicted, `Ψ₂Sq.eval x = 0`, the `2`-torsion `y`-coordinate `twoTorsionY` is already on the
curve (`equation_twoTorsionY`), over any field of characteristic `≠ 2`.  The closure-free argument
was in this file all along, inline in `nodup_roots_Ψ₃` below, which now calls this lemma rather
than repeating it. -/
lemma Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x : F}
    (hx : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := fun hΨ₂ =>
  Ψ₂Sq_eval_ne_zero_of_Ψ₃_eval_eq_zero
    (equation_iff_nonsingular.mp (equation_twoTorsionY h2 hΨ₂)) hx hΨ₂

/-! ## Separability of the `3`-division polynomial -/

/-- The formal derivative of `Ψ₃` is `3 · Ψ₂Sq`. -/
lemma derivative_Ψ₃ : derivative W.Ψ₃ = 3 * W.Ψ₂Sq := by
  simp only [Ψ₃, Ψ₂Sq, derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C, derivative_ofNat, C_mul, C_ofNat, Nat.cast_ofNat]
  ring

variable (W) in
/-- The roots of `Ψ₃`, as a subtype, are exactly the members of its root finset. -/
def rootsEquivΨ₃ [DecidableEq F] (h3 : (3 : F) ≠ 0) :
    {x : F // W.Ψ₃.eval x = 0} ≃ {x : F // x ∈ W.Ψ₃.roots.toFinset} :=
  Equiv.subtypeEquivRight fun x => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (W.Ψ₃_ne_zero h3)]
    exact Iff.rfl

/-- **`Ψ₃` is separable.**  Its derivative is `3Ψ₂Sq`, and a root of `Ψ₃` is never a root of `Ψ₂Sq`,
so `Ψ₃` has no repeated roots.  In particular no quartic discriminant is needed. -/
lemma nodup_roots_Ψ₃ [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    W.Ψ₃.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_contra hcount
  rw [not_le] at hcount
  have hroot : W.Ψ₃.eval r = 0 := by
    have hpos : 0 < W.Ψ₃.rootMultiplicity r := lt_of_lt_of_le Nat.zero_lt_one hcount.le
    exact (rootMultiplicity_pos (W.Ψ₃_ne_zero h3)).mp hpos
  have hder : (derivative W.Ψ₃).IsRoot r := by
    simpa using isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 1) hcount
  rw [derivative_Ψ₃, IsRoot, eval_mul, eval_ofNat, mul_eq_zero] at hder
  exact Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 hroot (hder.resolve_left h3)

/-- **The `3`-division quartic has exactly four roots** over any field of characteristic `≠ 2, 3`
over which it *splits*: it has degree `4` there, and `nodup_roots_Ψ₃` rules out a repeated one.

⚠️ The splitting hypothesis is the **only** thing the algebraically closed form `card_roots_Ψ₃`
below ever used its closure for: `nodup_roots_Ψ₃` and `natDegree_Ψ₃` both need nothing beyond
`[W.IsElliptic]`, `h2` and `h3`.  This is the `n = 3` analogue of
`EllipticCurves.Torsion.TwoTorsion`'s `card_roots_Ψ₂Sq_of_splits`, and — unlike the `n = 2` case —
it is **not** enough on its own for a count of `E[3]`: see `card_torsion_three_of_splits`. -/
lemma card_roots_Ψ₃_of_splits [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsplits : W.Ψ₃.Splits) : Nat.card {x : F // W.Ψ₃.eval x = 0} = 4 := by
  classical
  rw [Nat.card_congr (W.rootsEquivΨ₃ h3), Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup (nodup_roots_Ψ₃ h2 h3),
    ← hsplits.natDegree_eq_card_roots, W.natDegree_Ψ₃ h3]

/-- **The `3`-division quartic has exactly four roots** over an algebraically closed field of
characteristic `≠ 2, 3`.

The splitting hypothesis of `card_roots_Ψ₃_of_splits`, discharged by `IsAlgClosed.splits`. -/
lemma card_roots_Ψ₃ [W.IsElliptic] [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card {x : F // W.Ψ₃.eval x = 0} = 4 :=
  card_roots_Ψ₃_of_splits h2 h3 (IsAlgClosed.splits _)

/-! ## The count and the structure theorem -/

section Count

variable [DecidableEq F] [W.IsElliptic]

/-- The `3`-torsion point attached to a root `x` of `Ψ₃` together with a `y`-coordinate above it,
with `none` sent to the point at infinity. -/
def torsionThreeOfPair :
    Option ((x : {x : F // W.Ψ₃.eval x = 0}) × {y : F // W.Equation x.1 y}) → W.torsion 3
  | none => 0
  | some ⟨x, y⟩ => ⟨Point.some x.1 y.1 (equation_iff_nonsingular.mp y.2),
      mem_torsion_three_some_iff'.mpr x.2⟩

lemma torsionThreeOfPair_bijective :
    Function.Bijective (torsionThreeOfPair (W := W)) := by
  constructor
  · rintro (_ | ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩) (_ | ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (Point.some_ne_zero _)
    · exact absurd (congrArg Subtype.val hab) (Point.some_ne_zero _)
    · have hxy := congrArg Subtype.val hab
      rw [torsionThreeOfPair, torsionThreeOfPair, Point.some.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      rfl
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨⟨x, mem_torsion_three_some_iff'.mp hP⟩, ⟨y, h.1⟩⟩, rfl⟩

/-- **`E[3]` is the point at infinity together with the points above the roots of `Ψ₃`.** -/
noncomputable def torsionThreeEquiv :
    W.torsion 3 ≃ Option ((x : {x : F // W.Ψ₃.eval x = 0}) × {y : F // W.Equation x.1 y}) :=
  (Equiv.ofBijective _ torsionThreeOfPair_bijective).symm

/-- **`#E[3] = 9`** for an elliptic curve over any field of characteristic `≠ 2, 3` over which the
`3`-division quartic **splits** and the `2`-division value is a **square at every root of it**: the
point at infinity together with the two points above each of the four roots.

⚠️ **Two hypotheses, and the second has no `n = 2` counterpart.**  At `n = 2` a torsion point *is*
its `x`-coordinate — `y = negY x y` there — so `EllipticCurves.Torsion.TwoTorsion`'s
`card_torsion_two_of_splits` needs the cubic to split and nothing else.  At `n = 3` the description
of `E[3]` is `torsionThreeEquiv`, a **sigma** over the roots of `Ψ₃` and not an `Option` of them,
and splitting `Ψ₃` fixes only the base of that sigma.  Each fibre is the solution set of a
quadratic in `y` of discriminant `Ψ₂Sq.eval x` (`equation_iff_sq`), so a count needs that
discriminant to be a square — **a condition on a different polynomial, which no amount of splitting
`Ψ₃` supplies**.

⚠️ The other half of `card_setOf_equation_eq_two_of_isSquare`'s pair of hypotheses is free here:
`Ψ₂Sq.eval x ≠ 0` at a root of `Ψ₃` is `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, which takes no closure and
no squareness. -/
theorem card_torsion_three_of_splits (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsplits : W.Ψ₃.Splits) (hsq : ∀ x : F, W.Ψ₃.eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nat.card (W.torsion 3) = 9 := by
  haveI : Finite {x : F // W.Ψ₃.eval x = 0} :=
    (W.finite_setOf_Ψ₃_root h3).to_subtype
  haveI : Fintype {x : F // W.Ψ₃.eval x = 0} := Fintype.ofFinite _
  haveI : ∀ x : {x : F // W.Ψ₃.eval x = 0}, Finite {y : F // W.Equation x.1 y} :=
    fun x => (W.setOf_equation_finite x.1).to_subtype
  have hfib : ∀ x : {x : F // W.Ψ₃.eval x = 0}, Nat.card {y : F // W.Equation x.1 y} = 2 :=
    fun x => card_setOf_equation_eq_two_of_isSquare h2
      (Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 x.2) (hsq x.1 x.2)
  have hroots : Fintype.card {x : F // W.Ψ₃.eval x = 0} = 4 := by
    rw [← Nat.card_eq_fintype_card, card_roots_Ψ₃_of_splits h2 h3 hsplits]
  rw [Nat.card_congr torsionThreeEquiv, Finite.card_option, Nat.card_sigma,
    Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_const, Finset.card_univ, hroots]
  norm_num

/-- **`#E[3] = 9`** for an elliptic curve over an algebraically closed field of characteristic
`≠ 2, 3`: the point at infinity together with the two points above each of the four roots of the
`3`-division quartic.

Both hypotheses of `card_torsion_three_of_splits`, discharged by `IsAlgClosed.splits` and
`IsAlgClosed.exists_pow_nat_eq`. -/
theorem card_torsion_three [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (W.torsion 3) = 9 :=
  card_torsion_three_of_splits h2 h3 (IsAlgClosed.splits _) fun x _ => isSquare_eval_Ψ₂Sq x

/-- **The structure theorem for `E[3]`, over any field over which `Ψ₃` splits and `Ψ₂Sq` is a
square at each of its roots.**  Away from characteristics `2` and `3`, the `3`-torsion subgroup of
an elliptic curve is isomorphic to `ℤ/3ℤ × ℤ/3ℤ` under exactly the two hypotheses that give the
count — no algebraic closure is involved.

This is the `n = 3` instance of `E[n] ≅ (ℤ/nℤ)²`, obtained by feeding the count `#E[3] = 9` into
the finite-abelian-group classification core `AddCommGroup.equiv_zmod_sq_of_card_sq`.  ⚠️ The rank
argument at the prime `2` below is pure group theory on `W.torsion 3` and never looked at the
field, which is why only the count had to be generalised. -/
theorem nonempty_torsionThree_addEquiv_of_splits (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hsplits : W.Ψ₃.Splits) (hsq : ∀ x : F, W.Ψ₃.eval x = 0 → IsSquare (W.Ψ₂Sq.eval x)) :
    Nonempty (W.torsion 3 ≃+ ZMod 3 × ZMod 3) := by
  haveI := W.finite_torsion_three h3
  have hcard : Nat.card (W.torsion 3) = 3 ^ 2 := by
    rw [card_torsion_three_of_splits h2 h3 hsplits hsq]
    norm_num
  refine AddCommGroup.equiv_zmod_sq_of_card_sq three_pos (fun a => nsmul_mem_torsion a) hcard ?_
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · -- an element of `E[3]` killed by `2` is killed by `3 - 2 = 1`
    have hone : ∀ a : W.torsion 3, (2 : ℕ) • a = 0 → a = 0 := by
      intro a ha
      have h3a : (3 : ℕ) • a = 0 := nsmul_mem_torsion a
      have key : (2 : ℕ) • a + a = (3 : ℕ) • a := by rw [← succ_nsmul]
      rw [ha, zero_add, h3a] at key
      exact key
    have hcard1 : Nat.card {a : W.torsion 3 // (2 : ℕ) • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hone a.1 a.2).trans (hone b.1 b.2).symm)⟩,
        ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    norm_num
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc Nat.card {a : W.torsion 3 // p • a = 0}
        ≤ Nat.card (W.torsion 3) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 3 ^ 2 := hcard
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2

/-- **The structure theorem for `E[3]`.**  Over an algebraically closed field of characteristic
`≠ 2, 3`, the `3`-torsion subgroup of an elliptic curve is isomorphic to `ℤ/3ℤ × ℤ/3ℤ`.

Both hypotheses of `nonempty_torsionThree_addEquiv_of_splits`, discharged by `IsAlgClosed.splits`
and `IsAlgClosed.exists_pow_nat_eq`. -/
theorem nonempty_torsionThree_addEquiv [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nonempty (W.torsion 3 ≃+ ZMod 3 × ZMod 3) :=
  nonempty_torsionThree_addEquiv_of_splits h2 h3 (IsAlgClosed.splits _)
    fun x _ => isSquare_eval_Ψ₂Sq x

end Count

end WeierstrassCurve.Affine
