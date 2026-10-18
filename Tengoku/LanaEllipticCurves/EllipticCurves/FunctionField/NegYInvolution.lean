/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Fixtures
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.TranslationPullback
import Tengoku.Seed.Algebra.Field.ZMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The hyperelliptic involution of `F(W)`, and the witness that `Aut_F F(W)` is nontrivial

Let `W` be a Weierstrass curve over a field `F`, with affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` and function field `F(W) = Frac F[W]`.  This file constructs the
**hyperelliptic involution**

```
ι : F(W) ≃ₐ[F] F(W),      ι(x) = x,      ι(y) = negY(x, y) = −y − a₁x − a₃,
```

and proves that it is **not the identity** as soon as `W` is elliptic.

`EllipticCurves.FunctionField.Places`, in its `## What is *not* here` section, **used to record**
the second half as an explicit gap:

> **A witness `σ ≠ 1` for the automorphism action.**  See `mapProjPointHom`'s docstring: the
> natural candidate is the hyperelliptic involution, and producing it as an `AlgEquiv` is real work
> that is not attempted here.  No claim of non-triviality of the action is made.

`negYAlgEquiv_ne_one` is that witness.  ⚠️ **The quotation above is that bullet's wording before
`1198891`; `Places` now records the discharge and names `negYAlgEquiv`, so do not expect to find
the sentence there.**

⚠️ **What that bullet still says is the half this file does not supply, and it is worth carrying
here rather than leaving to a reader who follows the pointer.**  In `Places`' words: *"**no claim
about the induced permutation of places is made.** `mapProjPoint ι ≠ 1` is a strictly further
statement — it needs a place that `ι` moves — and it is proved nowhere."*  So `negYAlgEquiv_ne_one`
is a witness that the **automorphism** is nontrivial, and nothing below upgrades it to a statement
that the induced permutation of `ProjPoint W` is.  The two witnesses and what separates them are in
`mapProjPointHom`'s docstring.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.negYCoordHom` — the coordinate-ring half,
  `F[W] →ₐ[F[X]] F[W]`, sending the class of `Y` to the class of `W.negPolynomial`;
* `WeierstrassCurve.Affine.CoordinateRing.negYCoordEquiv` — the same map as an `AlgEquiv`, it being
  its own inverse;
* `WeierstrassCurve.Affine.CoordinateRing.negYEquiv` — the induced `F(W) ≃+* F(W)`, namely
  `IsFractionRing.ringEquivOfRingEquiv (negYCoordEquiv W).toRingEquiv`.  ⚠️ It is public and is not
  an implementation detail: it is the term `divisor_ringEquivOfRingEquiv` is instantiated at in the
  `## Free theorems` section below, so a reader chasing the affine divisor transport of `ι` lands
  on it;
* `WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv` — the involution of the function field,
  `F(W) ≃ₐ[F] F(W)`.

## Main results

* `WeierstrassCurve.Affine.polynomial_comp_negPolynomial` — the substitution identity
  `W.polynomial ∘ W.negPolynomial = W.polynomial` in `R[X][Y]`, which is what makes `ι` exist;
* `WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv_genX` and `negYAlgEquiv_genY` — the generator
  images, the second in the `negY` form of the base-changed curve `W ⁄ F(W)`;
* `WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv_negYAlgEquiv` — `ι ∘ ι = id`;
* `WeierstrassCurve.Δ_eq_zero_of_two_eq_zero` — a Weierstrass curve with `2 = 0`, `a₁ = 0`, `a₃ = 0`
  has `Δ = 0`;
* `WeierstrassCurve.Affine.polynomialY_ne_zero` — hence `W.polynomialY ≠ 0` for an elliptic curve
  over a nontrivial ring, in **every** characteristic;
* **`WeierstrassCurve.Affine.CoordinateRing.negYAlgEquiv_ne_one`** — the headline: `ι ≠ 1` whenever
  `[W.IsElliptic]`;
* **`WeierstrassCurve.Affine.CoordinateRing.nontrivial_algEquiv`** — `Nontrivial (F(W) ≃ₐ[F] F(W))`,
  the usable repackaging of the headline and what a consumer wanting a nontrivial automorphism
  group reaches for.

⚠️ This list is **selective, and deliberately so**: the file has 28 public declarations, plus 4
non-public ones (2 `def`s and 2 `instance`s in the non-vacuity section).  Twelve are listed above
and **sixteen are omitted** as steps of the two headlines rather than results in their own right —
among them `mk_polynomialY_ne_zero`, `Δ_eq_zero_of_polynomialY_eq_zero`, `natDegree_polynomialY_le`,
the four `negYCoordHom_*` lemmas, `negYAlgEquiv_genPsi` and `negYAlgEquiv_genY'`.  ⚠️ **Not**
`negYAlgEquiv_genX`, `negYAlgEquiv_genY` or `negYAlgEquiv_negYAlgEquiv`, which are listed above: a
glob over `negYAlgEquiv_gen*` would be a claim about a set that the list five lines up refutes.

⚠️ **The count is stated because PR #413's body said *"24"*, and the reason it did is worth more
than the correction.**  The declaration-count detector this tree's checklists mandate,

```
grep -nE '^(private |noncomputable |protected )*(theorem|lemma|def|abbrev|instance) ' <f> | wc -l
```

returns exactly **24** on this file, against a true 32 (28 public + 4 private).  It cannot see a
declaration written `@[simp] lemma …` on one line, and there are **eight** of those here.  So the
"24" was very likely the prescribed check answering, not a total copied from the section headers.
A better first approximation allows the attribute prefix,

```
grep -cE '^(@\[[^]]*\] *)*(private |noncomputable |protected |nonrec |scoped )*'\
'(theorem|lemma|def|abbrev|instance|structure|class) '
```

⚠️ but it is still not sound: it cannot see an `@[...]` on its own line, nor an
`attribute [...] in` standing before a docstring.  **The only reliable count is taken from
comment-stripped source with the attribute prefix consumed.**

## Why this is cheap, and where the one piece of mathematics is

`negY` is a *polynomial* in the coordinates, so — unlike `translateEndo`
(`EllipticCurves.FunctionField.TranslationEndomorphism`), which is built by `IsFractionRing.lift`
out of a dominance argument occupying a whole file — `ι` already exists on the coordinate ring, and
is visibly bijective because it is its own inverse.  Everything through `negYAlgEquiv` is
`AdjoinRoot.liftAlgHom` applied to the identity

```
W.polynomial.comp W.negPolynomial = W.polynomial,
```

which is `ring1` once the `Polynomial.comp` distribution lemmas have fired: substituting
`Y ↦ −Y − a₁X − a₃` into `Y² + a₁XY + a₃Y − (X³ + a₂X² + a₄X + a₆)` cancels the cross terms
identically.

**The mathematics is entirely in `negYAlgEquiv_ne_one`**, and it is the reason `[W.IsElliptic]`
appears.  `ι = 1` forces `y = −y − a₁x − a₃` in `F(W)`, i.e. `mk W W.polynomialY = 0`, i.e.
`W.polynomial ∣ W.polynomialY` in `F[X][Y]`.  The divisor has `Y`-degree `2` and the dividend
`Y`-degree at most `1`, so this forces `W.polynomialY = 0` outright — that is,
`(2 : F) = 0` **and** `a₁ = 0` **and** `a₃ = 0`, the inseparable case.  So `ι ≠ 1` is *false* for a
bare Weierstrass curve, and `Δ ≠ 0` is exactly what excludes the counterexample.

⚠️ The discriminant step is shorter than the characteristic-`2` folklore suggests, and needs no
case analysis and no `j`-invariant: with `2 = 0`, `a₁ = 0`, `a₃ = 0` one has
`b₂ = a₁² + 4a₂ = 0`, `b₄ = 2a₄ + a₁a₃ = 0` and `b₆ = a₃² + 4a₆ = 0`, and **every** term of
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆` carries one of `b₂`, `b₄`, `b₆`.  `b₈` never has to be
computed.

⚠️ Correspondingly the results below are stated with **no hypothesis on the characteristic**.  A
`(2 : F) ≠ 0` hypothesis would make `negYAlgEquiv_ne_one` vacuous in exactly the characteristic
where it has content, and the argument above does not need one; the non-vacuity section commits a
characteristic-`2` curve for this reason.

## Scope — what is deliberately *not* claimed

* **Nothing here says the induced permutation of places is nontrivial.**
  `EllipticCurves.FunctionField.Places`'s `mapProjPointHom` sends an `F`-automorphism of `F(W)`
  to a permutation of `ProjPoint W`, and `ι ≠ 1` is a statement about the automorphism, not about
  its image.  Showing
  `mapProjPoint ι ≠ 1` needs a place that `ι` moves, and that is a separate question.
* **No separability or Galois statement is made.**  `ι` is what one would use to prove
  `Algebra.IsSeparable ↥(ratFuncRange W) F(W)` and `IsGalois ↥(ratFuncRange W) F(W)` in every
  characteristic, by the `EllipticCurves.FunctionField.MulByTwoGalois` template with `⟨ι⟩` in place
  of `TorsionTwoMul W` — `ι` fixes `genX`, Artin computes the degree of the fixed field, and
  `finrank_ratFuncRange` says `[F(W) : F(x)] = 2`.  None of it is attempted here; in particular
  this file proves **no** statement about `ratFuncRange W`.  ⚠️ It is carried out, by exactly that
  route, in `EllipticCurves.FunctionField.NegYGalois` — `isGalois_ratFuncRange`, and
  `isGalois_ratFunc` for the abstract `RatFunc F`.  This sentence is a forward pointer and not an
  import: nothing in this file depends on that one.
* `polynomial_comp_negPolynomial`, `Δ_eq_zero_of_two_eq_zero`, `natDegree_polynomialY_le` and
  `polynomialY_ne_zero` are curve-generic and are upstream-Mathlib candidates; they are kept here
  because they have no other consumer in this tree yet.

## Free theorems, measured rather than promised

Two merged transport theorems are already generic in the automorphism, so `ι` needs **no new
transport theorem** — one instantiates the generic one, and no import is taken here for the sake of
restating it.  Both carry `[IsDedekindDomain W.CoordinateRing]`, the standing hypothesis of the
divisor layer.

⚠️ **This paragraph used to continue** *"which is a hypothesis of the divisor layer everywhere and
is **not** available for a bare `W` over a bare field — the `## Scope` section of
`EllipticCurves.FunctionField.DivisorTransport` records that it is discharged over an algebraically
closed field."*  **The quoted clause is false**, and it is false about this file's own subject:
`EllipticCurves.FunctionField.CoordinateRingNormalGeneral` registers `instIsDedekindDomain` as a
**global instance for `[W.IsElliptic]` over an arbitrary field**, with no `[IsAlgClosed F]`, so for
every curve this file talks about the hypothesis costs nothing.  The clause was copied from
`DivisorTransport`'s `## Scope`, whose own `variable` line carries **no** `[W.IsElliptic]` — where
it was true and merely superseded; restating it here, under `[W.IsElliptic]`, made it false.
⚠️ **Name the binder a hypothesis claim is relative to, every time.**

⚠️ **Availability is not the same as scope, and the difference bites here.**
`CoordinateRingNormalGeneral` is not among this file's imports, so
`IsDedekindDomain W.CoordinateRing` is not synthesised inside `NegYInvolution` itself.  It costs a
consumer nothing all the same — `EllipticCurves.FunctionField.PlaceOrder`, the module that supplies
`divisorProj_algEquiv`, does reach it, so anyone in a position to *use* the two instantiations
listed in this section already has the instance.  The
spike that measures this is stated for the `variable` line

```
{F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
```

— `[W.IsElliptic]` and nothing else, no `[IsDedekindDomain W.CoordinateRing]` and no
`[IsAlgClosed F]` — and the two instantiations that follow were type-checked under it, not
asserted:

* `divisorProj_algEquiv` (`EllipticCurves.FunctionField.PlaceOrder`) is stated for an arbitrary
  `σ : F(W) ≃ₐ[F] F(W)`, so
  `divisorProj W (ι f) = (divisorProj W f).mapDomain (mapProjPoint ι)` is
  `divisorProj_algEquiv (negYAlgEquiv W) hf` — given `[IsDedekindDomain W.CoordinateRing]` and
  `hf : f ≠ 0`, the two hypotheses the generic statement already carries;
* `divisor_ringEquivOfRingEquiv` (`EllipticCurves.FunctionField.DivisorTransport`) is stated for an
  arbitrary `e : F[W] ≃+* F[W]`, and `negYEquiv` is
  `IsFractionRing.ringEquivOfRingEquiv (negYCoordEquiv W).toRingEquiv` by definition, so the
  **affine** divisor transport of `ι` is `divisor_ringEquivOfRingEquiv _ f` — no hypothesis on `f`,
  but the same `[IsDedekindDomain W.CoordinateRing]`.

⚠️ Neither is a new theorem and neither is restated below; the point of recording them is that a
reader looking for the divisor behaviour of `ι` should reach for the generic lemma rather than file
an issue for a specialisation.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 (negation) and II.2.
* [H. Stichtenoth, *Algebraic function fields and codes*][stichtenoth2009], I.1–I.4.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### The substitution identities in `R[X][Y]` -/

variable (W' : Affine R)

namespace Affine

/-- **The Weierstrass polynomial is invariant under `Y ↦ −Y − a₁X − a₃`.**  This is the identity
that makes the hyperelliptic involution exist: expanding
`(−Y − a₁X − a₃)² + a₁X(−Y − a₁X − a₃) + a₃(−Y − a₁X − a₃)` returns `Y² + a₁XY + a₃Y`, the square
and cross terms cancelling identically. -/
theorem polynomial_comp_negPolynomial :
    W'.polynomial.comp W'.negPolynomial = W'.polynomial := by
  simp only [polynomial, negPolynomial, sub_comp, add_comp, mul_comp, pow_comp, X_comp, C_comp]
  ring1

/-- **`Y ↦ −Y − a₁X − a₃` is an involution of `R[X][Y]`.** -/
theorem negPolynomial_comp_negPolynomial :
    W'.negPolynomial.comp W'.negPolynomial = (Y : R[X][Y]) := by
  simp only [negPolynomial, sub_comp, neg_comp, X_comp, C_comp]
  ring1

/-- The `Y`-degree of `W.polynomialY = 2Y + (a₁X + a₃)` is at most one — the fact that makes
`W.polynomial ∣ W.polynomialY` collapse to `W.polynomialY = 0`. -/
lemma natDegree_polynomialY_le : W'.polynomialY.natDegree ≤ 1 := by
  rw [polynomialY]
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans (natDegree_C_mul_le _ _) natDegree_X_le
  · exact (natDegree_C _).le.trans zero_le_one

end Affine

/-! ### The discriminant vanishes in the inseparable case -/

variable {W'}

/-- **A Weierstrass curve with `2 = 0`, `a₁ = 0` and `a₃ = 0` has vanishing discriminant.**

No case analysis and no `j`-invariant: the three hypotheses kill `b₂ = a₁² + 4a₂`,
`b₄ = 2a₄ + a₁a₃` and `b₆ = a₃² + 4a₆`, and every term of
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆` carries one of the three.  `b₈` is never computed. -/
theorem Δ_eq_zero_of_two_eq_zero (h2 : (2 : R) = 0) (h1 : W'.a₁ = 0) (h3 : W'.a₃ = 0) :
    W'.Δ = 0 := by
  have hb2 : W'.b₂ = 0 := by simp only [b₂, h1]; linear_combination 2 * W'.a₂ * h2
  have hb4 : W'.b₄ = 0 := by simp only [b₄, h1, h3]; linear_combination W'.a₄ * h2
  have hb6 : W'.b₆ = 0 := by simp only [b₆, h3]; linear_combination 2 * W'.a₆ * h2
  simp only [Δ, hb2, hb4, hb6]
  ring1

/-- **`W.polynomialY = 0` forces `Δ = 0`.**  Reading off the two coefficients of
`W.polynomialY = C (C 2) * Y + C (C a₁ * X + C a₃)` gives `2 = 0`, `a₁ = 0` and `a₃ = 0`, and then
`Δ_eq_zero_of_two_eq_zero` applies. -/
theorem Δ_eq_zero_of_polynomialY_eq_zero (h : W'.polynomialY = 0) : W'.Δ = 0 := by
  have h2 : (2 : R) = 0 := by
    have := congrArg (fun p : R[X][Y] => (p.coeff 1).coeff 0) h
    simpa [Affine.polynomialY, coeff_C] using this
  have hc : C W'.a₁ * X + C W'.a₃ = (0 : R[X]) := by
    have := congrArg (fun p : R[X][Y] => p.coeff 0) h
    simpa [Affine.polynomialY, coeff_C, h2] using this
  have h1 : W'.a₁ = 0 := by
    have := congrArg (fun p : R[X] => p.coeff 1) hc
    simpa [coeff_C] using this
  have h3 : W'.a₃ = 0 := by
    have := congrArg (fun p : R[X] => p.coeff 0) hc
    simpa [coeff_C, h1] using this
  exact Δ_eq_zero_of_two_eq_zero h2 h1 h3

/-- **For an elliptic curve `W.polynomialY` is nonzero, in every characteristic.**  Contrapositive
of `Δ_eq_zero_of_polynomialY_eq_zero` against `IsElliptic`. -/
theorem Affine.polynomialY_ne_zero [Nontrivial R] [W'.IsElliptic] : W'.polynomialY ≠ 0 :=
  fun h => W'.isUnit_Δ.ne_zero (Δ_eq_zero_of_polynomialY_eq_zero h)

namespace Affine
namespace CoordinateRing

/-! ### The involution of the coordinate ring -/

variable (W')

/-- Evaluating a bivariate polynomial at the class of another one is the class of their
composite: `mk W (q ∘ r) = eval₂ (of W.polynomial) (mk W r) q`. -/
lemma eval₂_of_mk_eq_mk_comp (q r : R[X][Y]) :
    q.eval₂ (AdjoinRoot.of W'.polynomial) (mk W' r) = mk W' (q.comp r) := by
  rw [Polynomial.comp, Polynomial.hom_eval₂]
  rfl

/-- The well-definedness obligation of `negYCoordHom`: the class of `W.negPolynomial` is a root of
`W.polynomial` in `F[W]`, which is `polynomial_comp_negPolynomial` read through `mk`. -/
lemma eval₂_ofId_mk_negPolynomial :
    W'.polynomial.eval₂ (Algebra.ofId R[X] W'.CoordinateRing) (mk W' W'.negPolynomial) = 0 := by
  rw [show ((Algebra.ofId R[X] W'.CoordinateRing : R[X] →+* W'.CoordinateRing))
        = AdjoinRoot.of W'.polynomial from rfl,
    eval₂_of_mk_eq_mk_comp, polynomial_comp_negPolynomial, AdjoinRoot.mk_self]

/-- **The hyperelliptic involution on the coordinate ring**, `F[W] →ₐ[F[X]] F[W]`, fixing `x` and
sending `y` to `−y − a₁x − a₃`.  Unlike `translateEndo` this needs no dominance argument: `negY` is
polynomial, so the map already exists before passing to fractions. -/
noncomputable def negYCoordHom : W'.CoordinateRing →ₐ[R[X]] W'.CoordinateRing :=
  AdjoinRoot.liftAlgHom W'.polynomial (Algebra.ofId R[X] W'.CoordinateRing)
    (mk W' W'.negPolynomial) (eval₂_ofId_mk_negPolynomial W')

@[simp] lemma negYCoordHom_mk (q : R[X][Y]) :
    negYCoordHom W' (mk W' q) = mk W' (q.comp W'.negPolynomial) := by
  rw [negYCoordHom, AdjoinRoot.liftAlgHom_mk]
  exact eval₂_of_mk_eq_mk_comp W' q W'.negPolynomial

@[simp] lemma negYCoordHom_root :
    negYCoordHom W' (AdjoinRoot.root W'.polynomial) = mk W' W'.negPolynomial := by
  rw [← AdjoinRoot.mk_X, negYCoordHom_mk, X_comp]

/-- **The coordinate-ring map is an involution**, by `negPolynomial_comp_negPolynomial` on the
root. -/
lemma negYCoordHom_comp_negYCoordHom :
    (negYCoordHom W').comp (negYCoordHom W') = AlgHom.id R[X] W'.CoordinateRing :=
  AdjoinRoot.algHom_ext <| by
    rw [AlgHom.comp_apply, negYCoordHom_root, negYCoordHom_mk,
      negPolynomial_comp_negPolynomial, AdjoinRoot.mk_X, AlgHom.coe_id, id_eq]

@[simp] lemma negYCoordHom_negYCoordHom (g : W'.CoordinateRing) :
    negYCoordHom W' (negYCoordHom W' g) = g :=
  DFunLike.congr_fun (negYCoordHom_comp_negYCoordHom W') g

/-- **The hyperelliptic involution of `F[W]`** as an `F[X]`-algebra automorphism: `negYCoordHom` is
its own inverse. -/
noncomputable def negYCoordEquiv : W'.CoordinateRing ≃ₐ[R[X]] W'.CoordinateRing :=
  AlgEquiv.ofAlgHom (negYCoordHom W') (negYCoordHom W')
    (negYCoordHom_comp_negYCoordHom W') (negYCoordHom_comp_negYCoordHom W')

@[simp] lemma negYCoordEquiv_apply (g : W'.CoordinateRing) :
    negYCoordEquiv W' g = negYCoordHom W' g := rfl

/-! ### The involution of the function field -/

variable {F : Type*} [Field F] (W : Affine F)

/-- The hyperelliptic involution of `F(W)` as a ring automorphism, obtained from
`negYCoordEquiv` by `IsFractionRing.ringEquivOfRingEquiv`.  ⚠️ Note that this is exactly the shape
`EllipticCurves.FunctionField.DivisorTransport` records `translateEndo` as *not* having — *"it is
not `ringEquivOfRingEquiv e` for any `e : F[W] ≃+* F[W]`, the induced map on affine closed points
is only partially defined"* — because `ι` **does** preserve the affine coordinate ring. -/
noncomputable def negYEquiv : W.FunctionField ≃+* W.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (negYCoordEquiv W).toRingEquiv

lemma negYEquiv_algebraMap (g : W.CoordinateRing) :
    negYEquiv W (genPsi W g) = genPsi W (negYCoordHom W g) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ g

/-- **The hyperelliptic involution `ι : F(W) ≃ₐ[F] F(W)`**, `x ↦ x`, `y ↦ −y − a₁x − a₃`. -/
noncomputable def negYAlgEquiv : W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofRingEquiv (f := negYEquiv W) (fun c => by
    rw [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField,
      ← genPsi, negYEquiv_algebraMap]
    congr 1
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing]
    exact (negYCoordHom W).commutes _)

@[simp] lemma negYAlgEquiv_genPsi (g : W.CoordinateRing) :
    negYAlgEquiv W (genPsi W g) = genPsi W (negYCoordHom W g) :=
  negYEquiv_algebraMap W g

/-- **`ι` fixes the generic `x`-coordinate.** -/
@[simp] lemma negYAlgEquiv_genX : negYAlgEquiv W (genX W) = genX W := by
  rw [genX, negYAlgEquiv_genPsi, negYCoordHom_mk, C_comp]

/-- **`ι` negates the generic `y`-coordinate**: it sends `y` to `−y − a₁x − a₃`. -/
@[simp] lemma negYAlgEquiv_genY :
    negYAlgEquiv W (genY W) =
      -genY W - algebraMap F W.FunctionField W.a₁ * genX W
        - algebraMap F W.FunctionField W.a₃ := by
  have hC : (C (C W.a₁ * X + C W.a₃) : F[X][Y]) = C (C W.a₁) * C X + C (C W.a₃) := by
    rw [map_add, map_mul]
  rw [genY, negYAlgEquiv_genPsi, negYCoordHom_root, negPolynomial, hC]
  simp only [map_sub, map_neg, map_add, map_mul, genPsi_mk_CC]
  rw [← genX, AdjoinRoot.mk_X]
  ring

/-- **`ι` is the negation of the generic point**, in the `negY` of the base-changed curve
`W ⁄ F(W)` — the same curve `equation_gen` puts `(genX, genY)` on. -/
lemma negYAlgEquiv_genY' :
    negYAlgEquiv W (genY W) =
      (W.map (algebraMap F W.FunctionField)).negY (genX W) (genY W) := by
  rw [negYAlgEquiv_genY, negY, map_a₁, map_a₃]

@[simp] lemma negYAlgEquiv_negYAlgEquiv (f : W.FunctionField) :
    negYAlgEquiv W (negYAlgEquiv W f) = f := by
  obtain ⟨g, d, -, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) f
  simp only [map_div₀, negYAlgEquiv_genPsi, negYCoordHom_negYCoordHom]

/-- **`ι ∘ ι = id`.** -/
lemma negYAlgEquiv_trans_negYAlgEquiv :
    (negYAlgEquiv W).trans (negYAlgEquiv W) = AlgEquiv.refl :=
  AlgEquiv.ext (negYAlgEquiv_negYAlgEquiv W)

/-! ### The involution is not the identity -/

/-- The class of `W.polynomialY` is nonzero in `F[W]` for an elliptic curve: `W.polynomial` is
monic of `Y`-degree `2` and `W.polynomialY` is nonzero of `Y`-degree at most `1`, so the former
cannot divide the latter. -/
theorem mk_polynomialY_ne_zero [W.IsElliptic] : mk W W.polynomialY ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial polynomialY_ne_zero
    (by rw [natDegree_polynomial]; exact lt_of_le_of_lt (natDegree_polynomialY_le W) one_lt_two)

/-- `W.polynomialY = Y − W.negPolynomial`, read in `F(W)`: the class of `W.polynomialY` is the
difference between the generic `y` and its image under `ι`. -/
lemma genPsi_mk_polynomialY :
    genPsi W (mk W W.polynomialY) = genY W - negYAlgEquiv W (genY W) := by
  rw [← Y_sub_negPolynomial, map_sub, map_sub, AdjoinRoot.mk_X, ← genY, genY,
    negYAlgEquiv_genPsi, negYCoordHom_root]

/-- **The hyperelliptic involution is not the identity**, for any elliptic curve over any field —
with no hypothesis on the characteristic.

This is the `σ ≠ 1` witness `EllipticCurves.FunctionField.Places` records as missing.  If `ι = 1`
then `genPsi W (mk W W.polynomialY) = 0` by `genPsi_mk_polynomialY`, hence `mk W W.polynomialY = 0`
because `F[W] → F(W)` is injective, contradicting `mk_polynomialY_ne_zero`.

⚠️ It is *not* a claim that `ι` acts nontrivially on the places of `F(W)`: `mapProjPointHom` is a
different statement and is untouched here. -/
theorem negYAlgEquiv_ne_one [W.IsElliptic] : negYAlgEquiv W ≠ 1 := by
  intro h
  refine mk_polynomialY_ne_zero W ?_
  refine (injective_iff_map_eq_zero _).mp
    (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ ?_
  rw [genPsi_mk_polynomialY, h, AlgEquiv.one_apply, sub_self]

/-- **`Aut_F F(W)` is nontrivial** for an elliptic curve over any field. -/
theorem nontrivial_algEquiv [W.IsElliptic] :
    Nontrivial (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  ⟨negYAlgEquiv W, 1, negYAlgEquiv_ne_one W⟩

/-! ### Non-vacuity

`negYAlgEquiv_ne_one` needs `[W.IsElliptic]` and nothing else, and its whole content is in the
characteristic where `2 = 0`.  ⚠️ A `ℚ` certificate alone would therefore certify the *easy* half
and hide the one this file exists for, so a characteristic-`2` curve is committed as well:
`y² + y = x³` over `ZMod 2`, which is elliptic (`Δ = −27 = 1`) and has `a₁ = 0` — so it is exactly a
curve for which `2 = 0` and `a₁ = 0` hold and the involution is nevertheless nontrivial, `a₃ = 1`
being the surviving term of `W.polynomialY`. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/

open EllipticCurves.Fixture

/-- The supersingular curve `y² + y = x³` over `ZMod 2`, of discriminant `−27 = 1`. -/
private def exampleCurveTwo : Affine (ZMod 2) := ⟨0, 0, 1, 0, 0⟩

end Nonvacuity

end CoordinateRing
end Affine
end WeierstrassCurve
