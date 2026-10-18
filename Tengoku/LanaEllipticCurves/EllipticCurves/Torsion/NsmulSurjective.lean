/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.ThreeTorsionStructure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Surjectivity of `[n]` on `E(F̄)` from the multiplication-by-`n` coordinate formula

Over an algebraically closed field with `(2 : F) ≠ 0`, multiplication by `n` is surjective on the
points of an elliptic curve as soon as two index-dependent facts are available:

1. the coordinate formula `x(nP) = Φₙ(x)/ΨSqₙ(x)`, packaged here as `HasXCoordFormula W n`, and
2. the pointwise statement that `Φₙ` and `ΨSqₙ` have no common root in `F`.

**Everything else is uniform in `n`** — the degree count on `Φₙ − x₀·ΨSqₙ`, the root extraction over
`F̄`, the choice of a point above the root, and the absorption of the sign ambiguity `nP = ±Q` — and
this file is that uniform half, written once.

## ⚠️ Where the algebraic closure enters, and the finite-level layer that does without it

`[IsAlgClosed F]` is used in exactly **two** places in this file, both inside
`exists_nsmul_some_of_hasXCoordFormula`: the root extraction `exists_eval_Φ_eq` and the point
above the root `exists_equation`.  Nothing else here, and nothing this file imports on its behalf,
needs a closed field.  Promoted to arguments they give
`exists_nsmul_some_of_hasXCoordFormula_of_root` and its named-point form, which hold over an
arbitrary field — and, because `(2 : F) ≠ 0` and `n ≠ 0` are consumed *only* by those two uses, in
every characteristic and at every `n` as well.

⚠️ The two uses are **dependent**: the point is sought above the root the first one produced.  So
the finite-level form takes `x` and `y` as arguments rather than taking two independent
hypotheses — the naive "add a `Splits` hypothesis and an `IsSquare` hypothesis" shape does not
typecheck, because the second would have to mention a variable the first introduces.

`EllipticCurves.Torsion.DoublingSurjective` and `EllipticCurves.Torsion.TriplingSurjective`, which
**import this file**, supply the two inputs at `n = 2` and `n = 3` and obtain `nsmul_two_surjective`
and `nsmul_three_surjective` as one-line instances of `nsmul_surjective_of_hasXCoordFormula`.

## What this does and does not settle

⚠️ **Nothing is proved here at any index.**  This file contains no instance of either input; taken
alone its two headline theorems are conditional statements with no known witness.  The witnesses are
downstream.  ⚠️ **They are no longer the two low indices**: input (1) is witnessed at *every* index
by `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`, which imports this file)
over any field with `(2 : F) ≠ 0`, and input (2) at every **nonzero** index by
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`) on an elliptic curve
over an algebraically closed field with `(2 : F) ≠ 0`.  `hasXCoordFormula_two` /
`hasXCoordFormula_three` (`…DoublingSurjective`, `…TriplingSurjective`) remain the instances a
consumer *below* `NsmulOrder` can reach.

What the file *does* settle is **how much is needed, and that it is exactly two things**.
`EllipticCurves.Torsion.CoprimeStructure` reduces the structure theorem `E[n] ≅ (ℤ/nℤ)²` to prime
powers and records that every prime `p ≥ 5` is blocked on `[p]`-surjectivity, "which still needs the
general coordinate formula".  Its subject has names: what that sentence called missing at a prime
`p ≥ 5` is a term of `HasXCoordFormula W p` (issue `#251`) **and** a term of
`∀ x, (W.ΨSq p).eval x = 0 → (W.Φ p).eval x ≠ 0` (implied by issue `#1184`, and strictly weaker than
it).  Beyond those two, nothing — no degree hypothesis, no Bézout certificate, and no hypothesis on
`(n : F)`.

⚠️ **Both are now supplied, and the sentence quoted above no longer describes the tree.**  Composing
the two witnesses named in the previous section gives `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`): `[n]`-surjectivity on `E(F̄)` at **every** `n ≠ 0` on an
elliptic curve over an algebraically closed field with `(2 : F) ≠ 0`, with no `3`-smoothness and no
condition on `p`.  `EllipticCurves.Torsion.PrimaryTower`'s gate list records the same two closures.
⚠️ **This does not close `#1184`**, of which input (2) is only the pointwise shadow over `F̄`: that
shadow is obtained from the order dictionary rather than from a Bézout certificate and does not
descend to the `IsCoprime` statement over an arbitrary base.  Neither module named here is in this
file's import closure and none is added.

⚠️ So `#1184` is **not** only a gate under rung 3's degree count, which is where it is filed: a
weakening of it is also a gate under the structure theorem at every prime `p ≥ 5`.

⚠️ **The next sentence of this paragraph used to read *"The two instances that exist show the
weakening is the cheaper target — neither `n = 2` nor `n = 3` obtains it through Bézout"*, and its
second half is still exactly right while its first half has been answered and refuted.**  What was
measured is that at both available indices the pointwise input is obtained without a Bézout
certificate; what was inferred from it is that the pointwise statement is therefore the cheaper
target at general `n`.  It is not.  `eval_Φ_ne_zero_iff_of_eval_ΨSq_eq_zero`, in
`EllipticCurves.DivisionPolynomial.Coprime`, shows that at a root of `ΨSqₙ` the square of `Φₙ`
**is** the adjacent product `ΨSqₙ₊₁ · ΨSqₙ₋₁`.  So over a field the pointwise statement for
`(Φₙ, ΨSqₙ)` is *equivalent* to the pointwise statement for the adjacent pair, and the surviving
difficulty — that `ΨSqₙ` and its neighbours have no common root — is the same one `#1184` is left
with after `isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent`.  The weakening drops the Bézout certificate
and nothing else.

⚠️ **Nothing about this file changes.**  Its input is still the pointwise statement, that is still
strictly weaker than `#1184`, and taking it in that form is still right — what is retired is only
the claim that the general target is cheaper *because* of it.  Neither module named above is in
this file's import closure and none is added; both directions were re-grepped when this paragraph
was written.

## Two economies of the `n = 2` and `n = 3` arguments are preserved deliberately

* **No hypothesis on `(n : F)`.**  The degree input is `natDegree_Φ (n : ℤ) = n.natAbs ^ 2` with
  leading coefficient `1`, against `natDegree_ΨSq_le (n : ℤ) ≤ n.natAbs ^ 2 - 1`; **both are
  unconditional in Mathlib**, so `n ≠ 0` alone gives `Φₙ − C x₀ · ΨSqₙ` degree `n²`.  Mathlib's
  sharp `natDegree_ΨSq` carries `(n : R) ≠ 0` and is *not* used.  `TriplingSurjective`'s docstring
  records that this is exactly what makes `nsmul_three_surjective` hold in characteristic `3`; the
  same economy survives at general `n`.
* **No Bézout certificate — in this file.**  Input (2) is taken in the weak pointwise form
  `∀ x, (ΨSqₙ).eval x = 0 → (Φₙ).eval x ≠ 0`, and nothing here asks for more.
  The full coprimality `IsCoprime (W.Φ n) (W.ΨSq n)` — issue `#1184` — is **strictly stronger**
  than what is used, and `eval_Φ_ne_zero_of_isCoprime` below is the one-line bridge that lets it be
  plugged in.  ⚠️ It is a bridge and not a dependency: `#1184` is not in this file's import
  closure.  ⚠️ This bullet used to add *"proved in this tree only at `n = 2` and `n = 3`"* and
  *"if it ever lands at general `n`"*; it has landed, at every `n : ℤ` for an elliptic curve over a
  field of characteristic `≠ 2` (`WeierstrassCurve.Affine.isCoprime_Φ_ΨSq`,
  `EllipticCurves.Torsion.CoprimeAdjacent`, **downstream** of this file).  The `n = 2` and `n = 3`
  instances in `EllipticCurves.DivisionPolynomial.Coprime` are not superseded: they hold over an
  arbitrary commutative ring.

  ⚠️ **This bullet used to continue *"…which is what the two available instances establish
  directly — at `n = 2` through `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃` and at `n = 3` through
  `Φ_three_eval_ne_zero_of_Ψ₃`, neither of which needs a resultant or an identity
  `A·Φₙ + B·ΨSqₙ = Δ`"*, and that is no longer how the two instances are proved.**  Both
  `eval_Φ_two_ne_zero_of_root_ΨSq` (`EllipticCurves.Torsion.DoublingSurjective`) and
  `eval_Φ_three_ne_zero_of_root_ΨSq` (`EllipticCurves.Torsion.TriplingSurjective`) now route
  through `eval_Φ_ne_zero_of_eval_ΨSq_ne_zero` and the `IsCoprime` instances of
  `EllipticCurves.DivisionPolynomial.Coprime`, which **do** rest on `Δ`-certificates — in exchange
  for dropping `[IsAlgClosed F]` and `(2 : F) ≠ 0` from both statements.  The two certificate-free
  proofs are retained verbatim as `example`s beside them, so neither route left the tree.
  **The economy of *this* file is unaffected**: its interface is still the pointwise statement, it
  still asks for no certificate, and `Coprime` is still not in its import closure.

## Main definitions

* `WeierstrassCurve.Affine.HasXCoordFormula`: the multiplication-by-`n` coordinate formula at an
  affine point where `ΨSqₙ` does not vanish, as a predicate on `(W, n)`.

## Main statements

* `WeierstrassCurve.Affine.natDegree_Φ_sub_C_mul_ΨSq`: `Φₙ − C x₀ · ΨSqₙ` has degree `n²`.
* `WeierstrassCurve.Affine.exists_eval_Φ_eq_of_splits`: `x₀` solves `Φₙ(x) = x₀·ΨSqₙ(x)` whenever
  `Φₙ − C x₀ · ΨSqₙ` splits; `WeierstrassCurve.Affine.exists_eval_Φ_eq` is the algebraically closed
  case.
* `WeierstrassCurve.Affine.eval_Φ_ne_zero_of_isCoprime`: `IsCoprime (Φₙ, ΨSqₙ)` implies the
  pointwise no-common-root hypothesis.
* `WeierstrassCurve.Affine.exists_nsmul_some_of_hasXCoordFormula_of_root` and
  `WeierstrassCurve.Affine.exists_nsmul_eq_some_of_hasXCoordFormula_of_root`: the finite-level
  layer — a root of `Φₙ − x₀·ΨSqₙ` with a point of `W` above it makes `x₀`, respectively a named
  affine point, an `n`-fold multiple, **over an arbitrary field and in every characteristic**.
* `WeierstrassCurve.Affine.exists_nsmul_some_of_hasXCoordFormula`: every `x₀` is the `x`-coordinate
  of an `n`-fold multiple.
* **`WeierstrassCurve.Affine.exists_nsmul_eq_of_hasXCoordFormula`** and
  **`WeierstrassCurve.Affine.nsmul_surjective_of_hasXCoordFormula`**: the headline, `[n]` is
  surjective on `E(F̄)`.

Every public declaration of this file is listed above.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, Corollary 4.9.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## Solving the multiplication-by-`n` equation for the `x`-coordinate -/

/-- The auxiliary polynomial `Φₙ − x₀·ΨSqₙ`, whose roots are the `x`-coordinates of the points `P`
with `x(nP) = x₀`, is monic of degree `n²`: `Φₙ` is monic of degree `n²` while `ΨSqₙ` has degree at
most `n² − 1`.

**No hypothesis on `(n : F)`**: both Mathlib inputs, `natDegree_Φ` and `natDegree_ΨSq_le`, are
unconditional. -/
lemma natDegree_Φ_sub_C_mul_ΨSq {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    (W.Φ n - C x₀ * W.ΨSq n).natDegree = n ^ 2 := by
  have hpos : 0 < n ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hn)
  have hΦ : (W.Φ (n : ℤ)).natDegree = n ^ 2 := by
    rw [W.natDegree_Φ (n : ℤ), Int.natAbs_natCast]
  have hΨ : (C x₀ * W.ΨSq (n : ℤ)).natDegree < n ^ 2 := by
    refine lt_of_le_of_lt ((natDegree_C_mul_le x₀ _).trans (W.natDegree_ΨSq_le (n : ℤ))) ?_
    rw [Int.natAbs_natCast]
    exact Nat.sub_lt hpos one_pos
  rw [natDegree_sub_eq_left_of_natDegree_lt (hΦ ▸ hΨ), hΦ]

/-- **A value of `x` solves the multiplication-by-`n` equation as soon as `Φₙ − x₀·ΨSqₙ` splits.**
The polynomial has degree `n²` by `natDegree_Φ_sub_C_mul_ΨSq`, so it is not constant and a
splitting witness produces a root — Mathlib's `Polynomial.Splits.exists_eval_eq_zero`.

⚠️ This is the **only** thing `exists_eval_Φ_eq` below ever used its algebraic closure for, and the
hypothesis is a statement about one explicit polynomial at one explicit `x₀`, so a caller over a
field that is not algebraically closed can discharge it on a named curve.  Over a splitting field
of `Φₙ − x₀·ΨSqₙ` it holds by construction; transporting a *conclusion* back down to the base field
is a descent problem and is not this lemma's business.

⚠️ `Polynomial.Splits` takes **one** argument in this Mathlib — the `RingHom` form is gone.  A
`Splits` obligation appearing inside a proof as `(f.map φ).Splits` says something about the API that
consumes it, not about the arity of the predicate. -/
lemma exists_eval_Φ_eq_of_splits {n : ℕ} (hn : n ≠ 0) (x₀ : F)
    (hsplits : (W.Φ n - C x₀ * W.ΨSq n).Splits) :
    ∃ x : F, (W.Φ n).eval x = x₀ * (W.ΨSq n).eval x := by
  have hdeg : (W.Φ (n : ℤ) - C x₀ * W.ΨSq (n : ℤ)).degree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mp
      (by rw [natDegree_Φ_sub_C_mul_ΨSq hn]; exact Nat.pos_of_ne_zero (pow_ne_zero 2 hn))).ne'
  obtain ⟨x, hx⟩ := hsplits.exists_eval_eq_zero hdeg
  rw [eval_sub, eval_mul, eval_C, sub_eq_zero] at hx
  exact ⟨x, hx⟩

/-- **Every value of `x` solves the multiplication-by-`n` equation.**  Over an algebraically closed
field the degree-`n²` polynomial `Φₙ − x₀·ΨSqₙ` has a root.

The splitting hypothesis of `exists_eval_Φ_eq_of_splits`, discharged by `IsAlgClosed.splits`. -/
lemma exists_eval_Φ_eq [IsAlgClosed F] {n : ℕ} (hn : n ≠ 0) (x₀ : F) :
    ∃ x : F, (W.Φ n).eval x = x₀ * (W.ΨSq n).eval x :=
  exists_eval_Φ_eq_of_splits hn x₀ (IsAlgClosed.splits _)

/-- The bridge from the Bézout form of coprimality to the pointwise no-common-root hypothesis used
below.  `IsCoprime (W.Φ n) (W.ΨSq n)` at general `n` is issue `#1184`; the surjectivity engine
below needs only the conclusion.  ⚠️ This sentence used to end *"and is available in this tree only
at `n = 2` (`isCoprime_Φ_two_Ψ₂Sq`) and `n = 3` (`isCoprime_Φ_three_ΨSq_three`)"*.  Those two are
still the only instances over an **arbitrary commutative ring**; over a field of characteristic
`≠ 2` on an elliptic curve it holds at every `n : ℤ`
(`EllipticCurves.Torsion.CoprimeAdjacent`, downstream of this file).

⚠️ This docstring used to end *"…which both available instances obtain without any Bézout
certificate"*.  That was true of the instances as they were merged and is no longer true of them:
both now route through `EllipticCurves.DivisionPolynomial.Coprime`, which is what let them drop
`[IsAlgClosed F]` and `(2 : F) ≠ 0`.  The certificate-free proofs survive as `example`s beside
them.  Nothing in this file changed with them, and `#1184` is still not in its import closure.

⚠️ **The proof used to unfold the Bézout witness by hand** — `obtain ⟨a, b, hab⟩ := h`, then
`congrArg (Polynomial.eval x)` and eight `eval_*` rewrites to reach `1 = 0`.  Not a step of that
used `Φ` or `ΨSq`: it was a reproof of Mathlib's `Polynomial.aeval_ne_zero_of_isCoprime`,
specialised in the statement only.  `#1255` replaced it by a derivation from that lemma, which
needs **no new import** — it is already in scope here.

⚠️ **The statement stays specialised to `(Φₙ, ΨSqₙ)`, and that was a decision** (`#1255`, item 2),
not an oversight.  An environment census — walking `env.constants` and testing `getUsedConstants`
over every value *and* type — reports **zero** consumers, so there is no call site pulling either
way and the tie is broken on reading.  Two reasons for the specialised form: it is named for what
it bridges, `#1184`'s `IsCoprime` into the `hroot` hypothesis below, and it reads that way at the
call site; and the general form is already a public lemma in this tree,
`Polynomial.eval_ne_zero_of_isCoprime` (`EllipticCurves.DivisionPolynomial.Coprime`), which this
file **cannot see** — restating it here would turn a specialisation into a literal duplicate, which
is the worse of the two shapes.  See *"The de-duplication question, decided"* in that file for the
priced alternatives. -/
lemma eval_Φ_ne_zero_of_isCoprime {n : ℕ} (h : IsCoprime (W.Φ n) (W.ΨSq n)) {x : F}
    (hx : (W.ΨSq n).eval x = 0) : (W.Φ n).eval x ≠ 0 := by
  have h' := Polynomial.aeval_ne_zero_of_isCoprime (S := F) h x
  simp only [Polynomial.coe_aeval_eq_eval] at h'
  exact h'.resolve_right (not_not.mpr hx)

/-! ## The coordinate formula as a hypothesis -/

section Formula

variable [DecidableEq F]

/-- **The multiplication-by-`n` coordinate formula**, as a predicate.  It says that at an affine
point `(x, y)` of `W` at which `ΨSqₙ` does not vanish, the multiple `n • (x, y)` is affine with
`x`-coordinate `Φₙ(x)/ΨSqₙ(x)`.

This is the one index-dependent input of the surjectivity engine below.  It holds at **every** `n`
over a field of characteristic `≠ 2`: `hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`, issue `#251`).  ⚠️ That file imports this one, so the general
form is not available *here*; `hasXCoordFormula_two` (`EllipticCurves.Torsion.DoublingSurjective`)
and `hasXCoordFormula_three` (`EllipticCurves.Torsion.TriplingSurjective`) remain the instances a
consumer below `NsmulOrder` can reach. -/
def HasXCoordFormula (W : Affine F) (n : ℕ) : Prop :=
  ∀ ⦃x y : F⦄ (h : W.Nonsingular x y), (W.ΨSq n).eval x ≠ 0 →
    ∃ (y' : F) (h' : W.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • Point.some x y h = Point.some _ y' h'

/-! ## Surjectivity of multiplication by `n` -/

/-- **A root of `Φₙ − x₀·ΨSqₙ` carrying a point of `W` above it makes `x₀` an `n`-fold
`x`-coordinate**, over an arbitrary field.

This is the engine's two closure uses promoted to arguments.  The merged
`exists_nsmul_some_of_hasXCoordFormula` below obtains `x` from `exists_eval_Φ_eq` and `y` from
`exists_equation`, and those are the only two
places `[IsAlgClosed F]` enters anywhere in this file; supplied by hand, the remaining seven lines
need no closure.

⚠️ The two uses are **dependent** — the point is sought above the *root* the first use produced — so
they cannot be bolted onto the merged statement as two independent hypotheses.  `x` and `y` are
arguments, and that is the whole design content of the finite-level form.

⚠️ **`h2` and `hn` are gone as well, and that is not an oversight.**  In the merged statement
`(2 : F) ≠ 0` is consumed only by `exists_equation` and `n ≠ 0` only by the degree count inside
`exists_eval_Φ_eq`.  Promote both uses and neither hypothesis has a consumer left: what is stated
here holds in every characteristic, at every `n`, over every field. -/
theorem exists_nsmul_some_of_hasXCoordFormula_of_root [W.IsElliptic] {n : ℕ}
    (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) {x₀ x y : F} (hxy : W.Equation x y)
    (hx : (W.Φ n).eval x = x₀ * (W.ΨSq n).eval x) :
    ∃ (P : W.Point) (y' : F) (h' : W.Nonsingular x₀ y'), n • P = Point.some x₀ y' h' := by
  have hne : (W.ΨSq n).eval x ≠ 0 := fun h0 => hroot x h0 (by rw [hx, h0, mul_zero])
  have hns : W.Nonsingular x y := equation_iff_nonsingular.mp hxy
  obtain ⟨y', h', hP⟩ := hform hns hne
  have hxx : (W.Φ n).eval x / (W.ΨSq n).eval x = x₀ := by
    rw [hx, mul_div_assoc, div_self hne, mul_one]
  subst hxx
  exact ⟨Point.some x y hns, y', h', hP⟩

/-- **A named affine point is an `n`-fold multiple**, over an arbitrary field, given a root of
`Φₙ − x₀·ΨSqₙ` with a point of `W` above it.

`exists_nsmul_some_of_hasXCoordFormula_of_root` pins the `x`-coordinate; what is left is the sign
ambiguity `nP = ±Q`, which `Point.X_eq_iff` resolves and `−P` absorbs.  This is the form a
certificate on a named curve wants: it produces `n • P = Q` for the `Q` the caller names, rather
than for some point sharing its `x`-coordinate.

⚠️ `exists_nsmul_eq_of_hasXCoordFormula` below is **not** routed through this lemma.  Its `none`
branch has nothing in common with it, and the indirection would hide the two-case split that is the
point of that proof. -/
theorem exists_nsmul_eq_some_of_hasXCoordFormula_of_root [W.IsElliptic] {n : ℕ}
    (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀) {x y : F}
    (hxy : W.Equation x y) (hx : (W.Φ n).eval x = x₀ * (W.ΨSq n).eval x) :
    ∃ P : W.Point, n • P = Point.some x₀ y₀ hQ := by
  obtain ⟨P, y', h', hP⟩ := exists_nsmul_some_of_hasXCoordFormula_of_root hroot hform hxy hx
  rcases (Point.X_eq_iff (h₁ := h') (h₂ := hQ)).mp rfl with hc | hc
  · exact ⟨P, by rw [hP, hc]⟩
  · exact ⟨-P, by rw [smul_neg, hP, hc, neg_neg]⟩

/-- **Every value of `x` is the `x`-coordinate of an `n`-fold multiple.**  Over an algebraically
closed field of characteristic `≠ 2`, given the coordinate formula at `n` and the absence of a
common root of `Φₙ` and `ΨSqₙ`, every `x₀` is `x(nP)` for some point `P`.

`exists_nsmul_three_some` (`EllipticCurves.Torsion.TriplingSurjective`) is its only direct consumer;
at `n = 2` the tree consumes `exists_nsmul_eq_of_hasXCoordFormula` below instead. -/
theorem exists_nsmul_some_of_hasXCoordFormula [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ}
    (hn : n ≠ 0) (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) (x₀ : F) :
    ∃ (P : W.Point) (y' : F) (h' : W.Nonsingular x₀ y'), n • P = Point.some x₀ y' h' := by
  obtain ⟨x, hx⟩ := exists_eval_Φ_eq (W := W) hn x₀
  obtain ⟨y, hyeq⟩ := exists_equation (W := W) h2 x
  exact exists_nsmul_some_of_hasXCoordFormula_of_root hroot hform hyeq hx

/-- **Multiplication by `n` is surjective on `E(F̄)`**, given the coordinate formula at `n`.  The
point at infinity is `n • 0`; an affine `Q` is matched by `exists_nsmul_some_of_hasXCoordFormula`,
which pins the `x`-coordinate, leaving the sign ambiguity `nP = ±Q` that `Point.X_eq_iff` resolves
and `−P` absorbs. -/
theorem exists_nsmul_eq_of_hasXCoordFormula [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0)
    (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) (Q : W.Point) : ∃ P : W.Point, n • P = Q := by
  rcases Q with _ | ⟨x₀, y₀, hQ⟩
  · exact ⟨0, smul_zero n⟩
  · obtain ⟨P, y', h', hP⟩ := exists_nsmul_some_of_hasXCoordFormula h2 hn hroot hform x₀
    rcases (Point.X_eq_iff (h₁ := h') (h₂ := hQ)).mp rfl with hc | hc
    · exact ⟨P, by rw [hP, hc]⟩
    · exact ⟨-P, by rw [smul_neg, hP, hc, neg_neg]⟩

/-- **Multiplication by `n` is surjective on `E(F̄)`**, stated as `Function.Surjective` — the form
`EllipticCurves.Torsion.Divisible`'s `torsionSmulHom_surjective` consumes.  `nsmul_two_surjective`
and `nsmul_three_surjective` are its two instances. -/
theorem nsmul_surjective_of_hasXCoordFormula [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0)
    (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0)
    (hform : HasXCoordFormula W n) : Function.Surjective fun P : W.Point => n • P :=
  exists_nsmul_eq_of_hasXCoordFormula h2 hn hroot hform

end Formula

end WeierstrassCurve.Affine
