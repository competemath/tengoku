/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Certificate curves: the shared fixtures the non-vacuity blocks run on

Almost every file in this development ends in a `section Nonvacuity` block whose job is to show
that the results above it are not vacuous — that the hypotheses can be met on a curve that exists.
Those blocks all need the same handful of objects, and each one used to build its own `private`
copy. ⚠️ **Measured on `5e5768c`, the last commit before any stage of this consolidation landed**:
**164** `IsElliptic` instances across **119** files, of which **142** have a byte-identical
four-line proof naming `Δ`, `b₂`, `b₄`, `b₆`, `b₈`; **146** curve definitions over **five**
distinct curves, **142** of them in characteristic zero; and **72** copies of `AlgebraicClosure ℚ`
under six different names.

⚠️ **Every count in this docstring is that baseline, not a description of the tree today.** This
module exists to delete what it counts, so each stage of the migration makes the figures smaller by
design; a stage landing is not a defect in this paragraph and the numbers must not be "corrected"
to the current tree, which would only make them stale again at the next stage. Any figure added
here later should name its commit for the same reason.

This module holds the shared layer. ⚠️ **Its declarations exist only to make non-vacuity
certificates non-vacuous. They are not part of the mathematical API**, and no result about
Weierstrass curves in general should be stated in terms of them.

## The design, and the two decisions in it

**The curves are polymorphic in the base ring.** The same five literals occur in the tree both over
`ℚ` and over `AlgebraicClosure ℚ` (and, at four sites, over a finite field), so a definition taking
`[CommRing R]` serves every base at once and one definition replaces a whole column of copies.

**One `IsElliptic` instance per curve, over `[Field F] [CharZero F]`.** Each of the five
discriminants — `64`, `−27`, `−432`, `2304`, `−4096` — is a nonzero integer, so characteristic zero
is the exact hypothesis, and it covers the `ℚ` and `AlgebraicClosure ℚ` sites with a single
instance rather than one per base type.

⚠️ **The finite-field certificates are deliberately NOT served here, and there are FOUR of them.**
`EllipticCurves.FunctionField.NegYGaloisGroup` certifies over `ZMod 2` on purpose — its curve
docstring records that `negYAlgEquiv_ne_one` is exactly what would fail for `y² = x³ + …` in
characteristic `2` — and `EllipticCurves.FunctionField.NegYGalois`,
`EllipticCurves.FunctionField.NegYInvolution` and `EllipticCurves.FunctionField.MulByNDegreeTower`
do the same over `ZMod 2`, `ZMod 2` and `ZMod 5`. In full, so that no sweep has to rediscover it:

* `FunctionField/NegYGaloisGroup.lean`, `exampleCurveNegYGalois`, `⟨0,0,1,0,0⟩`, over
  `exampleFieldNegYGalois`;
* `FunctionField/NegYGalois.lean`, `exampleCurveChar2`, `⟨0,0,1,0,0⟩`, over `ZMod 2`;
* `FunctionField/NegYInvolution.lean`, `exampleCurveTwo`, `⟨0,0,1,0,0⟩`, over `ZMod 2`;
* `FunctionField/MulByNDegreeTower.lean`, `exampleCurveFive`, `⟨0,0,0,-1,0⟩`, over `ZMod 5`.

All four prove `IsElliptic` by `decide +kernel`. ⚠️ `NegYGalois` and `NegYGaloisGroup` are two
different files with near-identical names, both in `FunctionField/` and both certifying over
`ZMod 2`; the quotation above belongs to `NegYGaloisGroup`, and `exampleFieldNegYGalois` is that
file's own `private abbrev` for `ZMod 2`.

⚠️ **Each row is a file plus a declaration name and carries NO line number, on purpose. Do not add
them back.** The rows did carry `file.lean:NNN`, and three of the four went stale in one commit.
The `#1373` sweep added a single `import` line to the top of each of the 98 files it migrated, so
every line above such a file's `section Nonvacuity` block moved by `+1` and everything below it by
that block's own delta: `393 → 391`, `468 → 466`, `281 → 282`, while `NegYGaloisGroup` — the one
file of the four the sweep does not touch — stayed at `279`. ⚠️ **Nothing on this board detects
that.** A build, `lake lint`, the `#907` name-keyed comparator, the environment enumeration and the
`section Nonvacuity` source comparator are all silent on a docstring integer, so this list would
have gone on being wrong for exactly as long as someone trusted it — which is the one thing it
exists not to do. A declaration name resolves in one `grep -n` and never decays, and each row
already names the curve literal and the base, so the number was carrying nothing a reader could not
get more reliably without it. ⚠️ **The same reasoning applies to any `file.lean:NNN` anywhere in
this library while the migration is in flight**: name the declaration, not the line.

⚠️ **This is not the rule that governs the census below, and the two must not be conflated.** A
count is a historical measurement and is pinned precisely so that it is *not* corrected to the
current tree; an address is worth only what it resolves to. Do not read *"the numbers must not be
corrected"* as covering anything in this list.

Those bases are not of characteristic zero, so the instances below do not apply, and the missing
piece is an import: `Mathlib.FieldTheory.Finite.Basic` is what supplies `Field (ZMod p)` and makes
their `decide +kernel` proofs go through (checked, both directions). It is **not** imported here,
because this module is imported across the library and pulling a finite-field file into every one
of those import closures to serve four certificates is the wrong trade. **Those four keep their
local fixtures**, and a later sweep should not "finish the job" by deleting them: they are the only
positive-characteristic non-vacuity evidence on the `negY` front.

⚠️ **How that list came out one row short, because the same mistake is easy to repeat.** A grep for
`: Affine (ZMod` finds three of the four and misses `NegYGaloisGroup`, whose base is spelled through
an abbreviation; filtering on file names instead finds a different three. Enumerate every
`private … : Affine … := ⟨…⟩` in the tree, resolve each base through its own file's `abbrev`s, group
by the resolved base, and read **every** group — do not grep for the shape you expect. The same
recipe is what gives the counts quoted above, and running it is how the `(2 : F) ≠ 0` tally below
was corrected too.

## Imports

⚠️ This module is a **leaf**: it imports Mathlib and nothing from `EllipticCurves`, which is what
lets the ~119 non-vacuity blocks depend on it without being serialised behind each other. Keep it
that way. The Mathlib side is `Affine.Basic`, not `Affine.Point` — the file defines curves and
proves `IsElliptic`, and touches no point at all. Every consuming block imports `Affine.Point`
anyway for its own statements, so **this buys no build time**; it is here because a leaf that
~119 files import should carry the import it uses and no more.

## The base-changed `IsElliptic` instance: the one below, and the 18 it replaced

`EllipticCurves.Fixture.instIsEllipticBaseChange` below is the general
`[W.IsElliptic] → (W⁄F).IsElliptic` bridge for the whole library. ⚠️ **It mentions none of this
module's curves and is stated for an arbitrary elliptic curve and an arbitrary base change**; its
own docstring gives the copy-not-move reasoning and the second general instance it deliberately
leaves in place. The rest of this section is the measurement that produced it, kept because it is
the evidence, not the news.

⚠️ **Measured on `db0c65b` (`#1405`) and pinned to it**, in the sense the paragraph on counts above
sets out. It is an 18-row measurement at that commit and **must not be "corrected" to the current
tree**, where the number of `private` base-change fixtures is **0**: PR #535 (`#1397`) deleted the
first and `#1408` the other seventeen.

`WeierstrassCurve.baseChange` is a plain `def`, so `[(W⁄F).IsElliptic]` is **not** found by bare
`inferInstance` from `[W.IsElliptic]`, and eighteen files used to carry their own two-line
`private instance : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic := inferInstanceAs …` to bridge it.
`#1405` deleted each of the eighteen in turn and re-elaborated its own module with `lake env lean`.
**Four were load-bearing; fourteen were dead.**

| module whose fixture is load-bearing | `failed to synthesize` after deleting it |
| --- | --- |
| `Torsion.ThreePrimary` | **3**, all `IsElliptic (y2AddYEqX3 ℚ)⁄AlgClosedQ` |
| `TateModule.FreeThree` | **5**, all `IsElliptic (y2AddYEqX3 ℚ)⁄AlgClosedQ` |
| `FunctionField.MulByNPlacePullback` | **12** = **3** `IsElliptic` + **9** `IsDedekindDomain` |
| `FunctionField.MulByNTranscendence` | **4**, all `IsElliptic` |

The other fourteen re-elaborated at exit `0` with **zero** errors. ⚠️ **Group the failures by class
before quoting a count**: `MulByNPlacePullback`'s headline `12` is three quarters the *dependent*
class `IsDedekindDomain ((y2AddYEqX3 ℚ)⁄AlgClosedQ).CoordinateRing`, and
`grep -A1 "failed to synthesize" | grep "^  " | sort | uniq -c` is the whole recipe.

⚠️ **`private` hides a NAME, not an INSTANCE** (`#1397`). A `private instance` takes part in
typeclass resolution in every module downstream of the one that declares it. So a dead fixture is
dead because *another file's* `private` one is winning — measured, that was the supplier at all
fourteen, and at `db0c65b` this module declared no base-change instance for any of them to
reach.

⚠️ **`FunctionField.WeilPairingDeterminantCharacter` is the exception, and the exception is about
what was REACHABLE there, not about what won** (`#1413`). It is the one site of the eighteen with
the library's other general instance,
`WeierstrassCurve.Affine.CoordinateRing.instIsEllipticBaseChange`, in its `EllipticCurves`-import
closure — measured over all eighteen by import walk and, because that walker is under suspicion
(`#1292`), independently by elaboration: the name closes the goal there and is an
`Unknown constant` in `TateModule.Profinite`. ⚠️ **It is still not the supplier.** With that file's
own fixture deleted and the other seventeen in place, `#synth` there selects
`TateModule.DeterminantMod`'s `private` fixture, exactly as at the other thirteen — so the sentence
above holds at fourteen of fourteen. What is different is that this site had a public, general,
named instance to fall back on and the other thirteen did not, which is why PR #535 (`#1397`) could
delete this fixture and only this one: the deletion introduced no dependence on a `private` name.
⚠️ **Probe that at `7f2748d` or `db0c65b`, never here** — on this tree all eighteen fixtures are
gone, only general instances remain as candidates, and the answer flips to the public one. Note
also that this file reads `DivisionRing.toRatAlgebra` where the module declaring that general
instance reads `AlgebraicClosure.instAlgebra`, so it is likewise the one measured demonstration
that a **quantified** supplier matches across both of the `Algebra ℚ AlgClosedQ` paths the rule
below turns on.

**The rule, and it is exact on all eighteen.** A fixture is dead **iff** some other fixture-bearing
module in its `EllipticCurves`-import closure elaborates against the *same* `Algebra ℚ AlgClosedQ`
instance that it does. That instance is not unique in this library: the two `Torsion/` sites and
`FunctionField.MulByNTranscendence` read `AlgebraicClosure.instAlgebra`, while all thirteen
`TateModule/` sites and the other two `FunctionField/` ones read `DivisionRing.toRatAlgebra`
(measured site by site, one `synthInstance` probe per file). A fixture is
`inferInstanceAs`-elaborated against its own file's path and stops matching where the path flips,
so import distance alone does not decide this. ⚠️ **Two of the eighteen are exactly where those two
answers differ**: `TateModule.FreeThree` has two fixture modules in closure and
`FunctionField.MulByNPlacePullback` has one, and all three of those are on the other path, so
closure predicts both are dead and both are in fact load-bearing. Import distance has been the
stated argument for this family more than once; run the deletion instead.

⚠️ **Deleting the fourteen dead ones on their own would have been the wrong move, and that is why
`#1408` did something else.** Thirteen of them had nothing to fall back on but another file's
`private` fixture, which no import names and nothing pins — and inside `TateModule/` those
suppliers chain, rooted at `TateModule.FreeThree`. Removing those thirteen by themselves would have
traded thirteen independent two-line bridges for one hidden cascade. The fourteenth is the site
above with the public general instance also in closure, which is why PR #535 could remove it alone
and stop there. `#1408` removed the cascade instead, by putting the quantified instance below in a
module all eighteen already import — and a quantified instance is what the rule above says is
needed, since it matches at either `Algebra ℚ AlgClosedQ` path where a fixture matches at only one.

⚠️ **The leaf property is what makes that work, not what prevents it**, which is the opposite of
what two of the fixture docstrings used to say. Their argument was that the tree's only general
`(W⁄F).IsElliptic` sits in `EllipticCurves.FunctionField.GaloisFunctionField`, downstream of
`Torsion/`, and that `Fixtures` is a leaf importing no `EllipticCurves` module at all. Both clauses
are true; what is downstream is that instance's *address*, and the instance itself needs only
`baseChange`, `map` and `IsElliptic` — all Mathlib, all already in this module's closure.

⚠️ **What `#1408` did not change**: no `#916` certificate, no statement and no proof term. Root
`lake build EllipticCurves --wfail` is green at the same job count as before, and the four
positive-characteristic certificates listed at the top of this docstring are untouched — they are
`IsElliptic` over `ZMod 2` / `ZMod 5`, not base changes, and the instance below does not serve
them.

## Characteristic side-conditions

At `5e5768c` the `#916` blocks also carried **85** copies of `(2 : F) ≠ 0` and **64** of
`(3 : F) ≠ 0`, all proved `by norm_num` (84 and 63 of them inside a `section Nonvacuity`).
⚠️ **These two totals do not shrink as the migration proceeds — their proofs change instead.** A
migrated block still states its own `(2 : F) ≠ 0`, now over `AlgClosedQ` and discharged by
`two_ne_zero` rather than `norm_num`, so a reader who checks the counts sees them reproduce and a
reader who checks the *proofs* does not. That is why the tally is pinned above and why "all proved
`by norm_num`" is a statement about `5e5768c` only.

⚠️ Those two figures read `67` and `54` when this module was written, and the gap is the same
filtering mistake as above: those are the counts **over an abbreviated field name**
(`exampleField` 62, `exampleFieldBar` 2, `exampleFieldN` 2, `exampleFieldFibre` 1 = 67; and
52 + 1 + 1 = 54), silently dropping the **18** and **10** stated directly over `ℚ`. Only one of the
two needs anything here:

* `(2 : F) ≠ 0` is **already** Mathlib's `two_ne_zero` in a field of characteristic zero — nothing
  is added below for it, and a call site should use Mathlib's lemma directly.
* `(3 : F) ≠ 0` is not: `three_ne_zero` asks for a `NeZero 3` instance that is not found here, so
  `three_ne_zero_of_charZero` below supplies it.

## Naming

The curves are named after their Weierstrass equations rather than after the roles they play, since
several of them serve more than one role. What each is *for* is recorded in its own docstring; that
information came from the per-file docstrings this module replaces and must not be lost — in
particular `y2EqX3Add5X2Add4X` is the one with split rational `2`-torsion, and `y2AddYEqX3` is the
`n = 3` curve precisely because `y2EqX3SubX` has no rational `3`-torsion point.

The module is `EllipticCurves.Fixtures` (plural) and the namespace is `EllipticCurves.Fixture`
(singular). **That is deliberate and is settled**: Mathlib does not require the two to agree, a use
site reads as *the fixture curve* rather than as a reference to the collection, and the alternative
is a rename that buys nothing. ⚠️ It is recorded here because the mismatch has been raised twice;
it is not an oversight, and it should not be changed once files import this module.
-/

namespace EllipticCurves.Fixture

open WeierstrassCurve

/-- An algebraically closed field of characteristic zero, the base of most of the certificates in
this development. -/
abbrev AlgClosedQ : Type := AlgebraicClosure ℚ

/-- `y² = x³ − x = x(x − 1)(x + 1)`, of discriminant `64`.

This tree's standard `n = 2` certificate curve: its `2`-torsion is split and rational, so the
points `(0, 0)`, `(1, 0)`, `(−1, 0)` can be named over any base. ⚠️ It does **not** serve at
`n = 3` — `Ψ₃ = 3X⁴ − 6X² − 1` has no rational root, so none of its nine `3`-torsion points can be
named; `y2AddYEqX3` is the curve for that. -/
def y2EqX3SubX (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 0, -1, 0⟩

/-- `y² + y = x³`, of discriminant `−27`.

This tree's standard `n = 3` certificate curve: `Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 1)` factors, so `(0, 0)`
is a rational `3`-torsion point — which is exactly what `y2EqX3SubX` lacks. Over `ZMod 2` the same
equation is supersingular and has `a₁ = 0`, `a₃ = 1`, so `y ↦ −y − a₁x − a₃` is `y ↦ y + 1` and is
not the identity; that is the char-`2` certificate described in the module docstring, and it is not
served here. -/
def y2AddYEqX3 (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 1, 0, 0⟩

/-- `y² = x³ + 1`, of discriminant `−432`.

The certificate curve for the composite-index statements, which need a rational point `P` whose
double is also affine and rational: `(2, 3)` has order `6` and `[2](2, 3) = (0, 1)`. `y2EqX3SubX`
supplies no such pair, which is why `EllipticCurves.FunctionField.WeilPairingAlternatingConsumerN`
says of its own copy *"deliberately not `y² = x³ − x`"*. -/
def y2EqX3AddOne (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 0, 0, 1⟩

/-- `y² = x³ + 5x² + 4x = x(x + 1)(x + 4)`, of discriminant `2304`.

⚠️ Chosen for **split rational `2`-torsion**: the cubic factors over `ℚ` with three distinct roots
`0`, `−1`, `−4`, so all three nontrivial `2`-torsion points are rational. That is the entire content
of the four certificates that use it (`Torsion.TwoTorsion`, `Torsion.DoublingSurjective`,
`FunctionField.WeilPairingAlternatingTwoRational`,
`FunctionField.PullbackPrincipalityTwoRationalTorsion`), and substituting another curve there would
leave them green and vacuous. -/
def y2EqX3Add5X2Add4X (R : Type*) [CommRing R] : Affine R := ⟨0, 5, 0, 4, 0⟩

/-- `y² = x³ + 4x`, of discriminant `−4096`.

Chosen for the shape of its `Φ₂`: `b₂ = 0`, `b₄ = 8`, `b₆ = 0`, `b₈ = −16` give
`Φ₂ = X⁴ − 8X² + 16 = (X² − 4)²`, which vanishes at `x = 2` while the `2`-torsion point `T = (0, 0)`
has `x(T) = 0` — the root that discharges a halving from a polynomial identity in
`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN`. ⚠️ It shares `b₄`, `b₆`, `b₈` and
hence `Φ₂` with `y2EqX3Add5X2Add4X`, but **not** `Ψ₂Sq` (`4X³ + 16X` against `4X³ + 20X² + 16X`), so
`Ψ₃` and every evaluation differ; that file's docstring says the same and it is worth repeating
here, because the two curves look interchangeable and are not. -/
def y2EqX3Add4X (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 0, 4, 0⟩

section CharZero

variable (F : Type*) [Field F] [CharZero F]

/-- `(3 : F) ≠ 0` in a field of characteristic zero. Mathlib's `three_ne_zero` asks for a `NeZero 3`
instance that is not available here; the `2` case needs nothing, being Mathlib's `two_ne_zero`. -/
lemma three_ne_zero_of_charZero : (3 : F) ≠ 0 := by norm_num

/-- `Δ = 64 ≠ 0`. -/
instance : (y2EqX3SubX F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2EqX3SubX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Δ = −27 ≠ 0`. -/
instance : (y2AddYEqX3 F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2AddYEqX3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Δ = −432 ≠ 0`. -/
instance : (y2EqX3AddOne F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2EqX3AddOne, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

end CharZero

/-- **The base change `W⁄F` of an elliptic curve is elliptic.**

⚠️ **This is the only declaration in this module stated for an arbitrary curve**: it mentions
none of the five fixtures above and serves any `[W.IsElliptic]` over any base change. It lives
here because of this module's leaf property rather than in spite of it — see below.

`WeierstrassCurve.baseChange` is a plain `def`, so `[(W⁄F).IsElliptic]` is **not** found from
`[W.IsElliptic]` by bare `inferInstance`; `inferInstanceAs` on the unfolded `map` form is what
closes it. That two-line bridge used to be written out privately in **eighteen** `section
Nonvacuity` blocks, once per file. This instance replaces all of them (`#1408`).

⚠️ **It needs nothing from `EllipticCurves` and nothing beyond this module's two Mathlib imports**,
so the leaf property survives — and the leaf property is what makes the instance useful here. The
library's other general `(W⁄F).IsElliptic` is
`WeierstrassCurve.Affine.CoordinateRing.instIsEllipticBaseChange`, declared in
`EllipticCurves.FunctionField.GaloisFunctionField`; that module is downstream of `TateModule/` and
`Torsion/`, so fifteen of the eighteen sites could not reach it. Two docstrings used to give
exactly that as the reason their fixture could not move here, adding that *"`Fixtures` is a leaf
that imports no `EllipticCurves` module at all"*. Every clause was true and the conclusion was
backwards: what is downstream is the *address* of that instance, not the instance, which needs only
`baseChange`, `map` and `IsElliptic`.

⚠️ **Copied, not moved, and the reason is a dependency direction rather than tidiness.**
`instIsEllipticBaseChange` in `GaloisFunctionField` stays where it is. Relocating it would force
that module — a real API file — to `import EllipticCurves.Fixtures`, and everything in this module
exists to make non-vacuity certificates non-vacuous and is *not* part of the mathematical API. A
certificate layer may depend on the API; the API must not depend on the certificate layer. The two
are definitionally the same term, so no diamond arises and instance search simply picks one; the
root build is green with both. ⚠️ Two further reasons not to move it: this one is stated over
`[CommRing S] [CommRing F]` where that one sits in a field-and-`Algebra` `variable` block, so they
are not interchangeable in general; and that one's docstring carries the `#1277`
auto-generated-name finding, which is the only record of it.

⚠️ **Named rather than anonymous, for that same `#1277` reason.** Left anonymous, an instance whose
elaborated type mentions no constant of this project gets the lake **library** name appended by
`Lean.Elab.NameGen.mkBaseNameWithSuffix`, and the `defsWithUnderscore` linter does not report it
because `IsElliptic` is a `Prop`. -/
instance instIsEllipticBaseChange {S F : Type*} [CommRing S] [CommRing F] [Algebra S F]
    {W : WeierstrassCurve S} [W.IsElliptic] : (W⁄F).IsElliptic :=
  inferInstanceAs (W.map (algebraMap S F)).IsElliptic

end EllipticCurves.Fixture
