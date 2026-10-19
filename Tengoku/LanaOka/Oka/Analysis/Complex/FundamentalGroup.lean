/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Complex.CoveringMap
import Tengoku.Seed.Topology.Homotopy.Lifting
import Tengoku.Seed.Analysis.Convex.Contractible
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Log
import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fundamental group of the punctured plane is `ℤ`

Material for a **proposed** `Mathlib/Analysis/Complex/FundamentalGroup.lean`; see `README.md` on
the mirror tree, which allows a mirror path naming a Mathlib file that does not yet exist. Nothing
here is complex-analytic in this development's sense: no `ComplexAnalytic.AnalyticSpace`, no
analytification, and the statement makes sense to a reader who has never heard of Oka's theorem.

**Mathlib computes no fundamental group.** `Mathlib/AlgebraicTopology/FundamentalGroupoid/` builds
the groupoid and proves it trivial on `PUnit` and on contractible spaces, and there is no
non-trivial computation in the library — not for the circle, not for the punctured plane, not for
anything. This file is the first, and it is short for a reason that is worth recording rather than
leaving to be rediscovered: **two recent Mathlib files supply both halves and neither had been
used together.**

* `Complex.isAddQuotientCoveringMap_exp` (`Mathlib/Analysis/Complex/CoveringMap.lean`) presents
  `exp : ℂ → ℂ ∖ {0}` as a quotient covering map with group
  `AddSubgroup.zmultiples (2 * Real.pi * Complex.I)`.
* `IsAddQuotientCoveringMap.fundamentalGroupEquiv` (`Mathlib/Topology/Homotopy/Lifting.lean`)
  computes the fundamental group of the base of such a map as the opposite of its group, given
  that the total space is simply connected and path connected.

**Both hypotheses on `ℂ` are found by instance search and neither is supplied here**, through
`RealTopologicalVectorSpace.contractibleSpace` and `SimplyConnectedSpace.ofContractible`. What is
left is arithmetic: the group of periods is infinite cyclic on `2πi`.

## Why a proposed new file rather than either existing one

**Neither existing Mathlib file should absorb this, and the reason is measured rather than
felt.** By breadth-first search over `^(public )?import` with comments masked — the masking is not
tidiness, and `Oka/Analysis/Complex/CoveringMap.lean` records what an unmasked search costs:

* `Mathlib/Analysis/Complex/CoveringMap.lean` has a closure of **2071** modules, and these
  declarations would add **137** to it — 136 for `Mathlib.Topology.Homotopy.Lifting` and one for
  `Mathlib.Analysis.Convex.Contractible`. The other two imports above cost it **nothing**.
* `Mathlib/Topology/Homotopy/Lifting.lean` has a closure of **1439**, and they would add **769**.

So the second is worse by a factor of five, and the first is still a homotopy-theory import
dropped into an analysis file about covering maps. The union is **2208** modules, which is what
this file costs, and a Mathlib reviewer asked to put a fundamental-group computation somewhere
would ask for the new file rather than either. `README.md`'s rule is **split by destination, not
by subject**, and the destination here is a file that does not exist yet.

**This is deliberately not `Oka/Analysis/Complex/CoveringMap.lean`**, whose module docstring
claims — correctly, and this file does not change it — that its declarations cost their Mathlib
target *no* new imports. Adding these there would falsify that sentence, and a mirror file's
docstring is this development's dependency register.

## Main results

- `Complex.intEquivZMultiplesTwoPiI`: the group of periods of `Complex.exp` is infinite cyclic —
  `ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi * Complex.I)`, sending `1` to `2πi`.
- `Complex.fundamentalGroupPuncturedEquivInt`: **the fundamental group of `ℂ ∖ {0}` is `ℤ`**, at
  any basepoint and any point of its fibre under `Complex.exp`.
- `Complex.fundamentalGroupPuncturedOneEquivInt`: the same at the basepoint `1`, which is the form
  a consumer wants and the form in which the statement reads as its own name.
- `Complex.infinite_fundamentalGroupPunctured`: the group is infinite, so the results above are
  not an isomorphism onto a trivial group.

## What is not here

* **No classification of the coverings of `ℂ ∖ {0}`.** Knowing `π₁` does not produce them:
  building a covering space out of a `π₁`-set is absent from Mathlib at
  `81a5d257c8e410db227a6665ed08f64fea08e997` (`v4.32.0`, the revision `lakefile.toml` pins and
  `lake-manifest.json` resolves), as is any composition or cancellation lemma for
  `IsCoveringMap` — `Mathlib/Topology/Covering/Basic.lean` has only conjugation by a
  homeomorphism. **The revision is in that sentence and not in the one after it**, which is the
  stronger of the two forms this tree uses and the only one a reader who quotes the sentence
  carries away with it.
  **The first of the two absences is decided by an enumeration and not by a `grep`.** Over the
  environment of `import Mathlib` at that revision, **76** non-internal declarations have a
  **type** mentioning the constant `IsCoveringMap`, and **26** of them mention it in the
  conclusion once the binders are stripped. **Those 26 are every way the library has of producing
  a covering map**, whatever each is called and whatever namespace is open, which is the thing a
  name-keyed scan cannot say. **Two of the 26 mention `FundamentalGroup`,
  `Path.Homotopic.Quotient` or `MulAction` anywhere in the type, and both are about
  `IsQuotientCoveringMap`** — `IsQuotientCoveringMap.isCoveringMap` and
  `isQuotientCoveringMap_iff_isCoveringMap_and` — where the group acts on the **total** space.
  An action on the total space is the quotient construction and a `π₁`-set is not one, so the
  absence stands. **The control is the same scan asking for `IsSeparatedMap`, which returns 19**,
  the figure `Oka/Topology/SeparatedMap.lean` publishes for a claim of its own shape.
  **One of the 26 is worth naming because a reader who checks this meets it first**: the
  étale-space construction of `Mathlib/Topology/Sheaves/EtaleSpace.lean` makes a covering map out
  of a presheaf whose germ maps are bijective on a neighbourhood of each point. That is a locally
  constant sheaf, which is the *sheaf* avatar of a `π₁`-set and not a `π₁`-set; what stands
  between the two is an equivalence, and it is the equivalence that is missing here and not the
  construction. **It is named by its file and not by its declaration**, for the reason the
  *Nothing about the circle* bullet gives of `Mathlib/Topology/Covering/AddCircle.lean`: that
  module is in the import closure of nothing here, so its declaration name resolves against
  nothing and `scripts/check_docstring_names.py` reports it. **The scan does see it**,
  `import Mathlib` being the whole library — the two populations are different, and this is the
  sentence where that shows.
  **The clause carried the universal bare until 2026-09-22**, when this passage gave it the
  revision and the enumeration.
* **What is not absent is the fibre functor, and the sentence that used to close the bullet on the
  classification said it was.** That sentence read *Everything in
  `Mathlib/Topology/Homotopy/Lifting.lean` is the uniqueness half of the correspondence*, and at
  the pinned revision that file declares `IsCoveringMap.monodromyPerm` — a monoid hom from
  `FundamentalGroup X x` to the permutations of the fibre — and
  `IsCoveringMap.fundamentalGroupMulAction`, the `MulAction` of that group on the fibre which it
  gives. **That is the fibre of a covering read as a `π₁`-set: the forward direction of the
  correspondence, and not its uniqueness half.** What that bullet denies is the *reverse*
  direction, and the two are different statements. **This is corrected and not recorded.**
  `lakefile.toml`'s `rev` has read `v4.32.0` since this repository's first commit and no push has
  moved it, so both declarations were in the environment on 2026-08-31, when `ca56617` wrote the
  sentence; and `README.md`'s rule is that a clause false when it was written is corrected rather
  than dated.
* **Nothing about the circle.** `π₁(S¹) ≅ ℤ` is the same theorem through the covering
  `𝕜 → AddCircle p` of `Mathlib/Topology/Covering/AddCircle.lean`, but `Circle` in Mathlib is a
  submonoid of `ℂ` and the transport is a separate measurement that has not been made. It is not
  asserted to be two lines. **That covering is named by its file and not by its declaration on
  purpose**: the module is not in `Oka`'s import closure, so neither a declaration name from it
  nor the module name itself resolves against anything, and
  `scripts/check_docstring_names.py` reports both — which it did, on the first two heads of this
  file. A backticked *path* is checked by nothing and is the only form that passes here.
* **No basepoint independence.** `Complex.fundamentalGroupPuncturedEquivInt` takes both a
  basepoint and a point of its fibre because `IsAddQuotientCoveringMap.fundamentalGroupEquiv`
  does, and the isomorphism genuinely depends on the second — a different sheet conjugates it.
  That the ambiguity is invisible here, the target being abelian, is a fact about `ℤ` and not a
  theorem stated below.
-/

open AddSubgroup MulOpposite

namespace Complex

instance : Infinite (zmultiples (2 * Real.pi * Complex.I)) :=
  Infinite.of_injective (fun n : ℤ ↦ (⟨n • (2 * Real.pi * Complex.I), n, rfl⟩ :
      zmultiples (2 * Real.pi * Complex.I))) (by
    intro a b h
    simpa [sub_eq_zero, sub_smul, two_pi_I_ne_zero] using congrArg Subtype.val h)

/-- **The group of periods of `Complex.exp` is infinite cyclic**, generated by `2πi`.

`intEquivOfZMultiplesEqTop` needs the subgroup to be `Infinite`, which is the instance above and
is not automatic: it is the statement that `n ↦ n • 2πi` is injective, which is `two_pi_I_ne_zero`
together with `ℂ` being torsion free. -/
noncomputable def intEquivZMultiplesTwoPiI :
    ℤ ≃+ zmultiples (2 * Real.pi * Complex.I) :=
  intEquivOfZMultiplesEqTop
    (⟨2 * Real.pi * Complex.I, mem_zmultiples _⟩ : zmultiples (2 * Real.pi * Complex.I)) (by
      rw [eq_top_iff]
      rintro ⟨-, n, rfl⟩ -
      exact ⟨n, by ext; simp⟩)

/-- **The fundamental group of the punctured plane is `ℤ`.**

`Complex.isAddQuotientCoveringMap_exp` presents `exp : ℂ → ℂ ∖ {0}` as a quotient covering map
with group `AddSubgroup.zmultiples (2πi)`, and
`IsAddQuotientCoveringMap.fundamentalGroupEquiv` turns that into an isomorphism from the
fundamental group of the base onto the opposite of the group — the hypotheses that `ℂ` is simply
connected and path connected are found by instance search, through
`RealTopologicalVectorSpace.contractibleSpace` and `SimplyConnectedSpace.ofContractible`, and are
not supplied here. `MulOpposite.opMulEquiv` drops the opposite, which is available because the
group is commutative, and `Complex.intEquivZMultiplesTwoPiI` is the arithmetic.

**Both parameters are the ones `fundamentalGroupEquiv` takes.** The isomorphism depends on the
choice of `e`: a different sheet conjugates it, and only the target being abelian makes that
invisible. `Complex.fundamentalGroupPuncturedOneEquivInt` is the specialisation a consumer
wants. -/
noncomputable def fundamentalGroupPuncturedEquivInt (x : {z : ℂ // z ≠ 0})
    (e : (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ⁻¹' {x}) :
    FundamentalGroup {z : ℂ // z ≠ 0} x ≃* Multiplicative ℤ :=
  (Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e).trans
    (opMulEquiv.symm.trans (AddEquiv.toMultiplicative intEquivZMultiplesTwoPiI).symm)

/-- **The fundamental group of `ℂ ∖ {0}` at the basepoint `1` is `ℤ`**, which is the form in which
the statement reads as its own name.

The point of the fibre is `0`, since `exp 0 = 1`; the general statement is
`Complex.fundamentalGroupPuncturedEquivInt` and this is it at one basepoint, kept beside it rather
than replacing it because `AddSubgroup.zmultiples` is where the `ℤ` comes from and a statement at
a single basepoint hides that. -/
noncomputable def fundamentalGroupPuncturedOneEquivInt :
    FundamentalGroup {z : ℂ // z ≠ 0} ⟨1, one_ne_zero⟩ ≃* Multiplicative ℤ :=
  fundamentalGroupPuncturedEquivInt ⟨1, one_ne_zero⟩ ⟨0, by simp⟩

/-- **The fundamental group of `ℂ ∖ {0}` is infinite**, so the isomorphisms above are not onto a
trivial group.

A `≃*` cannot be vacuous, but it can be uninteresting: the type of
`Complex.fundamentalGroupPuncturedEquivInt` gives a reader no way to see that the source is not
the trivial group, and this is what says it. -/
theorem infinite_fundamentalGroupPunctured (x : {z : ℂ // z ≠ 0})
    (e : (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ⁻¹' {x}) :
    Infinite (FundamentalGroup {z : ℂ // z ≠ 0} x) :=
  Infinite.of_injective _ (fundamentalGroupPuncturedEquivInt x e).symm.injective

end Complex
