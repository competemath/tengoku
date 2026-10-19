/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Algebra.Category.Grp.FilteredColimits
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Abelian
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Limits
import Tengoku.Seed.Topology.Sheaves.Abelian
import Tengoku.LanaOka.Oka.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stalks of sheaves of modules on a topological space, and exactness

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Stalk.lean`; see `README.md` on the
mirror tree. Mathlib's `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` puts a
`Module (R.stalk x)` structure on the stalk of a presheaf of modules; this file is the other
half, the *functor* and what it detects.

**The mathematics here is Mathlib's.** `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` already
says that a short complex of sheaves of abelian groups on a space is exact exactly when it is
exact on every stalk. What this file adds is the transfer of that to sheaves of *modules*,
which is one step — `SheafOfModules.toSheaf` is faithful, and
`CategoryTheory.Functor.reflects_exact_of_faithful` needs nothing more than that.

## The seam this file exists to cross, and the one instance it costs

`TopCat.Sheaf C X` is a `def` for `CategoryTheory.Sheaf (Opens.grothendieckTopology X) C`, and
`SheafOfModules.toSheaf` lands in the second spelling while every stalk lemma is stated in the
first. **The two `Category` instances are equal by `rfl`** — checked — but instance search does
not cross them, so a statement about `TopCat.Sheaf.forget ⋙ TopCat.Presheaf.stalkFunctor` is not
found at a goal spelled the other way round. This is the same shape as the site spelling recorded
in `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`'s docstring: **a definitional equality that
`rfl` sees and the discrimination tree does not.**

**What the seam costs this file is one instance:
`CategoryTheory.Limits.PreservesFiniteLimits (TopCat.Sheaf.stalkFunctor X x)`.** Delete it,
re-elaborate the file, and the `SheafOfModules.stalkFunctorAddCommGrp` instance below it fails
with `failed to synthesize PreservesFiniteLimits (Sheaf.stalkFunctor X x)`.

`(TopCat.Sheaf.stalkFunctor X x).Additive` is a transport across the same seam, and it too is
genuinely not found by search — `inferInstance` on it fails if the declaration below is removed.
But **deleting it alone leaves the file compiling**, because `PreservesZeroMorphisms` already
follows from `PreservesFiniteLimits`; only when *both* go does
`TopCat.Sheaf.exact_iff_stalk_exact` additionally lose
`failed to synthesize (stalkFunctor X x).PreservesZeroMorphisms`. So it is kept as API for a
consumer that wants additivity, not as part of the cost, and it is labelled that way below.

An earlier version of this file also carried an `Abelian (CategoryTheory.Sheaf
(Opens.grothendieckTopology X) AddCommGrpCat)` transport and said here that the seam made that
instance unfindable. **That was false in the direction that matters:**
`CategoryTheory.sheafIsAbelian` (`Mathlib/CategoryTheory/Sites/Abelian.lean`) is stated for a
general site and applies at this one directly, and Mathlib's `Abelian (TopCat.Sheaf C X)` is
itself `inferInstanceAs` of it — so the spelling called unreachable is the primitive one. The
transport is recorded here rather than silently dropped because the negative is the kind a
reader would act on: **do not re-add it.**

At the point of use the site still has to be spelled so that it matches. For an
`AlgebraicGeometry.LocallyRingedSpace` `Y`, whose `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`
lives over `Opens.grothendieckTopology ↑Y.toPresheafedSpace`, the space to pass is
`TopCat.of ↑Y.toPresheafedSpace` and **not** `Y.toTopCat`; with `Y.toTopCat` the statement
elaborates and then fails to find `PreservesZeroMorphisms`.

## Main definitions

- `TopCat.Sheaf.stalkFunctor`: the stalk at `x` of a sheaf of abelian groups on `X`, as a
  functor, at the `CategoryTheory.Sheaf` spelling of the site.
- `SheafOfModules.stalkFunctorAddCommGrp`: the stalk at `x` of a sheaf of modules on `X`, as a
  functor to `AddCommGrpCat`.

## Main results

- `TopCat.Sheaf.exact_iff_stalk_exact`: Mathlib's criterion at the other spelling of the site.
- `SheafOfModules.exact_of_stalk_exact`: **a short complex of sheaves of modules is exact if it
  is exact on every stalk.**
- `SheafOfModules.stalk_exact_of_exact`: the converse.
- `SheafOfModules.exact_iff_stalk_exact`: the two as one biconditional.

## What the converse costs here, and what it needs before it can go upstream

**`SheafOfModules.stalk_exact_of_exact` is a transfer, and what it transfers is this
repository's and not Mathlib's.** The converse of `SheafOfModules.exact_of_stalk_exact` needs
`SheafOfModules.toSheaf` to be *right* exact as well as left exact. At `v4.32.0` — the revision
`lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997` — **Mathlib has no lemma making it right exact,
under any name**; the half it does have is
`CategoryTheory.Limits.PreservesFiniteLimits (SheafOfModules.toSheaf R)`
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean:118`). **What is missing is missing from
Mathlib and not from this repository**: `Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean`
declares `SheafOfModules.preservesFiniteColimits_toSheaf`, right exactness of the same functor
and an instance, under `[CategoryTheory.HasWeakSheafify]` and
`[CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective]` hypotheses this file's site
satisfies, and has done since `1bc5d33` — two days older than this file. **So the converse is a
transfer and not a theorem someone has to prove**, and until 2026-09-22 what kept it out of
*this* file was that this file did not import that one.

**The import is made here, and it costs one Mathlib module.** This file's Mathlib closure goes
**1584 to 1585** and the module added is `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits` —
the other two of that file's three Mathlib imports are in this closure already, which is a
membership and not a subtraction. `scripts/import_cost.py` refuses this file, whose mirror
target `Mathlib/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` does not exist, so both figures
are `--target` runs by hand over this file's four Mathlib imports with and without that
file's three. On the `Oka` side the import adds **one** module and no cycle —
`Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean` imports nothing from `Oka`, which
`scripts/module_graph.py --upstream` gives as **0** — and **104** modules are downstream of
this one and pay it. **The obstruction this passage carried for a month cost one module.**

**That makes the measurement below an upstreaming obstruction and not a to-do, which is why
this is a section of its own and no longer a `## What is not here` bullet.**
`Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean` sits on a mirror path whose Mathlib
target exists, and the scan says the right exactness is not in that target: so the converse
cannot be written into `Mathlib/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` until that file
has landed upstream, and the list below is the evidence that the obstruction is real
rather than an oversight. **This passage read *so
the converse is a theorem someone has to prove and not a transfer* until 2026-09-22**;
`git show ef9e5d2:Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` carries it at `:84–85`,
wrapped after *has to*. It was written on 2026-08-22 in this file's first commit, two days after
the instance that refutes it. **One file points at this passage** —
`Oka/Algebra/Category/ModuleCat/Sheaf/PullbackExact.lean` — and **its pointer is not repaired
here**: taxis #2135 is repairing that paragraph on a branch of its own, and this push leaves
that file alone while it is in flight. Nothing else in this tree leans on the retired sentence.
**That last clause has an instrument and here it is**: `grep -rn "someone has to"` over this
repository's `.lean` and `.md` files returns **three** matching lines, all in this file and all
inside this section — the verdict above, this record quoting what it replaced, and this
sentence, whose backticked command carries the pattern it publishes. **The sentence publishing
the instrument is one of the lines the instrument matches**, and that is why the figure is
given in *lines*: `grep -rn` reports matching lines and not occurrences, so a rewrap that moved
a second occurrence onto a line of its own would change the number with no word of the prose
changing — where a tool is keyed on lines, the wrapping of the file is part of the claim.

**The converse is not needed by the intended consumer**, which is why this file carried the
other direction alone for the month between its first commit and this one: an argument
that a functor preserves kernels compares the canonical map with the kernel and checks it is an
isomorphism, which needs the direction proved here plus `PreservesFiniteLimits`, both of which
are present.

**What the `inferInstance` probe decides, and what it does not — starting with the environment
it is taken in.** The probe is still run and still fails **under `import Mathlib` at the
revision above**, on `CategoryTheory.Limits.PreservesFiniteColimits (SheafOfModules.toSheaf R)`
and on `(SheafOfModules.toSheaf R).PreservesHomology`, with the left-exact instance above
succeeding beside them as its control. **In this repository's own environment both succeed** —
the first from `Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean` and the second from
Mathlib's `[PreservesFiniteLimits F] [PreservesFiniteColimits F] : F.PreservesHomology`
(`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:61`) once the first is there — so
**a probe report that does not name its environment states the opposite of the truth here**, and
the environment is part of the instrument in the same way the filter below is. **What it
decides is that no `instance` is registered**, which is a fact about how an API is spelled
rather than about what is in it: the same statement
carried as a `theorem` under any name at all would leave the probe failing exactly as it does,
and this passage's claim is about contents. So the instrument behind the claim is a scan of
**types** over the environment of `import Mathlib` at that rev — **15** of its constants have a
type mentioning `SheafOfModules.toSheaf`, **3044** have a type mentioning one of
`CategoryTheory.Limits.PreservesFiniteColimits`, `CategoryTheory.Limits.PreservesColimit`,
`CategoryTheory.Limits.PreservesColimitsOfShape`,
`CategoryTheory.Limits.PreservesColimitsOfSize`,
`CategoryTheory.Functor.PreservesHomology`, `CategoryTheory.Functor.PreservesEpimorphisms`,
`CategoryTheory.Limits.IsColimit` or `CategoryTheory.Limits.HasColimit` — the positive control,
which says the scan is pointed at something there is in quantity — and **0** have a type
mentioning both.

**The 15 are few enough to list, and a complete list is a stronger warrant than a zero.** Two
are simp lemmas for the functor (`SheafOfModules.toSheaf_obj_obj`,
`SheafOfModules.toSheaf_map_hom`) and one names its composite with
`CategoryTheory.sheafToPresheaf` (`SheafOfModules.toSheafCompSheafToPresheafIso`); two are
faithfulness and additivity
(`SheafOfModules.instFaithfulSheafAddCommGrpCatToSheaf`,
`SheafOfModules.instAdditiveSheafAddCommGrpCatToSheaf`); three are finite **limits**
(`SheafOfModules.instPreservesFiniteLimitsSheafAddCommGrpCatToSheaf`,
`…instPreservesFiniteLimitsFunctorOppositeAddCommGrpCatCompSheafToSheafSheafToPresheaf`,
`…instPreservesFiniteLimitsSheafAddCommGrpCatCompSheafOfModulesSheafificationToSheaf`); three
are reflection
(`PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf`,
`PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1`,
`PresheafOfModules.instReflectsFiniteLimitsSheafOfModulesSheafAddCommGrpCatToSheaf`); and four
are on the `PresheafOfModules` side of sheafification
(`PresheafOfModules.sheafificationCompToSheaf`,
`PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm`,
`PresheafOfModules.toPresheaf_map_sheafificationHomEquiv`,
`PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app`). **Nothing about colimits,
epimorphisms, homology or right exactness**, which is the verdict stated as a list. The grouping
is a reading of that list and the list is the measurement; a reader who thinks one of them
implies right exactness by a route not seen here should say which.

**Two of them are written elided, the reason is the column limit, and the elision costs
a check.** Those two generated instance names are **99** and **100** characters long, so a
backticked one of them on an indented line cannot fit the 100 columns `linter.style.longLine`
enforces — the second is over the limit before a backtick is added. Each has exactly one dot,
so eliding its leading namespace leaves no dot behind, and a dotless `…decl` is in
`scripts/check_docstring_names.py`'s **third** population, which that script reads and does not
resolve: the two are cited here and **not checked by anything**. **This passage adds three
dotless occurrences and three distinct ones**, and only two of the three are the citations —
the third is the shape name in the sentence before this one, which is written in the notation it
describes and so is an occurrence of it. That is taxis #2069's class, met here as a
consequence of a name length rather than of a style choice. **Both were resolved by hand
against `scripts/DumpEnvNames.lean`'s dump before being written**, and what they are is sayable
without the name: the first is finite limits for the composite of `SheafOfModules.toSheaf` with
`CategoryTheory.sheafToPresheaf`, the second finite limits for
`PresheafOfModules.sheafification` composed with `SheafOfModules.toSheaf`. Both statements are
`PreservesFiniteLimits` of a composite and neither mentions a colimit, which is the only thing
the verdict needs of them; the others are written out and every one is checked.

**The control's size depends on which names are counted internal and the verdict does not.** The
**3044** filters with `Lean.Name.isInternalDetail`; filtering with `Lean.Name.isInternal`
instead, over the same environment, gives **3145**. The **15** and the **0** are the
same under either, which is the property that makes the control worth printing.

**There is no third spelling to chase, and the three that do not exist are written here without
backticks.** CategoryTheory.Functor.RightExact, CategoryTheory.Functor.PreservesFiniteColimits
and CategoryTheory.Limits.PreservesCokernel are what a reader would try next, and **the three
are not in Mathlib at this rev** — the classes that exist are the two spelled above. They are
bare because `scripts/check_docstring_names.py` resolves every backticked dotted name against
the environment of `Oka` and would report all three, correctly: that they resolve to nothing is the
content of the sentence, and an entry in `scripts/docstring-names-ignore.txt` would buy silence at
the price of the same spelling being exempt tree-wide.

**Until 2026-09-22 this passage was invisible to `scripts/mathlib_absence.py`, and it is now three
of that scan's rows**, all three inside it: the version-bearing claim at the head, the sentence
that locates the missing right exactness in Mathlib rather than in this repository, and the one
retiring the three spellings that do not exist. `--file` on this module prints those three and
nothing else, and this module contributed none before, so the scan's headline gains **three** rows
and **one** file. **Naming them by quotation rather than by description would make this sentence a
fourth row and false as written** — the scan matches text, so a repair that quotes what it counts
is counted. *Mathlib has X and not Y* matches none of the six shapes it looks for, so the
strongest absence claim in this directory sat in none of the buckets the census reconciles, while
the pointer at it from `Oka/Algebra/Category/ModuleCat/Sheaf/PullbackExact.lean` is itself a row —
the census could see the pointer and not its target. The wording above is chosen to match,
deliberately; the scan is not changed, and its six shapes are spellings by design.

**That bullet read *Mathlib has `PreservesFiniteLimits (SheafOfModules.toSheaf R)`
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean`) and **not**
`CategoryTheory.Limits.PreservesFiniteColimits` — measured, `inferInstance` fails on both that
and `CategoryTheory.Functor.PreservesHomology`* until 2026-09-22**, with no revision named in
it and with an instance probe standing as the warrant for a claim about contents;
`git show 3f26e9d:Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` carries the retired wording
at `:79–87`, wrapped after *on both that*. **Round 1 of that push changed only the warrant;
round 2 changed the verdict, for the reason at the head of this section.**

**All of the above was the first bullet of `## What is not here` until 2026-09-22**, when
`SheafOfModules.stalk_exact_of_exact` was proved here and the converse stopped being absent.
`git show 34f83e4:Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` carries it at
`:79–221`, opening *The converse of `SheafOfModules.exact_of_stalk_exact`.* and indented
two columns as a list item. **Nothing measured in it moved with it**: the scan, the list,
the two controls, both of the records above and the census clause are the landing that wrote
them, reproduced and not re-taken, and a reader can check that by diffing this section against
that bullet with the two columns stripped.

## What is not here

* **Isomorphism detected on stalks for sheaves of modules.**
  `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` plus `SheafOfModules.toSheaf` reflecting
  isomorphisms gives it, and the only obstacle met was naming the underlying presheaf morphism
  of a morphism of sheaves across the `TopCat.Sheaf` `def`: the `deriving Category` on that `def`
  makes it an `CategoryTheory.InducedCategory.Hom`, on which the `val` projection is not a
  field. It is left to whoever needs it, with that warning.
* **Anything analytic.** This file is general theory and imports nothing from this development.
-/

open CategoryTheory Limits TopologicalSpace TopCat

universe u

variable {X : TopCat.{u}} {R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **The stalk at `x`, as a functor on sheaves of abelian groups on `X`**, at the
`CategoryTheory.Sheaf` spelling of the site.

This is `TopCat.Sheaf.forget` followed by `TopCat.Presheaf.stalkFunctor`; it is an `abbrev` so
that the instances Mathlib proves about that composite remain visible. -/
noncomputable abbrev TopCat.Sheaf.stalkFunctor (X : TopCat.{u}) (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

/-- The stalk functor is additive. A transport across the site spelling — the statement is
Mathlib's, at `TopCat.Sheaf.forget ⋙ TopCat.Presheaf.stalkFunctor`, and search does not find it
here — but **not one this file needs**: its `PreservesZeroMorphisms` comes from
`PreservesFiniteLimits` below. Kept as API. -/
noncomputable instance (x : X) : (TopCat.Sheaf.stalkFunctor X x).Additive :=
  inferInstanceAs ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive)

/-- **A short complex of sheaves of abelian groups on a space is exact exactly when it is exact
on every stalk.**

This is `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` with the site spelled
`CategoryTheory.Sheaf (Opens.grothendieckTopology X)` rather than `TopCat.Sheaf`. The proof is
the Mathlib lemma applied — the two statements are definitionally equal — but the restatement is
not decoration: a `rw` with the Mathlib lemma fails on a goal in this spelling, with
`did not find an occurrence of the pattern`. -/
theorem TopCat.Sheaf.exact_iff_stalk_exact
    (S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) :
    S.Exact ↔ ∀ x : X, (S.map (TopCat.Sheaf.stalkFunctor X x)).Exact :=
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

/-- **The stalk at `x`, as a functor on sheaves of modules on `X`, valued in abelian groups.**

The module structure on the stalk is
`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`'s and is available on the object; the functor to
abelian groups is what detects exactness, which is what this file is for. **The name carries
`AddCommGrp` because the unqualified `SheafOfModules.stalkFunctor` is the module-valued stalk
functor**, in `Oka/Algebra/Category/ModuleCat/Sheaf/PullbackStalk.lean` — that is the one a
reader expects under the plain name, and it is what the base-change theorem is a statement
about. -/
noncomputable abbrev SheafOfModules.stalkFunctorAddCommGrp (x : X) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ TopCat.Sheaf.stalkFunctor X x

/-- **A short complex of sheaves of modules on a space is exact if it is exact on every stalk.**

The forgetful functor to sheaves of abelian groups is faithful, and a faithful functor between
abelian categories that preserves zero morphisms reflects exactness — that is
`CategoryTheory.Functor.reflects_exact_of_faithful`, and it is the whole proof once the site
spellings agree. **The converse is `SheafOfModules.stalk_exact_of_exact` below**, and the two
together are `SheafOfModules.exact_iff_stalk_exact`.

**This docstring read *The converse is true and is not here; see the module docstring for what it
needs and why the intended consumer does not* until 2026-09-22**, when the converse was proved
here; `git show 34f83e4:Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` carries the retired
wording at `:297–298`, wrapped after *what it*. **What the module docstring accounts for has
changed with it**: it named what the converse needed and now names what it costs. -/
theorem SheafOfModules.exact_of_stalk_exact (S : ShortComplex (SheafOfModules.{u} R))
    (h : ∀ x : X, (S.map (SheafOfModules.stalkFunctorAddCommGrp x)).Exact) : S.Exact :=
  Functor.reflects_exact_of_faithful (SheafOfModules.toSheaf R) S
    ((TopCat.Sheaf.exact_iff_stalk_exact (S.map (SheafOfModules.toSheaf R))).mpr h)

/-- **The converse: a short complex of sheaves of modules that is exact is exact on every
stalk.**

**The proof is the mirror image of `SheafOfModules.exact_of_stalk_exact`'s.** That one
*reflects* exactness along `SheafOfModules.toSheaf R`, which is faithful; this one *maps* along
it, which needs it to be exact, and then takes the other direction of the same Mathlib
biconditional. `CategoryTheory.ShortComplex.Exact.map` asks for
`CategoryTheory.Functor.PreservesLeftHomologyOf` and
`CategoryTheory.Functor.PreservesRightHomologyOf` at this complex, which
`CategoryTheory.Functor.PreservesHomology` supplies, and Mathlib gives that only for a functor
that is `CategoryTheory.Limits.PreservesFiniteLimits` **and**
`CategoryTheory.Limits.PreservesFiniteColimits`. **The second of those is
`SheafOfModules.preservesFiniteColimits_toSheaf`, which is this repository's and not
Mathlib's** — see the section above on what this costs and what upstreaming it needs.

**Measured**: delete this file's `Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean` import and
this proof, and nothing else in the file, fails — with
`failed to synthesize (toSheaf R).PreservesLeftHomologyOf S`, which is the left half asking for
the colimits the deleted module supplies. -/
theorem SheafOfModules.stalk_exact_of_exact (S : ShortComplex (SheafOfModules.{u} R))
    (h : S.Exact) (x : X) : (S.map (SheafOfModules.stalkFunctorAddCommGrp x)).Exact :=
  (TopCat.Sheaf.exact_iff_stalk_exact _).mp (h.map (SheafOfModules.toSheaf R)) x

/-- **A short complex of sheaves of modules on a space is exact exactly when it is exact on every
stalk.**

The name is `TopCat.Sheaf.exact_iff_stalk_exact`'s one namespace down, and the two halves are
kept as declarations of their own rather than as `.mp` and `.mpr` projections: `mpr` is
`SheafOfModules.exact_of_stalk_exact`, which is older than this biconditional and has consumers,
and `mp` is `SheafOfModules.stalk_exact_of_exact`, which takes `x` as an argument where this
takes it under a `∀`. -/
theorem SheafOfModules.exact_iff_stalk_exact (S : ShortComplex (SheafOfModules.{u} R)) :
    S.Exact ↔ ∀ x : X, (S.map (SheafOfModules.stalkFunctorAddCommGrp x)).Exact :=
  ⟨fun h x => SheafOfModules.stalk_exact_of_exact S h x, SheafOfModules.exact_of_stalk_exact S⟩
