/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Topology.SeparatedMap

/-!
# A separated map: Hausdorff source, composites, and the clopen locus where two lifts agree

**The title read *A continuous separated map into a Hausdorff space has Hausdorff source, and
composites* until 2026-09-12**, and it was exact for the three statements it described; it is
shortened rather than extended because a fourth conjunct would have put it over the hundred-column
limit this repository keeps.

Material for `Mathlib/Topology/SeparatedMap.lean`; see `README.md` on the mirror tree. Four
statements, and each is something that file does not have: `IsSeparatedMap.t2Space`,
`IsSeparatedMap.comp`, `IsSeparatedMap.of_comp` and `IsSeparatedMap.isClopen_eqLocus` below.
**The opening read *One statement, and it is the direction that file does not have* and named only
the first, until 2026-09-08**, when the two composition statements were added, **and read *Three
statements, and each is a direction that file does not have* and named three, until 2026-09-12**,
when the fourth was and *direction* stopped being exact of all of them; both records are kept
because each sentence was exact for the file it described.

**The first three are directions Mathlib lacks at `v4.32.0`; the fourth is a conjunction it forms
and does not name, and the difference is worth stating rather than hiding.** The version is the
one `lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997`, and the first half is decided by an enumeration rather
than by a `grep`: over the environment of `import Mathlib` at that rev, exactly **19**
non-internal declarations have a **type** mentioning the constant `IsSeparatedMap`. **A statement
of any of the three directions has to mention that constant in its own type**, whatever it is
called and whatever namespace is open, so that enumeration decides the claim where a name-keyed
scan would only narrow it; they are, in four groups:

* **five characterisations of it** — `isSeparatedMap_iff_nhds`, `isSeparatedMap_iff_disjoint_nhds`,
  `isSeparatedMap_iff_isClosed_diagonal`, `isSeparatedMap_iff_isClosedMap` and
  `isSeparatedMap_iff_isClosedEmbedding`, the last two through `toPullbackDiag`;
* **six concluding it** — `T2Space.isSeparatedMap`, `Function.Injective.isSeparatedMap`,
  `IsCoveringMap.isSeparatedMap`, and the three transport statements `IsSeparatedMap.comp_left`,
  `IsSeparatedMap.comp_right` and `IsSeparatedMap.pullback`;
* **seven consuming it** — `IsSeparatedMap.isClosed_eqLocus`, `IsSeparatedMap.eq_of_comp_eq`,
  `IsSeparatedMap.eqOn_of_comp_eqOn`, `IsSeparatedMap.const_of_comp`,
  `IsSeparatedMap.constOn_of_comp`, `IsLocalHomeomorph.continuous_lift` and
  `IsLocalHomeomorph.monodromy_theorem`;
* **one biconditional with `T2Space`** — `t2space_iff_isSeparatedMap`, which reads
  `T2Space X ↔ IsSeparatedMap fun _ ↦ y` for a fixed `y`, at a constant map.

**None of the six that conclude it is either composition direction below**, for the reason the
paragraph on `IsSeparatedMap.comp_left` and `IsSeparatedMap.comp_right` gives, and
`IsSeparatedMap.pullback` concludes about `Function.Pullback.snd`; and **not one of them
concludes `T2Space` of the source of a separated map**, the only two that write `T2Space` at all
being `T2Space.isSeparatedMap`, where it is a hypothesis, and the biconditional above, whose
`IsSeparatedMap` is at a map that forgets its source.

**An enumeration keyed on a constant closes the name escape and not the characterisation escape,
and here the residue is measured rather than argued.** `IsSeparatedMap` is a `def` and the five
characterisations above are published equivalent forms, so a lemma could carry one of the three
directions through one of them and mention the constant nowhere — *if the diagonal of the pullback
is closed and `Y` is `T2Space` then `X` is* would serve a consumer perfectly and no scan keyed on
`IsSeparatedMap` would see it. Of the **35** non-internal declarations of that environment whose
type mentions `Function.pullbackDiagonal` or `Function.Pullback`, **none** mentions `T2Space`, so
that route is empty too and the enumeration above decides the claim after all.

**That opening read *The first three are directions Mathlib lacks; the fourth is a conjunction
Mathlib forms and does not name, and the difference is worth stating rather than hiding.* until
2026-09-21**, with no version and no instrument for its first half; `git show
c6bfc1f:Oka/Topology/SeparatedMap.lean` carries the retired wording at `:25–26`, wrapped after
*does*. **The claim is unchanged and only its warrant is**, which is why the retired wording is
kept here rather than struck: the second half was bounded when it was written — the two Mathlib
declarations are named below, and the `grep` for `isClopen_eqLocus` is quoted — and the first half
was a universal over *directions* that no `grep` could have reached.

`IsSeparatedMap.isClosed_eqLocus` and `IsLocallyInjective.isOpen_eqLocus` are both Mathlib's, in
that file, with exactly the binders below; what is not there is the **conjunction under a name**.
It is formed inline at `Mathlib/Topology/SeparatedMap.lean:206`, the only line of that file
carrying `IsClopen`, inside `IsSeparatedMap.eq_of_comp_eq`, and the term there —
`⟨sep.isClosed_eqLocus h₁ h₂ he, inj.isOpen_eqLocus h₁ h₂ he⟩` — is character for character the
whole of the proof below. **So this statement is not new mathematics and does not claim to be**,
and a grep for `isClopen_eqLocus` over `.lake/packages/mathlib/Mathlib/` returns nothing at the
pinned revision. What it buys is a caller that wants the clopen set itself rather than the
equality on a preconnected space that Mathlib derives from it, which is what the consumer named
below wants.

`Mathlib/Topology/SeparatedMap.lean` has the converse, `T2Space.isSeparatedMap` — a map out of a
Hausdorff space is separated, for any target — and the constant-map biconditional
`t2space_iff_isSeparatedMap`, which says `T2Space X` is separatedness of `fun _ : X ↦ y`. Neither
gives the statement below, and the biconditional is close enough to be worth saying why: it reads
separatedness of a map that forgets its source, so it recovers Hausdorffness from a *constant*
map, where what is wanted here is Hausdorffness from a map with a Hausdorff target.

**And it has two composition statements, neither of which is either of the two below.**
`IsSeparatedMap.comp_left` makes `g ∘ f` separated from `f` separated **and `g` injective**, and
`IsSeparatedMap.comp_right` makes `f ∘ g` separated from `f` separated and `g` continuous **and
injective**. Both spend an injectivity, which is what lets them ask nothing of the other map;
`IsSeparatedMap.comp` below asks separatedness of both maps and injectivity of neither, and
`IsSeparatedMap.of_comp` asks nothing at all of the second map — not continuity, not injectivity,
not separatedness, and not even a topology on its target, which is a `Sort` here as it is in
`IsSeparatedMap`'s own binders. A `git grep` for `IsSeparatedMap` outside
`Mathlib/Topology/SeparatedMap.lean` returns two lines at the commit that adds this, in
`Mathlib/Topology/Homotopy/Lifting.lean` and `Mathlib/Topology/Covering/Basic.lean`, and neither
is a composition statement.

Upstreaming to `Mathlib/Topology/SeparatedMap.lean` costs that file **no** new imports — its
closure of 615 Mathlib modules already contains the one import below, which is that file itself,
measured with `python3 scripts/import_cost.py Oka/Topology/SeparatedMap.lean`.

## Why here and not beside the consumer

The statement this makes possible is about `IsClosedMap.isCoveringMap_of_isLocalHomeomorph` in
`Oka/Topology/Covering/Basic.lean`, and that is not where this belongs. `README.md`'s mirror-tree
section says to **split by destination, not by subject**, and the destination is decided by the
imports: `Mathlib/Topology/SeparatedMap.lean`
publicly imports `Mathlib/Topology/Separation/Hausdorff.lean`, so it already has `t2_separation`
and this statement costs it nothing, whereas `Mathlib/Topology/Separation/Hausdorff.lean` — where
`Topology.IsEmbedding.t2Space` and the other transfers of the Hausdorff axiom live — does not
import `IsSeparatedMap` and could not hold this without a new edge in the direction that file's

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
own imports run against. `Mathlib/Topology/Covering/Basic.lean` is not a destination at all: the
statement mentions no covering map.

**`IsSeparatedMap.isClopen_eqLocus` answers to the same paragraph and its consumer is a different
one.** At the commit that adds it, what consumes it is
`ComplexAnalytic.AnalyticSpace.isClopen_eqLocus_base_of_isLocalIso` in
`Oka/AnalyticSpace/ClopenEqLocus.lean` — the one place in this repository where the conjunction
is wanted as a set. The destination argument is unchanged and needs no rerun: it asks only
`IsSeparatedMap`, `IsLocallyInjective` and `IsClopen`, which are that Mathlib file's own two
notions and its own public import of `Mathlib/Topology/Connected/Clopen.lean`, so the import cost
of upstreaming it is nil for the same reason and by the same measurement.

## The proof, and the case split is the whole of it

`IsSeparatedMap f` separates two points with the **same** image; a Hausdorff target separates two
points with **different** images, by pulling back a separation downstairs. Those are the two
cases of `f x = f y`, and in the first the hypothesis is the goal — `T2Space`'s field and
`IsSeparatedMap`'s conclusion are the same existential, so no repackaging is needed. Continuity is
spent once, in the second case, on the two preimages being open.

**`IsSeparatedMap.comp` is the same case split with the target's Hausdorffness replaced by `g`'s
separatedness**, and it is the same proof read one hypothesis weaker: two points of `X` with the
same image under `g ∘ f` either have the same image under `f`, where `f`'s separatedness is the
goal, or different ones, where `g`'s separates the two images and the preimages under `f` separate
the points. Continuity of `f` is spent in exactly the one place it is spent above.
`IsSeparatedMap.of_comp` needs no case split and no topology: two points with the same image under
`f` have the same image under `g ∘ f`, so the hypothesis applies to them directly.

**The heading above is about the three statements that predate 2026-09-12 and not about the file.**
`IsSeparatedMap.isClopen_eqLocus` has no case split and no argument of its own — it is the pair of
two Mathlib lemmas, one per half of `IsClopen` — and what is worth saying about it is which of its
hypotheses does which half, which its own docstring says.

## Main results

- `IsSeparatedMap.t2Space`: **a continuous separated map into a Hausdorff space has Hausdorff
  source.**
- `IsSeparatedMap.comp`: **a composite of two separated maps is separated**, when the first is
  continuous.
- `IsSeparatedMap.of_comp`: **and the first factor of a separated composite is separated**, with
  no hypothesis whatever on the second — its target is not even asked to be a topological space.
- `IsSeparatedMap.isClopen_eqLocus`: **the locus where two continuous lifts of a map agree is
  clopen**, when the map they lift along is separated and locally injective.

## What is not here

* **No converse, and no biconditional — although one holds.** The converse is Mathlib's
  `T2Space.isSeparatedMap`: it asks `T2Space` of the *source*, gives `IsSeparatedMap f` for any
  target, and asks neither `[T2Space X]` nor `Continuous f`. Paired with `IsSeparatedMap.t2Space`,
  whose proof spends both, it gives `IsSeparatedMap f ↔ T2Space E` under those two hypotheses.
  That `Iff` is not stated here: each direction is what a caller uses, and its right-hand side is
  a class, which an `Iff` cannot present to instance search.
* **The biconditional that fails is the one with `[T2Space X]` dropped, and it fails forwards.**
  `Function.Injective.isSeparatedMap` is Mathlib's and makes an injective map separated whatever
  its source, so the identity of a space that is not Hausdorff is a separated map whose source is
  not Hausdorff.
* **This bullet read *Nothing about `IsLocallyInjective`* until 2026-09-12**, and what it said in
  full was: *"**Nothing about `IsLocallyInjective`**, the dual notion
  `Mathlib/Topology/SeparatedMap.lean` introduces alongside `IsSeparatedMap`, and nothing about the
  covering maps that satisfy both. The one application in this repository composes this with
  `IsCoveringMap.isSeparatedMap`, which is Mathlib's and is in
  `Mathlib/Topology/Covering/Basic.lean`."* **The first half is closed by
  `IsSeparatedMap.isClopen_eqLocus`**, which asks `IsLocallyInjective` of the same map it asks
  `IsSeparatedMap` of. **The second half stands**: nothing here is about covering maps, and the
  sentence about `IsCoveringMap.isSeparatedMap` still describes the one application that composes
  along that route. The record is kept because the bullet was exact for the file it described.
* **No `instance`.** The *named* hypotheses of all four are explicit arguments and none is a
  class, so instance search could not fire on any of them; a caller supplies them.
  `IsSeparatedMap.t2Space` does carry an instance argument, `[T2Space X]` on the target, and it is
  not one of them: what blocks the `instance` attribute is `hsep` and `hf`, which nothing can
  synthesise.
* **No converse of `IsSeparatedMap.of_comp`, and `IsSeparatedMap.comp` cannot drop `hg`.**
  Separatedness of `f` alone does not give separatedness of `g ∘ f`: take `f` the identity of a
  space that is **not** Hausdorff — separated, because `Function.Injective.isSeparatedMap` asks
  nothing of the source — and `g` the constant map to a point. Then `g ∘ f` is that constant map,
  which `t2space_iff_isSeparatedMap` makes separated exactly when the space is Hausdorff, so it is
  not. Nothing below states that failure; this is a remark about which hypotheses are load-bearing
  and not a theorem of this file.
* **Nothing about the second factor.** `IsSeparatedMap.of_comp` reads separatedness off the
  composite for `f` and says nothing about `g`, and no statement below does: a separated `g ∘ f`
  with `f` surjective does make `g` separated, and that is not proved here because nothing in this
  repository asks for it.
-/

/-- **A continuous separated map into a Hausdorff space has Hausdorff source.**

Two points of the source are separated by the hypothesis when they have the same image, and by the
preimages of a separation downstairs when they do not. `Topology.IsEmbedding.t2Space` is the same
shape at a stronger hypothesis on the map; this asks only that the map separate the points of its
own fibres. -/
theorem IsSeparatedMap.t2Space {E : Type*} {X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] {f : E → X} (hsep : IsSeparatedMap f) (hf : Continuous f) : T2Space E := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases h : f x = f y
  · exact hsep x y h hxy
  · obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation h
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hf, hv.preimage hf, hxu, hyv, huv.preimage _⟩

/-- **A composite of two separated maps is separated**, when the first is continuous.

Two points of the source with the same image under `g ∘ f` either have the same image under `f`,
where `hf` separates them, or different ones, where `hg` separates the two images and their
preimages separate the points. **Neither map is asked to be injective**, which is what separates
this from Mathlib's `IsSeparatedMap.comp_left` and `IsSeparatedMap.comp_right`: each of those
spends an injectivity and asks nothing of the other map. -/
theorem IsSeparatedMap.comp {X Y : Type*} {Z : Sort*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : Y → Z} (hf : IsSeparatedMap f) (hg : IsSeparatedMap g)
    (hcont : Continuous f) : IsSeparatedMap (g ∘ f) := by
  intro x₁ x₂ he hne
  rcases eq_or_ne (f x₁) (f x₂) with h | h
  · exact hf x₁ x₂ h hne
  · obtain ⟨u, v, hu, hv, h₁, h₂, huv⟩ := hg _ _ he h
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hcont, hv.preimage hcont, h₁, h₂, huv.preimage f⟩

/-- **The first factor of a separated composite is separated**, with no hypothesis whatever on the
second — not continuity, not injectivity, not separatedness, and not a topology on its target.

Two points with the same image under `f` have the same image under `g ∘ f`, so the hypothesis
applies to them unchanged; `g` is an explicit argument only because it appears in neither the
hypothesis's binder nor the conclusion in a position elaboration could read it from. -/
theorem IsSeparatedMap.of_comp {X : Type*} {Y Z : Sort*} [TopologicalSpace X] {f : X → Y}
    (g : Y → Z) (h : IsSeparatedMap (g ∘ f)) : IsSeparatedMap f :=
  fun x₁ x₂ he hne ↦ h x₁ x₂ (congrArg g he) hne

/-- **The locus where two continuous lifts agree is clopen**, when the map they lift along is
separated and locally injective.

`IsSeparatedMap.isClosed_eqLocus` and `IsLocallyInjective.isOpen_eqLocus` are both Mathlib's, with
exactly these binders; this is their conjunction under a name. **Mathlib forms that conjunction
and does not name it** — the term below is character for character the anonymous constructor
inside `IsSeparatedMap.eq_of_comp_eq`, which then feeds it to `IsClopen.eq_univ` and concludes
that the two lifts are equal on a preconnected space. A caller that wants the **set** rather than
that conclusion has nothing to cite, which is what this statement is for. **A caller whose source
is preconnected should use Mathlib's conclusion and not this**: `IsSeparatedMap.eq_of_comp_eq` is
strictly more useful there, and the clopen set is only worth naming where preconnectedness is not
available and the decomposition it gives is the point. The module docstring's
`## Why here and not beside the consumer` names what consumes it here.

**The two hypotheses are dual and neither is redundant.** `IsSeparatedMap f` closes the locus and
`IsLocallyInjective f` opens it; `Mathlib/Topology/SeparatedMap.lean`'s own module docstring says
so in terms of the diagonal of `f.Pullback f`, which is a closed embedding for the first and an
open embedding for the second. Dropping either leaves a set with one half of the conclusion, and
the statement below has no form with one hypothesis that is not already one of those two
lemmas. -/
theorem IsSeparatedMap.isClopen_eqLocus {X Y A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    {f : X → Y} {g₁ g₂ : A → X} (sep : IsSeparatedMap f) (inj : IsLocallyInjective f)
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (he : f ∘ g₁ = f ∘ g₂) :
    IsClopen {a | g₁ a = g₂ a} :=
  ⟨sep.isClosed_eqLocus h₁ h₂ he, inj.isOpen_eqLocus h₁ h₂ he⟩
