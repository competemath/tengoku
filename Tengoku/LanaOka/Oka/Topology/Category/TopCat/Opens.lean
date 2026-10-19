/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.CategoryTheory.Filtered.Final
import Tengoku.Seed.Topology.Category.TopCat.Opens

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `TopologicalSpace.Opens.map` is a final functor

Material for `Mathlib/Topology/Category/TopCat/Opens.lean`; see `README.md` on the mirror tree.
Upstreaming it adds `Mathlib.CategoryTheory.Filtered.Final`, which the argument below needs, to a
target whose closure is **707** Mathlib modules — **117** new ones, measured with
`scripts/import_cost.py`. **The obvious alternative destination is worse and that is measured
too**: the same declarations priced into `Mathlib/CategoryTheory/Filtered/Final.lean` cost it
**205**, so the finality of `Opens.map` belongs on the `Opens` side of the pair.

For a continuous map `f : X ⟶ Y`, taking preimages is a functor `Opens Y ⥤ Opens X`, and it is
**final**: colimits over `Opens Y` of a diagram pulled back along it agree with colimits over
`Opens X`. **At `v4.32.0` — the revision `lakefile.toml` pins, resolved by `lake-manifest.json`
to `81a5d257c8e410db227a6665ed08f64fea08e997` — Mathlib has no statement of it and no instance
that yields it.** The two halves are measured separately, because no one instrument reaches both
and neither of them is a `grep`.

* **No instance.** At that rev, `#synth (Opens.map f).Final`, for `f : X ⟶ Y` in `TopCat.{u}`
  under `variable`, in a file whose only `import` is `Mathlib`, **fails to synthesize**. That is
  the half no scan of source can decide: an instance stated at an arbitrary functor with some
  property would carry `(Opens.map f).Final` without writing `Opens.map` anywhere, and synthesis
  is what sees one. **The probe is live and the positive control says so**: the same `#synth`
  with this module imported as well prints `Opens.final_map f`, the instance below, whose full
  name is `TopologicalSpace.Opens.final_map`.
* **No statement.** Over the environment of `import Mathlib` at that rev, **no** non-internal
  declaration has a type mentioning both `CategoryTheory.Functor.Final` and
  `TopologicalSpace.Opens.map`, against **192** whose type mentions the first and **663** whose
  type mentions the second. A Mathlib
  statement *about* the finality of `Opens.map` has to name both constants in its own type, so
  that zero is a decision and not a narrowing, and the two controls are what make it one rather
  than a scan that found nothing because it was pointed nowhere.

**What is deliberately not claimed is that `(Opens.map f).Final` is unreachable from Mathlib**,
and the section below proves that it is reachable in three lines. The claim is about what Mathlib
**states** and what it **provides by synthesis**, which is what a caller meets; the content is
Mathlib's and is named there.

**That clause read *Mathlib does not have this — `grep -rn "Opens.map.*Final\|Final.*Opens.map"`
over all of Mathlib returns nothing* until 2026-09-21** — `git show
d4c49af:Oka/Topology/Category/TopCat/Opens.lean` carries it at `:21–22`, wrapped after *all*.
**The figure is right and it is the instrument that is retired**, for two reasons of different
weight. The `grep` is line-anchored, so a statement wrapped across two source lines is
invisible to it, which is the failure mode taxis #1712 records of `git log -S`; re-run over the
whitespace-normalised text of every one of the **8264** tracked `.lean` files under `Mathlib/`, with
the two tokens allowed 200 characters apart in either order, it still returns **0**, so the figure
survives the better `grep`. But the better `grep` only narrows. Of the three questions put to such
a scan, two are answered *yes* here — the thing denied can be spelled another way, and it can be
inherited from a binder the scan does not read — and a scan whose spelling cannot in principle
decide the claim is worse than carrying no instrument. The two above are what answer them.

## The content is that `Opens` is filtered

`CategoryTheory.Functor.final_of_exists_of_isFiltered` asks for two things, and over a lattice
both are immediate:

* every `U : Opens X` admits a map to some `(Opens.map f).obj V` — take `V = ⊤`, since
  `U ≤ f ⁻¹' ⊤`;
* any two parallel maps into `(Opens.map f).obj V` are coequalized after a further map — they are
  *equal*, because a preorder has at most one morphism between two objects, so this is
  `Subsingleton.elim`.

`IsFilteredOrEmpty (Opens Y)` is what carries the weight and it is Mathlib's: `Opens Y` has `⊤`
and binary joins.

## What it is for

`SheafOfModules.pullbackObjUnitToUnit` is an isomorphism when the functor between the sites is
final (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`), and for a morphism of
locally ringed spaces that functor is `Opens.map f.base`. So this instance is what makes
`f^* 𝒪_Y ≅ 𝒪_X` — and, with it, "pullback sends free sheaves to free sheaves" — available at all.
-/

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

end TopologicalSpace.Opens
