/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Tengoku.Seed.Algebra.Category.Grp.Abelian
public import Tengoku.Seed.CategoryTheory.ConcreteCategory.EpiMono
public import Tengoku.Seed.CategoryTheory.Sites.Abelian
public import Tengoku.Seed.CategoryTheory.Sites.EpiMono
public import Tengoku.LanaOka.Oka.Algebra.Category.Grp.EpiMono

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An epimorphism of sheaves of abelian groups is locally surjective

`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` says that a morphism of sheaves valued in a
concrete category is locally surjective exactly when it is an epimorphism, given three
hypotheses. For `AddCommGrpCat` two of them — `HasSheafCompose` and, via
`CategoryTheory.sheafIsAbelian`, `Balanced` — are already available, and the third,
`HasFunctorialSurjectiveInjectiveFactorization`, follows from Mathlib's generic instance for
concrete categories once `(forget AddCommGrpCat).PreservesEpimorphisms` is supplied, which
is what `Oka/Algebra/Category/Grp/EpiMono.lean` does. This file records the resulting
statement, which is
what one actually reaches for: **a section of the target of an epimorphism of sheaves of abelian
groups lifts on a covering sieve.**

The direction that is not formal is `epi → locally surjective`; the converse is Mathlib's
`CategoryTheory.Sheaf.epi_of_isLocallySurjective`.

The universe of `AddCommGrpCat` is kept independent of the universes of the site, as it is in
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`. Tying it to the morphism universe of `C`
would be enough for sheaves on a topological space but not for
`Oka/Algebra/Category/ModuleCat/Sheaf/LocallySurjective.lean`, where the universe of the
modules is a parameter of its own.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib.

## Where this would go upstream, and why no existing file will take it

A **new** file `Mathlib/Algebra/Category/Grp/Sheaf/LocallySurjective.lean`, beside the
sheaves-of-modules analogue of this statement that
`Oka/Algebra/Category/ModuleCat/Sheaf/LocallySurjective.lean` proposes for
`Mathlib/Algebra/Category/ModuleCat/Sheaf/`. Being new it costs no existing Mathlib
file anything; the Mathlib part of its own transitive closure is **1405** modules, or **1407**
once the instance in `Oka/Algebra/Category/Grp/EpiMono.lean` reaches its own target.

**This file was `Oka/CategoryTheory/Sites/LocallySurjective.lean` until taxis #935**, and that
path stated **57**: `Mathlib.CategoryTheory.Sites.Abelian` 55 and
`Mathlib.CategoryTheory.Sites.EpiMono` 2, on a closure of 922. Both figures were right and the 57
was not the price, because `Abelian AddCommGrpCat` — which
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` needs here — used to arrive through
`Oka.Algebra.Category.Grp.EpiMono`, which carried `Mathlib.Algebra.Category.Grp.Abelian` for this
file and did not use it. **`scripts/import_cost.py` prices a file's own `Mathlib.` imports and
drops its `Oka.` ones, so a Mathlib import reached through a mirror file is invisible to it in
both directions**: it was charged in full to `Grp/EpiMono.lean`, whose declaration does not need
it, and not at all here. With the import where it is used, the old path prices at **483**.

Every existing destination is far past the **96** `README.md` records as the figure that once
made an upstreaming judged too expensive, and the cheapest is not the closest:

| destination | its closure | these two lemmas cost it |
|---|---|---|
| `Mathlib/CategoryTheory/Sites/LocallySurjective.lean` | 922 | **483** |
| `Mathlib/CategoryTheory/Sites/Abelian.lean` | 977 | **428** |
| `Mathlib/Algebra/Category/Grp/Abelian.lean` | 1179 | **226** |
| `Mathlib/Algebra/Category/Grp/AB.lean` | 1290 | **181** |

Those are the four `Mathlib.` imports above, which is what `scripts/import_cost.py` prices; each
of the first three is **2** higher — 485, 430, 228 — if the destination must also take
`Mathlib/Algebra/Category/Grp/EpiMono.lean`, where the instance goes. `Grp/AB.lean` has it
already, which is why its 181 does not move.

Exactly two files under `Mathlib/` already import everything these two lemmas need, and they are
`Mathlib/Topology/Sheaves/Flasque.lean` and `Mathlib/Condensed/Light/AB.lean` — neither a home
for a statement about an arbitrary site. **So the price does not choose between destinations
here; it rules out all of them**, which is what makes a new file the answer rather than a
preference. Measured with `scripts/import_cost.py` and with an independent breadth-first search,
not estimated.

## Main results

- `CategoryTheory.Sheaf.isLocallySurjective_iff_epi_addCommGrp`
- `CategoryTheory.Sheaf.isLocallySurjective_of_epi_addCommGrp`
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {F G : Sheaf J AddCommGrpCat.{w}}

/-- A morphism of sheaves of abelian groups is locally surjective exactly when it is an
epimorphism. -/
lemma isLocallySurjective_iff_epi_addCommGrp (f : F ⟶ G) :
    IsLocallySurjective f ↔ Epi f :=
  isLocallySurjective_iff_epi' (A := AddCommGrpCat.{w}) f

/-- An epimorphism of sheaves of abelian groups is locally surjective: every section of the
target is, on a covering sieve, in the image. -/
lemma isLocallySurjective_of_epi_addCommGrp (f : F ⟶ G) [Epi f] : IsLocallySurjective f :=
  (isLocallySurjective_iff_epi_addCommGrp f).2 ‹_›

end CategoryTheory.Sheaf
