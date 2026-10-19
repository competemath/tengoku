/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Tengoku.Seed.Algebra.Category.Grp.EpiMono
public import Tengoku.Seed.CategoryTheory.ConcreteCategory.EpiMono

/-!
# The forgetful functor on abelian groups preserves epimorphisms

`CategoryTheory.ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization` is the hypothesis
under which a morphism of sheaves valued in a concrete category factors as a locally surjective
morphism followed by a locally injective one, and hence — the reason one wants it — under which
**an epimorphism of sheaves is locally surjective**
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`, and for sheaves on a topological space
`TopCat.Sheaf.isLocallySurjective_iff_epi`).

Mathlib derives that class for any concrete category with strong epi–mono factorisations whose
forgetful functor preserves monomorphisms and epimorphisms
(`Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean:148`). For `AddCommGrpCat` all of those
hold, but `(forget AddCommGrpCat).PreservesEpimorphisms` is not registered; an epimorphism of
abelian groups is surjective, which is `AddCommGrpCat.epi_iff_surjective`, and that is all the
instance below needs. With it, and in a file that also has `Abelian AddCommGrpCat`, the
factorization class is `inferInstance`.

The strong epi–mono factorisations that class also wants come from `AddCommGrpCat` being
abelian, which is `Mathlib.Algebra.Category.Grp.Abelian` — the same trap as
`Balanced (Sheaf J AddCommGrpCat)`, where the missing piece was also `Abelian AddCommGrpCat` and
the error message named the construction rather than the category. **That import is not here**,
because the instance below does not use it; it is in
`Oka/Algebra/Category/Grp/Sheaf/LocallySurjective.lean`, the file that assembles the
factorization class and is the only thing in this repository that needs it.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Oka/`-mirror of the Mathlib directory tree for that reason, next to
`Mathlib/Algebra/Category/Grp/EpiMono.lean`.

**Upstreaming it costs that file nothing.** Its transitive closure is **637** Mathlib modules and
both imports above are already in it, so the cost is **0** — measured with
`python3 scripts/import_cost.py Oka/Algebra/Category/Grp/EpiMono.lean`, counting modules with a
file under `Mathlib/`, and not estimated.

**This paragraph read 544 until taxis #935, and the 544 was real but was not this declaration's.**
`Mathlib.Algebra.Category.Grp.Abelian` is not in the target's closure and adding it costs **544**
— 5.7× the **96** `README.md` records as the figure that once made an upstreaming judged too
expensive, and the largest price this tree carried. The instance does not need it: with that
import deleted this file still compiles, and the only thing under `Oka/` that stops compiling is

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
`Oka/Algebra/Category/Grp/Sheaf/LocallySurjective.lean`, at the one line where
`HasStrongEpiMonoFactorisations` is synthesised. **A re-exported import is priced against the
file that carries it, not against the file that needs it**, so a per-file sweep reads the whole
544 here; moving one line put it where the dependency is and made this file free.

## Main results

- the forgetful functor `AddCommGrpCat ⥤ Type` preserves epimorphisms. The instance below is
  anonymous, so the name Lean generates for it is not one to cite; it is the
  `CategoryTheory.Functor.PreservesEpimorphisms` instance for `forget AddCommGrpCat`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- The forgetful functor from abelian groups to types preserves epimorphisms, because an
epimorphism of abelian groups is surjective. -/
instance : (forget AddCommGrpCat.{u}).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    exact (CategoryTheory.epi_iff_surjective _).2 hf

end AddCommGrpCat
