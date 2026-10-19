/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Tengoku.Seed.CategoryTheory.Sites.Over

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The iterated slice equivalence preserves covers

Material for `Mathlib/CategoryTheory/Sites/Over.lean`; see `README.md` on the mirror tree. This
file imports its target and nothing else, so upstreaming it adds nothing to that file's transitive
imports.

For `Y : Over X`, `CategoryTheory.Over.iteratedSliceEquiv` identifies `Over Y` with `Over Y.left`.
Both of its functors are cocontinuous for the sliced topologies, because an equivalence is; what
is recorded here is that they are **cover-preserving**, and hence that `CategoryTheory.Over.post`
along either of them is *continuous*. Note where that statement lives: the two instances below are
at `((J.over X).over Y).over W` and `(J.over Y.left).over W`, so the slicing is **three deep on one
side** and the functor whose continuity is asserted is `CategoryTheory.Over.post` of an iterated
slice functor, not the iterated slice functor itself.

**The consumer is `Oka/Algebra/Category/ModuleCat/Sheaf/Generators.lean`, which is the only file
that imports this one.** Its hypothesis is written in exactly these terms —
`[∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]`, at four of its declarations — and
it is what lets a sheaf of modules on one further slice be pushed to the other.

It is **not** `Oka/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`'s
`SheafOfModules.overOverEquivalence`, and that is worth saying because a clause here used to claim
it was. That definition does not and cannot see these instances — the file imports three Mathlib
modules and nothing else — and it does not want them: its binders are
`[Functor.IsContinuous eqv.functor J K]` and `[Functor.IsContinuous eqv.inverse K J]`, continuity
of the iterated slice functors *themselves* at the twice-sliced topologies, which Mathlib supplies
on its own.

Neither cover-preservation lemma is proved directly. Mathlib's
`CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving` turns cocontinuity of one adjoint
into cover preservation of the other, and an equivalence supplies both adjunctions, so the two
lemmas are each other's mirror image with the roles of the two functors exchanged. The two
instances then follow from `CategoryTheory.CoverPreserving.overPost` and
`CategoryTheory.Functor.isContinuous_of_coverPreserving`; the representable flatness that
`CategoryTheory.compatiblePreservingOfFlat` asks for is left to instance search.

## Main results

- `CategoryTheory.coverPreserving_iteratedSliceForward` and
  `CategoryTheory.coverPreserving_iteratedSliceBackward`, and the two
  `CategoryTheory.Functor.IsContinuous` instances for `CategoryTheory.Over.post` that they give.
  The two lemmas now carry docstrings; the instances are anonymous, so they have no name to cite
  and the paragraph above is where they are accounted for.
-/

@[expose] public section

universe v' u'

namespace CategoryTheory

open Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- **The forward iterated slice functor preserves covers.** For `Y : Over X`, it carries a
covering sieve of the twice-sliced topology `(J.over X).over Y` to a covering sieve of
`J.over Y.left`.

Not proved directly. `CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving` turns
cocontinuity of one adjoint into cover preservation of the other, and
`CategoryTheory.Over.iteratedSliceBackward` is cocontinuous because it is half of an
equivalence. -/
lemma coverPreserving_iteratedSliceForward {X : C} (Y : Over X) :
    CoverPreserving ((J.over X).over Y) (J.over Y.left) Y.iteratedSliceForward :=
  (Y.iteratedSliceEquiv.symm.toAdjunction.isCocontinuous_iff_coverPreserving
    (J := J.over Y.left) (K := (J.over X).over Y)).mp
    (inferInstanceAs (Y.iteratedSliceBackward.IsCocontinuous _ _))

/-- **The backward iterated slice functor preserves covers**, in the other direction. The mirror
image of `CategoryTheory.coverPreserving_iteratedSliceForward` with the two functors of the
equivalence exchanged; see its docstring for the argument, which is the same one. -/
lemma coverPreserving_iteratedSliceBackward {X : C} (Y : Over X) :
    CoverPreserving (J.over Y.left) ((J.over X).over Y) Y.iteratedSliceBackward :=
  (Y.iteratedSliceEquiv.toAdjunction.isCocontinuous_iff_coverPreserving
    (J := (J.over X).over Y) (K := J.over Y.left)).mp
    (inferInstanceAs (Y.iteratedSliceForward.IsCocontinuous _ _))

instance {X : C} (Y : Over X) (W : Over Y) :
    (Over.post Y.iteratedSliceEquiv.functor).IsContinuous (((J.over X).over Y).over W)
      ((J.over Y.left).over (Y.iteratedSliceEquiv.functor.obj W)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_iteratedSliceForward (J := J) Y).overPost W)

instance {X : C} (Y : Over X) (W : Over Y.left) :
    (Over.post Y.iteratedSliceEquiv.inverse).IsContinuous ((J.over Y.left).over W)
      (((J.over X).over Y).over (Y.iteratedSliceEquiv.inverse.obj W)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_iteratedSliceBackward (J := J) Y).overPost W)

end CategoryTheory
