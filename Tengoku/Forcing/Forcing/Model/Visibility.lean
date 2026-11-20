/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Order.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The abstract visibility context

Genericity over a ground model quantifies over the tests *visible to the model*. This file
introduces the minimal interface that makes such quantification possible: a `VisibilityContext` is
nothing but the family of sets of conditions the ground model can see.

The context is deliberately spartan:

* **No countability.** Countability of the visible family is always an external hypothesis of an
  existence statement (Rasiowa–Sikorski), never a field of the context.
* **No carrier-specific data.** Designated designated reals arrive with the Cohen layer, not here.
* **No model of anything.** Visibility is an interface to be implemented by a later material
  ground model; nothing here is a claim about sets, transitivity, or ZFC.

Visibility and dense-openness are independent predicates — see the sanity examples — and
`visibleDenseOpen` is their intersection. Genericity over the context is `GenericFor` of that
family; it is deliberately not defined in this file.

## Main definitions

* `Forcing.VisibilityContext P`: the visibility interface.
* `Forcing.VisibilityContext.Visible`: `M` can see the set of conditions `D`.
* `Forcing.VisibilityContext.visibleDenseOpen`: the visible dense-open tests.

## Main results

* `Forcing.VisibilityContext.visibleDenseOpen_mono`: a context that sees more has more tests.
* `Forcing.VisibilityContext.full`, `Forcing.VisibilityContext.empty`: the extreme contexts, and the
  sanity examples separating `Visible` from `IsDenseOpen` in both directions.
-/

namespace Forcing

variable {P : Type*} [Preorder P]

/-- An abstract visibility context over the forcing notion `P`: the family of sets of
conditions the ground model can see. Deliberately minimal — no countability (that is always an
external hypothesis of an existence statement), no carrier-specific data, and no claim to model
anything.-/
@[ext] structure VisibilityContext (P : Type*) [Preorder P] where
  /-- The sets of conditions the ground model can see.-/
  visible : Set (Set P)

namespace VisibilityContext

variable {M M' : VisibilityContext P} {D : Set P}

/-- `M` can see the set of conditions `D`. Independent of `IsDenseOpen D` — see the sanity
examples below.-/
def Visible (M : VisibilityContext P) (D : Set P) : Prop :=
  D ∈ M.visible

/--
@isnad1 id=iff.0h3v.s5.a8e0585bd5cb from=translated src=- shape=e9f638a5 vocab=f0d5a8e1
-/
theorem visible_def : M.Visible D ↔ D ∈ M.visible :=
  .rfl

/-- The visible dense-open family: the tests that count for genericity over `M`.-/
def visibleDenseOpen (M : VisibilityContext P) : Set (Set P) :=
  {D ∈ M.visible | IsDenseOpen D}

/--
@isnad1 id=iff.0h3v.s5.a5500f049ad6 from=translated src=- shape=e3b85132 vocab=7acb89ec
-/
@[simp] theorem mem_visibleDenseOpen :
    D ∈ M.visibleDenseOpen ↔ M.Visible D ∧ IsDenseOpen D :=
  Iff.rfl

/-- Seeing more means owing more: the visible dense-open family is monotone in visibility.
@isnad1 id=le.1h3v.s5.bba226fef180 from=translated src=- shape=8521fee7 vocab=120098e9
-/
theorem visibleDenseOpen_mono (h : M.visible ⊆ M'.visible) :
    M.visibleDenseOpen ⊆ M'.visibleDenseOpen :=
  fun _ hD ↦ ⟨h hD.1, hD.2⟩

/-- The full context: sees every set of conditions. Genericity over it will be genericity for
every dense open set.-/
def full (P : Type*) [Preorder P] : VisibilityContext P :=
  ⟨Set.univ⟩

/--
@isnad1 id=visible.0h2v.s3.9324a07b05f5 from=translated src=- shape=9e7302da vocab=9dc70682
-/
@[simp] theorem visible_full : (full P).Visible D :=
  Set.mem_univ D

/--
@isnad1 id=eq.0h1v.s4.3aa3000a0315 from=translated src=- shape=264fa0dd vocab=d92b3198
-/
@[simp] theorem visibleDenseOpen_full : (full P).visibleDenseOpen = {D | IsDenseOpen D} :=
  Set.sep_univ

/-- The empty context: sees nothing. Genericity over it will be trivial.-/
def empty (P : Type*) [Preorder P] : VisibilityContext P :=
  ⟨∅⟩

/--
@isnad1 id=not.0h2v.s4.9bc3595f2f8c from=translated src=- shape=95e6dcad vocab=eeeb46ff
-/
@[simp] theorem not_visible_empty : ¬(empty P).Visible D :=
  Set.notMem_empty D

/--
@isnad1 id=eq.0h1v.s4.33388940ef16 from=translated src=- shape=8ee16e86 vocab=f6ffd75c
-/
@[simp] theorem visibleDenseOpen_empty : (empty P).visibleDenseOpen = ∅ :=
  Set.sep_empty _

/-!
### Sanity examples

`Visible` and `IsDenseOpen` are independent. The full context sees the empty set, which is not
dense once `P` is nonempty (over the empty preorder every set is vacuously dense, so the
hypothesis is required); and the empty context fails to see `Set.univ`, which is dense open over
any preorder.
-/

end VisibilityContext

end Forcing
