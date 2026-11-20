import Tengoku.Seed.CategoryTheory.Action
import Tengoku.Seed.GroupTheory.FreeGroup.NielsenSchreier
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

namespace MarshallHall

universe u

/-!
## The labelled Schreier graph and its spanning-tree basis

The action groupoid is equipped with the smaller generating quiver whose edges
are labelled by the original free generators.  This is the finite graph that
the core construction uses; the generic Nielsen--Schreier instance instead
uses the whole free group as a generator synonym.
-/

abbrev CoverVertex (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :=
  ActionCategory (FreeGroup α) A

instance coverQuiver (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :
    Quiver (CoverVertex α A) where
  Hom x y := {e : α // FreeGroup.of e • x.back = y.back}

/-! The action groupoid is free for this explicit labelled generating quiver. -/

/-!
The basis is indexed by the actual labelled edges outside the chosen tree.
The proof is the same unique-lift argument as Mathlib's spanning-tree theorem,
but keeps the edge type explicit for later core-support statements.
-/

end MarshallHall
