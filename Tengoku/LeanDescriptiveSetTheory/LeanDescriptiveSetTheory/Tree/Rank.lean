/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.WellFounded
import Tengoku.Seed.SetTheory.Ordinal.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordinal ranks of well-founded descriptive-set-theoretic trees

The immediate-child relation from `LeanDescriptiveSetTheory.Tree.WellFounded` is oriented exactly
as required by mathlib's well-founded ordinal rank. This file exposes that rank on tree nodes and
defines the rank of a tree to be the rank of its root. The empty tree, which has no root node, is
assigned rank zero.

No second ordinal recursion is introduced: `nodeRank` is a thin wrapper around
`IsWellFounded.rank`, and its defining supremum equation and strict decrease along child edges are
inherited from mathlib.
-/

universe u

namespace DescriptiveSetTheory.Tree

variable {A : Type u} {T : Descriptive.tree A}

/-- The ordinal rank of a node in a well-founded tree.-/
noncomputable def nodeRank (hT : IsWellFounded T) (s : T) : Ordinal.{u} :=
  letI : _root_.IsWellFounded T (Child T) := ⟨hT⟩
  _root_.IsWellFounded.rank (Child T) s

/-- A node rank is the supremum of the successors of its immediate children's ranks.
@isnad1 id=eq.1h3v.s10.d21cbe1ce07f from=translated src=- shape=ac6504e1 vocab=a46c7ca2
-/
theorem nodeRank_eq (hT : IsWellFounded T) (s : T) :
    nodeRank hT s = ⨆ t : {t : T // Child T t s}, Order.succ (nodeRank hT t.1) := by
  letI : _root_.IsWellFounded T (Child T) := ⟨hT⟩
  simpa [nodeRank] using _root_.IsWellFounded.rank_eq (Child T) s

/-- The ordinal rank strictly decreases when passing from a parent to an immediate child.
@isnad1 id=lt.2h4v.s8.9b0356782fd3 from=translated src=- shape=e4067811 vocab=0ec7d228
-/
theorem nodeRank_lt_of_child (hT : IsWellFounded T) {s t : T} (h : Child T s t) :
    nodeRank hT s < nodeRank hT t := by
  letI : _root_.IsWellFounded T (Child T) := ⟨hT⟩
  simpa [nodeRank] using _root_.IsWellFounded.rank_lt_of_rel h

/-- The rank of a well-founded tree is its root rank, or zero when the tree is empty.-/
noncomputable def rank (T : Descriptive.tree A) (hT : IsWellFounded T) : Ordinal.{u} := by
  classical
  exact if hroot : [] ∈ T then nodeRank hT ⟨[], hroot⟩ else 0

/-- A tree containing its root has the same rank as that root node.
@isnad1 id=eq.2h2v.s8.f8b07420411d from=translated src=- shape=44950b0e vocab=c93f029d
-/
theorem rank_eq_nodeRank (hT : IsWellFounded T) (hroot : [] ∈ T) :
    rank T hT = nodeRank hT ⟨[], hroot⟩ := by
  simp [rank, hroot]

/-- A tree without a root has rank zero.
@isnad1 id=eq.2h2v.s7.ad306a2cd62e from=translated src=- shape=12b3733a vocab=f6931510
-/
theorem rank_eq_zero_of_nil_not_mem (hT : IsWellFounded T) (hroot : [] ∉ T) :
    rank T hT = 0 := by
  simp [rank, hroot]

/--
@isnad1 id=eq.1h1v.s7.ed1e1b7b44aa from=translated src=- shape=feb4cb49 vocab=d38504e0
-/
@[simp]
theorem rank_bot (hT : IsWellFounded (⊥ : Descriptive.tree A)) : rank ⊥ hT = 0 := by
  exact rank_eq_zero_of_nil_not_mem hT (by simp)

end DescriptiveSetTheory.Tree
