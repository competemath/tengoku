/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.TreeCode.Basic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.WellFounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Validity of coded Borel syntax trees

Semantic validity is deliberately separate from the Polish raw carrier.  A valid code contains its
root, has a well-founded underlying tree, uses only the four frozen node tags, has zero payload at
non-basic nodes, and has exactly the children prescribed by its node kind:

* empty and basic nodes have no children;
* complement nodes have only child `0`;
* countable-union nodes have every natural-number child.

Labels outside the decoded tree are irrelevant.  No evaluator is introduced in this module.
-/

open Set

namespace DescriptiveSetTheory.BorelTreeCode

/-- A raw label is coherent when its tag is recognized and only a basic leaf carries payload.-/
def IsCoherentLabel (label : ℕ × ℕ) : Prop :=
  match NodeKind.ofCode? label.1 with
  | some .basic => True
  | some _ => label.2 = 0
  | none => False

/-- Label coherence at a specified finite node.-/
def Raw.IsCoherentAt (c : Raw) (s : List ℕ) : Prop :=
  IsCoherentLabel (c.labels s)

/-- The exact immediate-child shape prescribed by the label at a node.-/
def Raw.HasExpectedChildrenAt (c : Raw) (s : List ℕ) : Prop :=
  match c.kindAt? s with
  | some .empty => ∀ n, s ++ [n] ∉ c.tree
  | some .basic => ∀ n, s ++ [n] ∉ c.tree
  | some .compl => s ++ [0] ∈ c.tree ∧ ∀ n, n ≠ 0 → s ++ [n] ∉ c.tree
  | some .iUnion => ∀ n, s ++ [n] ∈ c.tree
  | none => False

/-- Exact semantic validity for a raw coded Borel tree.-/
structure IsValid (c : Raw) : Prop where
  root_mem : [] ∈ c.tree
  wellFounded : Tree.IsWellFounded c.tree
  coherent : ∀ s, s ∈ c.tree → c.IsCoherentAt s
  expectedChildren : ∀ s, s ∈ c.tree → c.HasExpectedChildrenAt s

/-- The subtype of valid codes. No standard-Borel instance is claimed for this generally
coanalytic locus.-/
abbrev Valid := {c : Raw // IsValid c}

namespace IsValid

variable {c : Raw} (h : IsValid c)

include h

/-- Every node of a valid code has one of the four recognized kinds.-/
theorem exists_kindAt (s : List ℕ) (hs : s ∈ c.tree) :
    ∃ kind, c.kindAt? s = some kind := by
  have hcoherent := IsValid.coherent h s hs
  cases hkind : c.kindAt? s with
  | none =>
      unfold Raw.IsCoherentAt IsCoherentLabel at hcoherent
      change NodeKind.ofCode? (c.labels s).1 = none at hkind
      rw [hkind] at hcoherent
      exact hcoherent.elim
  | some kind => exact ⟨kind, rfl⟩

/-- Empty nodes have no immediate children.-/
theorem noChildren_of_kindAt?_eq_empty {s : List ℕ} (hs : s ∈ c.tree)
    (hkind : c.kindAt? s = some .empty) (n : ℕ) : s ++ [n] ∉ c.tree := by
  have hchildren : ∀ n, s ++ [n] ∉ c.tree := by
    simpa only [Raw.HasExpectedChildrenAt, hkind] using
      IsValid.expectedChildren h s hs
  exact hchildren n

/-- Basic nodes have no immediate children.-/
theorem noChildren_of_kindAt?_eq_basic {s : List ℕ} (hs : s ∈ c.tree)
    (hkind : c.kindAt? s = some .basic) (n : ℕ) : s ++ [n] ∉ c.tree := by
  have hchildren : ∀ n, s ++ [n] ∉ c.tree := by
    simpa only [Raw.HasExpectedChildrenAt, hkind] using
      IsValid.expectedChildren h s hs
  exact hchildren n

/-- The unique complement child belongs to the underlying tree.-/
theorem child_zero_mem_of_kindAt?_eq_compl {s : List ℕ} (hs : s ∈ c.tree)
    (hkind : c.kindAt? s = some .compl) : s ++ [0] ∈ c.tree := by
  have hchildren : s ++ [0] ∈ c.tree ∧
      ∀ n, n ≠ 0 → s ++ [n] ∉ c.tree := by
    simpa only [Raw.HasExpectedChildrenAt, hkind] using
      IsValid.expectedChildren h s hs
  exact hchildren.1

/-- Complement nodes have no immediate child other than child zero.-/
theorem child_not_mem_of_kindAt?_eq_compl {s : List ℕ} (hs : s ∈ c.tree)
    (hkind : c.kindAt? s = some .compl) {n : ℕ} (hn : n ≠ 0) :
    s ++ [n] ∉ c.tree := by
  have hchildren : s ++ [0] ∈ c.tree ∧
      ∀ n, n ≠ 0 → s ++ [n] ∉ c.tree := by
    simpa only [Raw.HasExpectedChildrenAt, hkind] using
      IsValid.expectedChildren h s hs
  exact hchildren.2 n hn

/-- Every natural-number child of a countable-union node belongs to the tree.-/
theorem child_mem_of_kindAt?_eq_iUnion {s : List ℕ} (hs : s ∈ c.tree)
    (hkind : c.kindAt? s = some .iUnion) (n : ℕ) : s ++ [n] ∈ c.tree := by
  have hchildren : ∀ n, s ++ [n] ∈ c.tree := by
    simpa only [Raw.HasExpectedChildrenAt, hkind] using
      IsValid.expectedChildren h s hs
  exact hchildren n

/-- Non-basic nodes in a valid code have zero payload.-/
theorem payload_eq_zero_of_kindAt?_eq {s : List ℕ} (hs : s ∈ c.tree)
    {kind : NodeKind} (hkind : kind ≠ .basic) (htag : c.kindAt? s = some kind) :
    c.payloadAt s = 0 := by
  have hcoherent := IsValid.coherent h s hs
  unfold Raw.IsCoherentAt IsCoherentLabel at hcoherent
  change NodeKind.ofCode? (c.labels s).1 = some kind at htag
  rw [htag] at hcoherent
  cases kind with
  | basic => exact (hkind rfl).elim
  | empty | compl | iUnion => simpa [Raw.payloadAt] using hcoherent

end IsValid

end DescriptiveSetTheory.BorelTreeCode
