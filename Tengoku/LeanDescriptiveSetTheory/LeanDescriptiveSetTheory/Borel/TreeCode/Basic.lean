/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.CodeSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Raw coded Borel syntax trees

This file fixes the carrier and label convention for externally coded Borel syntax.  A raw code
consists of a prefix-closed Boolean tree code together with two natural-number coordinates at every
finite node.  The first coordinate is a node-kind tag; the second is a basis index for basic leaves
and must be zero for every other valid node kind.

The carrier is Polish (hence standard Borel).  It intentionally contains malformed and
ill-founded codes.  `BorelTreeCode.IsValid`, defined in the next module, is the separate semantic
validity predicate; no evaluator is defined on `Raw` alone.
-/

open Set

namespace DescriptiveSetTheory.BorelTreeCode

/-- Stable node tags used by the raw natural-number label coordinate.-/
inductive NodeKind where
  | empty
  | basic
  | compl
  | iUnion
  deriving DecidableEq, Repr

/-- The frozen numerical encoding of a Borel-syntax node kind.-/
def NodeKind.code : NodeKind → ℕ
  | .empty => 0
  | .basic => 1
  | .compl => 2
  | .iUnion => 3

/-- Decode a raw natural-number tag. Tags outside `0, 1, 2, 3` are malformed.-/
def NodeKind.ofCode? : ℕ → Option NodeKind
  | 0 => some .empty
  | 1 => some .basic
  | 2 => some .compl
  | 3 => some .iUnion
  | _ => none

/-- Encoding and then decoding a recognized node kind is exact.-/
@[simp]
theorem NodeKind.ofCode?_code (kind : NodeKind) : NodeKind.ofCode? kind.code = some kind := by
  cases kind <;> rfl

/-- A raw code is a Polish tree carrier together with a natural pair at every finite node.-/
abbrev Raw : Type := Tree.TreeCode × (List ℕ → ℕ × ℕ)

/-- The prefix-closed Boolean-tree component of a raw code.-/
def Raw.treeCode (c : Raw) : Tree.TreeCode := c.1

/-- Decode the Boolean-tree component as a descriptive tree.-/
def Raw.tree (c : Raw) : Descriptive.tree ℕ := Tree.decodeTree c.treeCode

/-- The complete raw label function.-/
def Raw.labels (c : Raw) : List ℕ → ℕ × ℕ := c.2

/-- The raw kind tag at a finite node.-/
def Raw.kindCodeAt (c : Raw) (s : List ℕ) : ℕ := (c.labels s).1

/-- The payload at a finite node. It is a basis index only at a valid basic leaf.-/
def Raw.payloadAt (c : Raw) (s : List ℕ) : ℕ := (c.labels s).2

/-- Decode the node kind at a finite node, returning `none` for a malformed tag.-/
def Raw.kindAt? (c : Raw) (s : List ℕ) : Option NodeKind :=
  NodeKind.ofCode? (c.kindCodeAt s)

/-- Membership in the decoded tree is the corresponding Boolean coordinate.-/
@[simp]
theorem Raw.mem_tree {c : Raw} {s : List ℕ} :
    s ∈ c.tree ↔ c.treeCode.1 s = true :=
  Iff.rfl

/-- The tree projection is continuous.-/
theorem continuous_treeCode : Continuous (fun c : Raw => c.treeCode) :=
  continuous_fst

/-- The label-function projection is continuous.-/
theorem continuous_labels : Continuous (fun c : Raw => c.labels) :=
  continuous_snd

/-- Reading the full label at a fixed node is continuous.-/
theorem continuous_labelAt (s : List ℕ) : Continuous (fun c : Raw => c.labels s) :=
  (continuous_apply s).comp continuous_labels

/-- Reading the kind tag at a fixed node is continuous.-/
theorem continuous_kindCodeAt (s : List ℕ) : Continuous (fun c : Raw => c.kindCodeAt s) :=
  continuous_fst.comp (continuous_labelAt s)

/-- Reading the payload at a fixed node is continuous.-/
theorem continuous_payloadAt (s : List ℕ) : Continuous (fun c : Raw => c.payloadAt s) :=
  continuous_snd.comp (continuous_labelAt s)

/-- The tree projection is measurable for the inherited Borel structures.-/
theorem measurable_treeCode : Measurable (fun c : Raw => c.treeCode) :=
  continuous_treeCode.measurable

/-- Every fixed label coordinate is measurable.-/
theorem measurable_labelAt (s : List ℕ) : Measurable (fun c : Raw => c.labels s) :=
  (continuous_labelAt s).measurable

end DescriptiveSetTheory.BorelTreeCode
