/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.Normalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Perfect trees and coherent binary splitting systems

A natural-number tree is perfect here when it contains the root and every node has two
incompatible extensions. Such a tree is pruned, but the stronger incompatible-extension condition
is what supports a coherent copy of the full binary tree.

The public constructor returns `Nonempty (BinarySplittingSystem T)`. Its internal choices are not
exported as a canonical selector. A splitting system records membership, coherent strict extension,
and incompatibility of the two children at every binary node.
-/

namespace DescriptiveSetTheory.Tree

/-- Two finite nodes are incompatible when neither extends the other.-/
def AreIncompatible {A : Type*} (s t : List A) : Prop :=
  ¬ s <+: t ∧ ¬ t <+: s

theorem AreIncompatible.symm {A : Type*} {s t : List A}
    (h : AreIncompatible s t) : AreIncompatible t s :=
  ⟨h.2, h.1⟩

/-- A natural-number tree is perfect when it contains its root and every node has two
incompatible extensions in the tree.-/
structure IsPerfectTree (T : Descriptive.tree ℕ) : Prop where
  root_mem : [] ∈ T
  exists_incompatible_extensions : ∀ {s : List ℕ}, s ∈ T →
    ∃ t ∈ T, ∃ u ∈ T, s <+: t ∧ s <+: u ∧ AreIncompatible t u

/-- The full natural-number tree is perfect.-/
theorem isPerfectTree_top : IsPerfectTree (⊤ : Descriptive.tree ℕ) := by
  refine ⟨by simp, fun {s} _ => ?_⟩
  refine ⟨s ++ [0], by simp, s ++ [1], by simp, ⟨[0], rfl⟩, ⟨[1], rfl⟩, ?_⟩
  constructor <;> intro h
  · have heq := h.eq_of_length (by simp)
    simp at heq
  · have heq := h.eq_of_length (by simp)
    simp at heq

/-- A coherent binary family of nodes inside a natural-number tree. Each child strictly extends
its parent, and the two children at every binary node are incompatible.-/
structure BinarySplittingSystem (T : Descriptive.tree ℕ) where
  /-- The selected natural-number tree node at each finite binary address.-/
  node : List Bool → List ℕ
  /-- Every selected node belongs to the original tree.-/
  node_mem : ∀ s, node s ∈ T
  /-- Each selected child extends its selected parent.-/
  node_prefix_child : ∀ s b, node s <+: node (s ++ [b])
  /-- The selected child is a strict extension, witnessed by length growth.-/
  node_length_lt_child : ∀ s b, (node s).length < (node (s ++ [b])).length
  /-- The two selected children of every binary address are incompatible.-/
  children_incompatible : ∀ s,
    AreIncompatible (node (s ++ [false])) (node (s ++ [true]))

namespace BinarySplittingSystem

variable {T : Descriptive.tree ℕ} (S : BinarySplittingSystem T)

/-- Coherence along immediate children extends to arbitrary binary-prefix extension.-/
theorem node_prefix_of_prefix {s t : List Bool} (hst : s <+: t) :
    S.node s <+: S.node t := by
  rcases hst with ⟨u, rfl⟩
  induction u generalizing s with
  | nil => simp
  | cons b u ih =>
      exact (S.node_prefix_child s b).trans (by
        simpa [List.append_assoc] using ih (s := s ++ [b]))

/-- The node chosen at binary depth `n` has length at least `n`.-/
theorem depth_le_node_length (s : List Bool) : s.length ≤ (S.node s).length := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s b ih =>
      simpa using Nat.succ_le_of_lt (lt_of_le_of_lt ih (S.node_length_lt_child s b))

/-- Distinct binary children of one node have incompatible selected extensions, in either order.-/
theorem children_incompatible_of_ne (s : List Bool) {b c : Bool} (hbc : b ≠ c) :
    AreIncompatible (S.node (s ++ [b])) (S.node (s ++ [c])) := by
  cases b <;> cases c
  · exact (hbc rfl).elim
  · exact S.children_incompatible s
  · exact AreIncompatible.symm (S.children_incompatible s)
  · exact (hbc rfl).elim

end BinarySplittingSystem

private def SplitPair (T : Descriptive.tree ℕ) (s : T) :=
  {p : T × T //
    s.1 <+: p.1.1 ∧ s.1 <+: p.2.1 ∧ AreIncompatible p.1.1 p.2.1}

private theorem IsPerfectTree.nonempty_splitPair {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : T) : Nonempty (SplitPair T s) := by
  rcases hT.exists_incompatible_extensions s.2 with ⟨t, ht, u, hu, hst, hsu, htu⟩
  exact ⟨⟨(⟨t, ht⟩, ⟨u, hu⟩), hst, hsu, htu⟩⟩

private noncomputable def IsPerfectTree.chosenSplit {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : T) : SplitPair T s :=
  Classical.choice (hT.nonempty_splitPair s)

private noncomputable def IsPerfectTree.nextNode {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : T) (b : Bool) : T :=
  if b then (hT.chosenSplit s).1.2 else (hT.chosenSplit s).1.1

private theorem IsPerfectTree.node_prefix_nextNode {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : T) (b : Bool) : s.1 <+: (hT.nextNode s b).1 := by
  cases b <;> simp [IsPerfectTree.nextNode, (hT.chosenSplit s).2.1,
    (hT.chosenSplit s).2.2.1]

private theorem IsPerfectTree.node_length_lt_nextNode {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : T) (b : Bool) : s.1.length < (hT.nextNode s b).1.length := by
  have hpref := hT.node_prefix_nextNode s b
  have hne : s.1 ≠ (hT.nextNode s b).1 := by
    cases b with
    | false =>
        change s.1 ≠ (hT.chosenSplit s).1.1.1
        intro h
        apply (hT.chosenSplit s).2.2.2.1
        rw [← h]
        exact (hT.chosenSplit s).2.2.1
    | true =>
        change s.1 ≠ (hT.chosenSplit s).1.2.1
        intro h
        apply (hT.chosenSplit s).2.2.2.2
        rw [← h]
        exact (hT.chosenSplit s).2.1
  exact lt_of_le_of_ne hpref.length_le fun hlen => hne (hpref.eq_of_length hlen)

private theorem IsPerfectTree.nextNodes_incompatible {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : T) :
    AreIncompatible (hT.nextNode s false).1 (hT.nextNode s true).1 := by
  simpa [IsPerfectTree.nextNode] using (hT.chosenSplit s).2.2.2

private noncomputable def IsPerfectTree.nodeAt {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : List Bool) : T :=
  s.foldl hT.nextNode ⟨[], hT.root_mem⟩

private theorem IsPerfectTree.nodeAt_append {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) (s : List Bool) (b : Bool) :
    hT.nodeAt (s ++ [b]) = hT.nextNode (hT.nodeAt s) b := by
  simp [IsPerfectTree.nodeAt]

/-- Every perfect natural-number tree contains a coherent binary splitting system. The statement
is existential so the internal choices are not presented as canonical data.-/
theorem IsPerfectTree.exists_binarySplittingSystem {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) : Nonempty (BinarySplittingSystem T) := by
  let S : BinarySplittingSystem T :=
    { node := fun s => (hT.nodeAt s).1
      node_mem := fun s => (hT.nodeAt s).2
      node_prefix_child := fun s b => by
        rw [hT.nodeAt_append]
        exact hT.node_prefix_nextNode (hT.nodeAt s) b
      node_length_lt_child := fun s b => by
        rw [hT.nodeAt_append]
        exact hT.node_length_lt_nextNode (hT.nodeAt s) b
      children_incompatible := fun s => by
        rw [hT.nodeAt_append, hT.nodeAt_append]
        exact hT.nextNodes_incompatible (hT.nodeAt s) }
  exact ⟨S⟩

end DescriptiveSetTheory.Tree
