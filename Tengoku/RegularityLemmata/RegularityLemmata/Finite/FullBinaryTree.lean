/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.Seed.Data.Fintype.Vector
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.List.Infix
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite full binary trees as words

A **full binary tree of height `h`** is the set of binary words of length at most `h`. Its
**internal nodes** are the words of length `< h` and its **leaves** are the words of length
exactly `h`. A leaf *is* a full branch of the tree: the two notions coincide, and there is
deliberately no second name for one of them.

## Words, not a constructor tree

Nodes carry their address. Ancestry is `List.IsPrefix` and branch direction is the letter
immediately after the common prefix, so both are decidable and both come with Mathlib's list
API. Mathlib's `BinaryTree` is a storage type — it holds data at nodes and offers no notion of
a node's address — so it does not support these relations and is not used here.

## Subtypes over one carrier

The three node types are subtypes of `List Bool`, so the carrier never varies and only the
proof field does; `Subtype.ext` discharges it. Raw words with a length hypothesis were the
alternative, and would have pushed that hypothesis through every coloring, every embedding
law, every composition theorem, and every enumeration.

## Height conventions

At height `0` there are no internal nodes and exactly one leaf, the empty word. At height
`h + 1` the empty word is the root, an internal node, and each node of a height-`h` tree
appears twice, once under each branch of the root.
-/

namespace RegularityLemmata

/-! ### Node types -/

/-- A vertex of the full binary tree of height `h`: a word of length at most `h`.-/
abbrev TreeNode (h : ℕ) : Type := {w : List Bool // w.length ≤ h}

/-- An internal node of the full binary tree of height `h`: a word of length `< h`. These are
the nodes a coloring is defined on.-/
abbrev InternalNode (h : ℕ) : Type := {w : List Bool // w.length < h}

/-- A leaf of the full binary tree of height `h`: a word of length exactly `h`.

A leaf and a full branch are the same object, viewed from the two ends. There is no
`FullBranch` synonym.-/
abbrev LeafNode (h : ℕ) : Type := {w : List Bool // w.length = h}

variable {h : ℕ}

/-- An internal node is a vertex.-/
def internalToTree (x : InternalNode h) : TreeNode h := ⟨x.1, le_of_lt x.2⟩

/-- A leaf is a vertex.-/
def leafToTree (x : LeafNode h) : TreeNode h := ⟨x.1, le_of_eq x.2⟩

/--
@isnad1 id=eq.0h2v.s5.862efcbe72e6 from=translated src=- shape=9f5fdcf3 vocab=15bd7c3f
-/
@[simp] theorem internalToTree_val (x : InternalNode h) : (internalToTree x).1 = x.1 := rfl

/--
@isnad1 id=eq.0h2v.s5.829d5cbfda53 from=translated src=- shape=e8ab8f20 vocab=bfd74069
-/
@[simp] theorem leafToTree_val (x : LeafNode h) : (leafToTree x).1 = x.1 := rfl

/-! ### Ancestry and branch direction

Both relations are stated on **words**, not on nodes of a fixed height. An embedding relates
trees of two different heights, so a relation tied to one height would need transporting at
every use. -/

/-- `y` lies strictly below `x`.-/
def IsStrictPrefix (x y : List Bool) : Prop := x <+: y ∧ x ≠ y

/-- **`y` lies in the `b`-branch below `x`**: the first turn on the way from `x` down to `y` is
`b`. This is the relation an embedding preserves, and it is strictly stronger than recording
the immediate children of `x`, because `y` may be arbitrarily far below.-/
def BranchBelow (b : Bool) (x y : List Bool) : Prop := x ++ [b] <+: y

/--
@isnad1 id=iff.0h3v.s5.672e754ae0a3 from=translated src=- shape=c8ef54f5 vocab=29a2383a
-/
theorem branchBelow_def (b : Bool) (x y : List Bool) :
    BranchBelow b x y ↔ x ++ [b] <+: y := Iff.rfl

/-- Both relations are decidable, which is what lets the branch-direction tests below be
settled by `decide` rather than by a hand proof that could be written to match a wrong
definition.-/
instance (b : Bool) (x y : List Bool) : Decidable (BranchBelow b x y) :=
  inferInstanceAs (Decidable (x ++ [b] <+: y))

instance (x y : List Bool) : Decidable (IsStrictPrefix x y) :=
  inferInstanceAs (Decidable (x <+: y ∧ x ≠ y))

/--
@isnad1 id=isstrict.1h3v.s4.05c1f0da74dc from=translated src=- shape=b1b1fea7 vocab=86092cdb
-/
theorem BranchBelow.isStrictPrefix {b : Bool} {x y : List Bool} (h : BranchBelow b x y) :
    IsStrictPrefix x y := by
  refine ⟨(List.prefix_append _ _).trans h, ?_⟩
  intro hxy
  have := h.length_le
  simp [hxy] at this

/--
@isnad1 id=lt.1h3v.s4.13591a9eaef9 from=translated src=- shape=82d815df vocab=3782234d
-/
theorem BranchBelow.length_lt {b : Bool} {x y : List Bool} (h : BranchBelow b x y) :
    x.length < y.length := by
  have := h.length_le
  simp at this
  omega

/-- **A strict descent happens through one definite turn.** Ancestry therefore carries no
information beyond the branch relation, which is why an embedding needs only the branch law.
@isnad1 id=ex.1h2v.s4.132eded60caf from=translated src=- shape=54dae646 vocab=86092cdb
-/
theorem exists_branchBelow_of_isStrictPrefix {x y : List Bool} (h : IsStrictPrefix x y) :
    ∃ b : Bool, BranchBelow b x y := by
  obtain ⟨⟨t, ht⟩, hne⟩ := h
  cases t with
  | nil => exact (hne (by simpa using ht)).elim
  | cons b r => exact ⟨b, ⟨r, by simpa using ht⟩⟩

/-- Two prefixes of one word, of equal length, coincide. The reason the two branches below a
node can never meet again.-/
theorem eq_of_prefix_of_prefix_of_length_eq {l₁ l₂ l : List Bool}
    (h₁ : l₁ <+: l) (h₂ : l₂ <+: l) (hlen : l₁.length = l₂.length) : l₁ = l₂ := by
  obtain ⟨t, ht⟩ := List.prefix_of_prefix_length_le h₁ h₂ (le_of_eq hlen)
  have htnil : t = [] := by
    have := congrArg List.length ht
    simp at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  simpa [htnil] using ht

/-- **The two branches below a node are disjoint.**
@isnad1 id=false.2h3v.s4.1192adb6b5f6 from=translated src=- shape=315b6896 vocab=34e07869
-/
theorem not_branchBelow_of_branchBelow {b : Bool} {x y : List Bool}
    (h₁ : BranchBelow b x y) (h₂ : BranchBelow (!b) x y) : False := by
  have := eq_of_prefix_of_prefix_of_length_eq h₁ h₂ (by simp)
  have hb : b = !b := by simpa using congrArg (fun l => l.getLast?) this
  cases b <;> simp at hb

/-- **The word trichotomy.** Any two words are prefix-comparable, or else they separate at a
definite point through opposite turns. This is the case analysis behind injectivity of an
embedding.
@isnad1 id=or.0h2v.s5.aa28bb526ff6 from=translated src=- shape=6ada4633 vocab=3247245a
-/
theorem prefix_trichotomy : ∀ x y : List Bool,
    x <+: y ∨ y <+: x ∨ ∃ (z : List Bool) (b : Bool), BranchBelow b z x ∧ BranchBelow (!b) z y
  | [], _ => Or.inl List.nil_prefix
  | _ :: _, [] => Or.inr (Or.inl List.nil_prefix)
  | a :: x, c :: y => by
      by_cases hac : a = c
      · subst hac
        rcases prefix_trichotomy x y with hp | hp | ⟨z, b, h1, h2⟩
        · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
        · exact Or.inr (Or.inl (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
        · refine Or.inr (Or.inr ⟨a :: z, b, ?_, ?_⟩)
          · rw [BranchBelow, List.cons_append]
            exact List.cons_prefix_cons.mpr ⟨rfl, h1⟩
          · rw [BranchBelow, List.cons_append]
            exact List.cons_prefix_cons.mpr ⟨rfl, h2⟩
      · refine Or.inr (Or.inr ⟨[], a, ?_, ?_⟩)
        · rw [BranchBelow, List.nil_append]
          exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
        · have hb : (!a) = c := by cases a <;> cases c <;> simp_all
          rw [BranchBelow, List.nil_append]
          exact List.cons_prefix_cons.mpr ⟨hb, List.nil_prefix⟩

/-! ### The root, children, and the parent -/

/-- The root of a tree of positive height, as an internal node. A tree of height `0` has no
internal node, so the root is only internal once there is a turn to make.-/
def root (h : ℕ) : InternalNode (h + 1) := ⟨[], by simp⟩

/--
@isnad1 id=eq.0h1v.s5.5206f332e79f from=translated src=- shape=845dae08 vocab=a050e3aa
-/
@[simp] theorem root_val (h : ℕ) : (root h).1 = [] := rfl

/-- The `b`-child of an internal node, as a vertex. It need not be internal: the child of a
node at the last internal level is a leaf.-/
def child (b : Bool) (x : InternalNode h) : TreeNode h :=
  ⟨x.1 ++ [b], by have := x.2; simp; omega⟩

/-- The left child.-/
abbrev leftChild (x : InternalNode h) : TreeNode h := child false x

/-- The right child.-/
abbrev rightChild (x : InternalNode h) : TreeNode h := child true x

/--
@isnad1 id=eq.0h3v.s5.a3792aa6db88 from=translated src=- shape=fbfe641b vocab=27acb567
-/
@[simp] theorem child_val (b : Bool) (x : InternalNode h) : (child b x).1 = x.1 ++ [b] := rfl

/-- A node lies in the `b`-branch below its own `b`-child, inclusively: the child is the least
such node.
@isnad1 id=branchbe.0h3v.s5.2920dae4add2 from=translated src=- shape=edb913c8 vocab=dac31aff
-/
theorem branchBelow_child (b : Bool) (x : InternalNode h) :
    BranchBelow b x.1 (child b x).1 := by
  rw [BranchBelow, child_val]

/-- The parent of a vertex, with the root its own parent. Total, so no positivity guard is
needed at a use site.-/
def parent (x : TreeNode h) : TreeNode h :=
  ⟨x.1.dropLast, le_trans (by simp) x.2⟩

/--
@isnad1 id=eq.0h2v.s5.102c1b1f99df from=translated src=- shape=31063e25 vocab=552cd852
-/
@[simp] theorem parent_val (x : TreeNode h) : (parent x).1 = x.1.dropLast := rfl

/-! ### Descending into a branch

Prefixing a word by `b` embeds a tree of height `h` into the `b`-branch of a tree of height
`h + 1`. This is what lets the two halves of a recursive construction be assembled. -/

/-- A node of a height-`h` tree, viewed inside the `b`-branch of a height-`h + 1` tree.-/
def consInternal (b : Bool) (x : InternalNode h) : InternalNode (h + 1) :=
  ⟨b :: x.1, by have := x.2; simp; omega⟩

/--
@isnad1 id=eq.0h3v.s5.f88e788dd57c from=translated src=- shape=14cefc3a vocab=dc7f2694
-/
@[simp] theorem consInternal_val (b : Bool) (x : InternalNode h) :
    (consInternal b x).1 = b :: x.1 := rfl

/-- Everything in the image of `consInternal b` lies in the `b`-branch below the root.
@isnad1 id=branchbe.0h3v.s6.1e2979b48efa from=translated src=- shape=9bf2da14 vocab=60795bd8
-/
theorem branchBelow_root_cons (b : Bool) (x : InternalNode h) :
    BranchBelow b (root h).1 (consInternal b x).1 := by
  rw [BranchBelow, root_val, List.nil_append, consInternal_val]
  exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩

/--
@isnad1 id=injectiv.0h2v.s4.d02ad427210c from=translated src=- shape=628b0bd2 vocab=ffa96931
-/
theorem consInternal_injective (b : Bool) :
    Function.Injective (consInternal (h := h) b) := by
  intro x y hxy
  exact Subtype.ext (by simpa using congrArg Subtype.val hxy)

/-- **The height-`h + 1` case analysis.** Every internal node is either the root or lies in one
of the two branches, and the branch decomposition is by the first letter.
@isnad1 id=or.0h2v.s6.6c483611e2d8 from=translated src=- shape=4d23e4a5 vocab=697e9aee
-/
theorem internalNode_cases (x : InternalNode (h + 1)) :
    x = root h ∨ ∃ (b : Bool) (y : InternalNode h), x = consInternal b y := by
  obtain ⟨w, hw⟩ := x
  cases w with
  | nil => exact Or.inl rfl
  | cons b w => exact Or.inr ⟨b, ⟨w, by simpa using hw⟩, rfl⟩

/-! ### Enumeration and finiteness -/

/-- Every word of length at most `h`. Defined by recursion rather than through a choice
principle, so that the `Fintype` instances below are computable and `decide` can run on
statements quantified over nodes.-/
def wordsLE : ℕ → Finset (List Bool)
  | 0 => {[]}
  | h + 1 =>
      insert [] (((wordsLE h).image (List.cons true)) ∪ ((wordsLE h).image (List.cons false)))

/--
@isnad1 id=iff.0h2v.s4.81762e1d008d from=translated src=- shape=4df08e09 vocab=ab0e79f7
-/
@[simp] theorem mem_wordsLE : ∀ {h : ℕ} {w : List Bool}, w ∈ wordsLE h ↔ w.length ≤ h
  | 0, _ => by simp [wordsLE, List.length_eq_zero_iff]
  | _ + 1, [] => by simp [wordsLE]
  | h + 1, b :: w => by
      simp [wordsLE, mem_wordsLE (h := h)]
      cases b <;> simp

instance treeNodeFintype (h : ℕ) : Fintype (TreeNode h) :=
  Fintype.subtype (wordsLE h) fun _ => mem_wordsLE

instance internalNodeFintype (h : ℕ) : Fintype (InternalNode h) :=
  Fintype.subtype ((wordsLE h).filter fun w => w.length < h) fun _ => by
    simp only [Finset.mem_filter, mem_wordsLE]
    omega

instance leafNodeFintype (h : ℕ) : Fintype (LeafNode h) :=
  Fintype.subtype ((wordsLE h).filter fun w => w.length = h) fun _ => by
    simp only [Finset.mem_filter, mem_wordsLE]
    omega

/-! ### Height endpoints -/

/-- **A tree of height `0` has no internal node.** The endpoint that makes the base case of the
Ramsey induction a statement about nothing, and the one an extension through the leaf level has
to handle separately.-/
instance : IsEmpty (InternalNode 0) := ⟨fun x => by have := x.2; omega⟩

/-- **A tree of height `0` has exactly one leaf**, the empty word — so height `0` is not the
empty tree.
@isnad1 id=eq.0h1v.s5.85121f35f9c9 from=translated src=- shape=b182823c vocab=14a7c6f3
-/
theorem leafNode_zero_eq (x : LeafNode 0) : x = ⟨[], rfl⟩ :=
  Subtype.ext (List.eq_nil_of_length_eq_zero x.2)

instance : Unique (LeafNode 0) where
  default := ⟨[], rfl⟩
  uniq := leafNode_zero_eq

/--
@isnad1 id=eq.0h1v.s4.6632c2c6e07b from=translated src=- shape=5b09d1d5 vocab=34aa3a5b
-/
@[simp] theorem card_leafNode (h : ℕ) : Fintype.card (LeafNode h) = 2 ^ h := by
  have hcard : Fintype.card (LeafNode h)
      = @Fintype.card (List.Vector Bool h) (List.Vector.instFintype) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcard, card_vector]
  simp

/-! ### Tests -/

section Tests

-- Cardinalities at the small heights the Ramsey base cases use, computed rather than assumed.

end Tests

end RegularityLemmata
