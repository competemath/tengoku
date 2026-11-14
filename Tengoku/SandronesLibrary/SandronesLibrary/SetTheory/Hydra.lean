/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A finite hydra game: definition and one-step computation

This file defines one explicit, ordered-tree version of a hydra game.  It does
not claim the Kirby--Paris termination theorem: no ordinal ranking or global
termination proof is supplied here.
-/

namespace SandronesLibrary.SetTheory

/-- A finite hydra is a finite ordered rooted tree.  The constructor is the
root, and its list contains the hydra's immediate subtrees.-/
inductive Hydra where
  | node (children : List Hydra) : Hydra
  deriving Repr

namespace Hydra

/-- A leaf, used as a hydra head.-/
def head : Hydra := .node []

/-- The subtree at a path of child indices.  The empty path denotes the whole
tree.-/
def subtreeAt : Hydra → List Nat → Option Hydra
  | h, [] => some h
  | .node children, i :: path =>
      match children[i]? with
      | none => none
      | some child => subtreeAt child path

/-- A head position is a nonempty valid path ending at a leaf.  In particular,
the root itself is never a head that Hercules may cut.-/
def IsHeadPosition (h : Hydra) (path : List Nat) : Prop :=
  path ≠ [] ∧ subtreeAt h path = some head

/-- Replace the entry at `index` by all entries of `replacement`.-/
def replaceAtWith {α : Type*} : List α → Nat → List α → Option (List α)
  | [], _, _ => none
  | _ :: tail, 0, replacement => some (replacement ++ tail)
  | first :: tail, index + 1, replacement =>
      (replaceAtWith tail index replacement).map (first :: ·)

/-- One deterministic cut at a specified head path in round `stage`.

* A head attached directly to the root is simply deleted.
* For a deeper head, at its grandparent replace the head's parent by
  `stage + 1` copies of that parent after the head has been deleted.
* Above that grandparent, only the unique subtree on the chosen path changes.

Invalid paths, or paths that do not end at a leaf, return `none`.-/
def chop (stage : Nat) : Hydra → List Nat → Option Hydra
  | _, [] => none
  | .node children, [i] => do
      let child ← children[i]?
      match child with
      | .node [] => return .node (← replaceAtWith children i [])
      | .node (_ :: _) => none
  | .node children, i :: j :: path => do
      let child ← children[i]?
      let changed ← (match path with
        | [] =>
            match child with
            | .node grandchildren => do
                let candidateHead ← grandchildren[j]?
                match candidateHead with
                | .node [] =>
                    let pruned := Hydra.node (← replaceAtWith grandchildren j [])
                    return List.replicate (stage + 1) pruned
                | .node (_ :: _) => none
        | k :: rest => do
            let descendant ← chop stage child (j :: k :: rest)
            return [descendant] : Option (List Hydra))
      return .node (← replaceAtWith children i changed)

/-- The stage-indexed one-step relation induced by `chop`.-/
def Step (stage : Nat) (before after : Hydra) : Prop :=
  ∃ path, IsHeadPosition before path ∧ chop stage before path = some after

/-- Cutting the sole head attached to the root leaves the root alone.-/
theorem chop_single_head (stage : Nat) :
    chop stage (.node [head]) [0] = some (.node []) := by
  rfl

/-- At stage two, cutting one of two heads below a non-root parent leaves the
other head in the pruned parent and makes three copies of that parent.-/
theorem chop_regrows_three :
    chop 2 (.node [.node [head, head]]) [0, 1] =
      some (.node [.node [head], .node [head], .node [head]]) := by
  rfl

/--
> **Entry**: settheory.googology.hydra-game-step
> **一句话**: 有限有序 Hydra 游戏的一步先按路径砍掉叶头，并在非根情形按阶段复制砍头后的父子树。
> **依赖**: 无
> **mathlib**: 无（本库显式有限树、路径和可执行单步）

The preceding computation is also a certified legal game step.  This entry
does not assert that every play terminates.-/
theorem regrows_three_step :
    Step 2 (.node [.node [head, head]])
      (.node [.node [head], .node [head], .node [head]]) := by
  refine ⟨[0, 1], ?_, chop_regrows_three⟩
  constructor
  · simp
  · rfl

end Hydra
end SandronesLibrary.SetTheory
