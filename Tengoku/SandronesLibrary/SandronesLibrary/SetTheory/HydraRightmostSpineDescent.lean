/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HydraParentSiblingDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict descent along an arbitrary finite rightmost spine

Replication still occurs only at the selected head's grandparent, exactly as
specified by `Hydra.chop`.  Above it, a certificate lists arbitrary left
sibling forests whose selected child is rightmost.  Legality and strict
ordinal descent are propagated through every certified ancestor.
-/

namespace SandronesLibrary.SetTheory.HydraRightmostSpineDescent

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.Ordinal
open SandronesLibrary.SetTheory.HydraOrdinalAssignment
open SandronesLibrary.SetTheory.HydraSiblingDescent
open SandronesLibrary.SetTheory.HydraParentSiblingDescent

universe u

/-- Insert a focused hydra under a finite sequence of rightmost-child
contexts.  Each list contains the siblings retained to the focus's left.-/
def plugRightmostSpine : List (List Hydra) → Hydra → Hydra
  | [], focus => focus
  | siblings :: ancestors, focus =>
      .node (siblings ++ [plugRightmostSpine ancestors focus])

/-- Prefix a path by the rightmost-child index selected at every certified
ancestor.-/
def rightmostSpinePath : List (List Hydra) → List Nat → List Nat
  | [], localPath => localPath
  | siblings :: ancestors, localPath =>
      siblings.length :: rightmostSpinePath ancestors localPath

private theorem rightmostSpinePath_two (ancestors : List (List Hydra))
    (first second : Nat) (rest : List Nat) :
    ∃ next following tail,
      rightmostSpinePath ancestors (first :: second :: rest) =
        next :: following :: tail := by
  induction ancestors with
  | nil => exact ⟨first, second, rest, rfl⟩
  | cons siblings ancestors ih =>
      rcases ih with ⟨next, following, tail, pathEq⟩
      exact ⟨siblings.length, next, following :: tail, by
        simp only [rightmostSpinePath, pathEq]⟩

/-- Replacing the entry after a prefix by one item preserves the prefix.-/
private theorem replaceAtWith_rightmost {α : Type*}
    (initial : List α) (old new : α) :
    Hydra.replaceAtWith (initial ++ [old]) initial.length [new] =
      some (initial ++ [new]) := by
  induction initial with
  | nil => rfl
  | cons first initial ih =>
      simp only [List.cons_append, List.length_cons, Hydra.replaceAtWith]
      rw [ih]
      rfl

private theorem replaceAtWith_prefix_length {α : Type*}
    (initial replacement suffix : List α) (entry : α) :
    Hydra.replaceAtWith (initial ++ entry :: suffix) initial.length replacement =
      some (initial ++ replacement ++ suffix) := by
  induction initial with
  | nil => rfl
  | cons first initial ih =>
      simp only [List.cons_append, List.length_cons, Hydra.replaceAtWith]
      rw [ih]
      rfl

/-- Following the certified spine and then a local path reaches the same
subtree as following the local path inside the focus.-/
theorem subtreeAt_plugRightmostSpine (ancestors : List (List Hydra))
    (focus : Hydra) (localPath : List Nat) :
    Hydra.subtreeAt (plugRightmostSpine ancestors focus)
        (rightmostSpinePath ancestors localPath) =
      Hydra.subtreeAt focus localPath := by
  induction ancestors with
  | nil => rfl
  | cons siblings ancestors ih =>
      simp only [plugRightmostSpine, rightmostSpinePath, Hydra.subtreeAt]
      rw [show (siblings ++ [plugRightmostSpine ancestors focus])[siblings.length]? =
          some (plugRightmostSpine ancestors focus) by simp]
      exact ih

/-- A successful cut whose path already has at least two indices can be lifted
through every certified rightmost ancestor without causing extra replication
at those higher levels.-/
theorem chop_plugRightmostSpine (stage : Nat) (ancestors : List (List Hydra))
    (before after : Hydra) (first second : Nat) (rest : List Nat)
    (cut : Hydra.chop stage before (first :: second :: rest) = some after) :
    Hydra.chop stage (plugRightmostSpine ancestors before)
        (rightmostSpinePath ancestors (first :: second :: rest)) =
      some (plugRightmostSpine ancestors after) := by
  induction ancestors with
  | nil => exact cut
  | cons siblings ancestors ih =>
      rcases rightmostSpinePath_two ancestors first second rest with
        ⟨next, following, tail, pathEq⟩
      rw [pathEq] at ih
      simp [plugRightmostSpine, rightmostSpinePath, pathEq, Hydra.chop, ih,
        replaceAtWith_rightmost]

/-- A certificate for an arbitrarily deep rightmost-spine cut.  The bottom two
levels contain the actual replication rule; `ancestors` records every higher
rightmost-child context.-/
def RightmostSpineReplicatedCut (stage : Nat) (ancestors : List (List Hydra))
    (grandparentSiblings parentSiblings : List Hydra)
    (before after : Hydra) : Prop :=
  before = plugRightmostSpine ancestors
    (.node (grandparentSiblings ++ [.node (parentSiblings ++ [Hydra.head])])) ∧
  after = plugRightmostSpine ancestors
    (.node (grandparentSiblings ++
      List.replicate (stage + 1) (.node parentSiblings)))

theorem rightmostSpineReplicatedCut_isStep {stage : Nat}
    {ancestors : List (List Hydra)} {grandparentSiblings parentSiblings : List Hydra}
    {before after : Hydra}
    (cut : RightmostSpineReplicatedCut stage ancestors grandparentSiblings
      parentSiblings before after) :
    Hydra.Step stage before after := by
  rcases cut with ⟨rfl, rfl⟩
  let localBefore : Hydra :=
    .node (grandparentSiblings ++ [.node (parentSiblings ++ [Hydra.head])])
  let localAfter : Hydra :=
    .node (grandparentSiblings ++
      List.replicate (stage + 1) (.node parentSiblings))
  have headPath : Hydra.IsHeadPosition localBefore
      [grandparentSiblings.length, parentSiblings.length] := by
    constructor
    · simp
    · simp [localBefore, Hydra.subtreeAt, Hydra.head]
  have chopPath : Hydra.chop stage localBefore
      [grandparentSiblings.length, parentSiblings.length] = some localAfter := by
    simp [localBefore, localAfter, Hydra.chop, Hydra.head,
      replaceAtWith_prefix_length]
  refine ⟨rightmostSpinePath ancestors
      [grandparentSiblings.length, parentSiblings.length], ?_, ?_⟩
  · constructor
    · rcases rightmostSpinePath_two ancestors grandparentSiblings.length
        parentSiblings.length [] with ⟨next, following, tail, pathEq⟩
      rw [pathEq]
      simp
    · rw [subtreeAt_plugRightmostSpine]
      exact headPath.2
  · exact chop_plugRightmostSpine stage ancestors localBefore localAfter
      grandparentSiblings.length parentSiblings.length [] chopPath

end SandronesLibrary.SetTheory.HydraRightmostSpineDescent
