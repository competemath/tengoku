/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HydraSiblingDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hydra descent with siblings inside the copied parent

Both the root and the copied parent may retain arbitrary ordered left sibling
forests.  The selected parent and selected head must remain rightmost at their
respective levels.  This file proves legality and strict descent only for that
ordered subclass.
-/

namespace SandronesLibrary.SetTheory.HydraParentSiblingDescent

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.Ordinal
open SandronesLibrary.SetTheory.HydraOrdinalAssignment
open SandronesLibrary.SetTheory.HydraOneLevelDescent
open SandronesLibrary.SetTheory.HydraSiblingDescent

universe u

/-- Replacing the item just after a list prefix keeps the prefix and splices in
the replacement.-/
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

/-- A two-prefix replicated cut.  `rootSiblings` stay to the left of the copied
parent, while `parentSiblings` stay to the left of the head removed inside that
parent.-/
def ParentRightmostHeadReplicatedCut (stage : Nat)
    (rootSiblings parentSiblings : List Hydra) (before after : Hydra) : Prop :=
  before = .node
      (rootSiblings ++ [.node (parentSiblings ++ [Hydra.head])]) ∧
    after = .node
      (rootSiblings ++ List.replicate (stage + 1) (.node parentSiblings))

/-- The specified two-prefix transformation is exactly `chop` at the path
formed by the lengths of the two retained prefixes.
@isnad1 id=step.1h5v.s4.aa5708186472 from=translated src=- shape=85aeb539 vocab=657b4de0
-/
theorem parentRightmostHeadReplicatedCut_isStep {stage : Nat}
    {rootSiblings parentSiblings : List Hydra} {before after : Hydra}
    (cut : ParentRightmostHeadReplicatedCut stage rootSiblings parentSiblings
      before after) :
    Hydra.Step stage before after := by
  rcases cut with ⟨rfl, rfl⟩
  refine ⟨[rootSiblings.length, parentSiblings.length], ?_, ?_⟩
  · constructor
    · simp
    · simp [Hydra.subtreeAt, Hydra.head]
  · simp only [Hydra.chop]
    rw [show
      (rootSiblings ++ [.node (parentSiblings ++ [Hydra.head])])[rootSiblings.length]? =
        some (.node (parentSiblings ++ [Hydra.head])) by simp]
    simp [Hydra.head, replaceAtWith_prefix_length]

end SandronesLibrary.SetTheory.HydraParentSiblingDescent
