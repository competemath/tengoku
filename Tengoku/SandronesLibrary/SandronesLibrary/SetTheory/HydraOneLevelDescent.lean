/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HydraOrdinalAssignment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict descent for one replicated hydra cut

This file proves strict ordinal descent for a genuine stage-dependent cut: a
root has one parent branch, that parent has one head, and cutting the head
replaces the pruned parent by `stage + 1` copies.  No claim is made about all
hydra shapes or all `Hydra.Step`s.
-/

namespace SandronesLibrary.SetTheory.HydraOneLevelDescent

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.Ordinal
open SandronesLibrary.SetTheory.HydraOrdinalAssignment

/-- The one-level replicated cut considered in this file.  It is an actual
hydra step for every stage, not merely a comparison of two unrelated trees.-/
def OneLevelReplicatedCut (stage : Nat) (before after : Hydra) : Prop :=
  before = .node [.node [Hydra.head]] ∧
    after = .node (List.replicate (stage + 1) (.node []))

theorem oneLevelReplicatedCut_isStep {stage : Nat} {before after : Hydra}
    (cut : OneLevelReplicatedCut stage before after) :
    Hydra.Step stage before after := by
  rcases cut with ⟨rfl, rfl⟩
  refine ⟨[0, 0], ?_, ?_⟩
  · constructor
    · simp
    · rfl
  · simp [Hydra.chop, Hydra.replaceAtWith, Hydra.head]

end SandronesLibrary.SetTheory.HydraOneLevelDescent
