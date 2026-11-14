/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HydraCertifiedStepWellFounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite certified hydra trajectories and transitive descent

Zero steps mean equality.  A positive exact step count gives strict ordinal
descent, and existentially quantifying a positive count yields the nonempty
transitive closure.  This closure inherits well-foundedness from certified
one-step predecessors.
-/

namespace SandronesLibrary.SetTheory.HydraCertifiedTransitiveDescent

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.HydraOrdinalAssignment
open SandronesLibrary.SetTheory.HydraCertifiedPlayTermination
open SandronesLibrary.SetTheory.HydraCertifiedStepWellFounded

/-- `CertifiedExactSteps n before after` means that exactly `n` certified
forward transitions lead from `before` to `after`.-/
def CertifiedExactSteps : Nat → Hydra → Hydra → Prop
  | 0, before, after => before = after
  | n + 1, before, after =>
      ∃ middle, CertifiedStep before middle ∧ CertifiedExactSteps n middle after

/-- The nonempty finite transitive closure of `CertifiedStep`.-/
def CertifiedTransitiveStep (before after : Hydra) : Prop :=
  ∃ n, CertifiedExactSteps (n + 1) before after

/-- The same nonempty closure in the predecessor orientation expected by
`WellFounded`.-/
def CertifiedTransitivePredecessor (after before : Hydra) : Prop :=
  CertifiedTransitiveStep before after

/-- A zero-step trajectory has equal endpoints, and endpoint equality always
gives the zero-step trajectory.-/
theorem certifiedExactSteps_zero_iff {before after : Hydra} :
    CertifiedExactSteps 0 before after ↔ before = after := by
  rfl

/-- Every predecessor in the library's nonempty finite closure belongs to the
standard transitive closure of the one-step predecessor relation.-/
theorem certifiedTransitivePredecessor_to_transGen {after before : Hydra}
    (steps : CertifiedTransitivePredecessor after before) :
    Relation.TransGen CertifiedPredecessor after before := by
  rcases steps with ⟨n, steps⟩
  induction n generalizing before with
  | zero =>
      rcases steps with ⟨middle, first, rfl⟩
      exact Relation.TransGen.single first
  | succ n ih =>
      rcases steps with ⟨middle, first, remaining⟩
      exact (ih remaining).tail first

end SandronesLibrary.SetTheory.HydraCertifiedTransitiveDescent
