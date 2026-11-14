/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HydraCertifiedPlayTermination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Well-founded induction for certified hydra steps

The forward game relation is reversed into the predecessor orientation expected
by `WellFounded`.  Pulling ordinal well-foundedness back along `hydraOrdinal`
then yields public `WellFounded`, `Acc`, and induction interfaces for certified
successors only.
-/

namespace SandronesLibrary.SetTheory.HydraCertifiedStepWellFounded

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.Ordinal
open SandronesLibrary.SetTheory.HydraOrdinalAssignment
open SandronesLibrary.SetTheory.HydraCertifiedPlayTermination

/-- The predecessor-oriented relation used by `WellFounded`: `after` is below
`before` exactly when the game has a certified forward step from `before` to
`after`.-/
def CertifiedPredecessor (after before : Hydra) : Prop :=
  CertifiedStep before after

end SandronesLibrary.SetTheory.HydraCertifiedStepWellFounded
