/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HydraRightmostSpineDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Termination of certified rightmost-spine hydra plays

This file defines finite and infinite play interfaces for steps carrying the
rightmost-spine certificate from the preceding module.  Ordinal well-foundedness
rules out an infinite play all of whose steps have such a certificate.  This is
not a termination theorem for every `Hydra.Step`.
-/

namespace SandronesLibrary.SetTheory.HydraCertifiedPlayTermination

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.Ordinal
open SandronesLibrary.SetTheory.HydraOrdinalAssignment
open SandronesLibrary.SetTheory.HydraRightmostSpineDescent

/-- A step certified by some stage, finite rightmost ancestor spine, and the
two retained left sibling forests at the replication site.-/
def CertifiedStep (before after : Hydra) : Prop :=
  ∃ stage ancestors grandparentSiblings parentSiblings,
    RightmostSpineReplicatedCut stage ancestors grandparentSiblings
      parentSiblings before after

/-- A finite list is a certified play when every adjacent pair is a certified
step.  Empty and singleton lists are valid finite plays.-/
def IsCertifiedFinitePlay : List Hydra → Prop
  | [] => True
  | [_] => True
  | before :: after :: rest =>
      CertifiedStep before after ∧ IsCertifiedFinitePlay (after :: rest)

/-- An infinite certified play supplies a hydra at every natural time and a
rightmost-spine certificate for every transition.-/
structure CertifiedInfinitePlay where
  state : Nat → Hydra
  certified : ∀ n, CertifiedStep (state n) (state (n + 1))

end SandronesLibrary.SetTheory.HydraCertifiedPlayTermination
