/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Nondeterministic
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Internal.FirstPhase
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Internal.Tail
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.OutputBounds

/-!
# Deterministic prefix of the nondeterministic composition — proof internals

The branch-`false` projection of `NTM.compositionNTM tmF N` runs
deterministically from the initial configuration through the first
computation, the raw-output rewind, the copy onto the virtual-input tape,
and the virtual-input rewind, stopping at the rewind phase's halt state —
the last configuration before the branch-dependent seam into the placed
retargeted phase. Every step source on the way satisfies
`NTM.BranchesAgreeAt`, so the run is packaged as a `TM.ReachesInVia`
annotated run, ready for `NTM.trace_of_det_prefix`.

The main result is `NTM.compositionNTM_detPrefix_internal`, which also
records the boundary configuration's tape shape: the virtual-input tape
holds `f x` parked at head `1`, the second machine's scratch block and the
output are parked blanks, and every tape is start-invariant with head at
least `1`.
-/

public section

namespace Complexity

namespace NTM

variable {nf ng : ℕ}

/-- The boundary configuration at the end of the deterministic prefix:
    state at the virtual-input rewind's halt, virtual input `y` parked at
    head `1`, second scratch block and output parked blank, and every tape
    start-invariant with positive head. -/
@[expose] def DetPrefixBoundary (tmF : TM nf) (N : NTM ng) (y : List Bool)
    (E : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q) : Prop :=
  E.state = Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).qhalt))) ∧
  E.work (TM.compositionVirtualInputIdx nf ng) =
    (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
  (∀ j : Fin ng, E.work (TM.compositionSecondWorkIdx nf ng j) =
    (Tape.init []).move Dir3.right) ∧
  E.output = (Tape.init []).move Dir3.right ∧
  E.input.StartInvariant ∧ 1 ≤ E.input.head ∧
  (∀ i, (E.work i).StartInvariant ∧ 1 ≤ (E.work i).head)

end NTM

end Complexity
