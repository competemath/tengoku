/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators

/-!
# Retargeted-input computation seams

An ordinary machine begins with every head on `▷`; its first transition moves
all heads right and may also change the control state. A phase-composed machine
usually enters its next phase with tapes already parked at cell `1`. This file
defines an executable wrapper that resumes a machine after that compulsory
sentinel transition while reading its input from the last work tape.

## Main definitions

- `TM.retargetInputStartState` — control state after the sentinel transition
- `TM.retargetInputStarted` — virtual-input machine entered with heads at cell `1`
- `TM.retargetInputStartedCfg` — canonical entry configuration for a virtual input
-/

@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- The source control state produced by its first transition from the all-`▷`
initial head positions. -/
def retargetInputStartState (M : TM k) : M.Q :=
  (M.δ M.qstart Γ.start (fun _ => Γ.start) Γ.start).1

/-- Read the source input from work tape `k`, starting from the already-parked
post-sentinel configuration. If the source starts halted, the wrapper also
starts halted; otherwise its start state is `retargetInputStartState M`.

The transition function and halt state are exactly those of `retargetInput M`. -/
def retargetInputStarted (M : TM k) : TM (k + 1) where
  Q := M.Q
  qstart := if M.qstart = M.qhalt then M.qhalt else retargetInputStartState M
  qhalt := M.qhalt
  δ := (retargetInput M).δ
  δ_right_of_start := (retargetInput M).δ_right_of_start

/-- Canonical phase-entry configuration for `retargetInputStarted M`: virtual
input `y` is on the last work tape at head `1`; source work tapes and the real
output are parked and blank. The ignored real input tape is arbitrary. -/
def retargetInputStartedCfg (M : TM k) (y : List Bool) (realInput : Tape) :
    Cfg (k + 1) (retargetInputStarted M).Q where
  state := (retargetInputStarted M).qstart
  input := realInput
  work := fun i =>
    if i.val < k then (Tape.init []).move Dir3.right
    else (Tape.init (y.map Γ.ofBool)).move Dir3.right
  output := (Tape.init []).move Dir3.right

/--
@isnad1 id=eq.0h4v.s6.588b0a0b4f68 from=translated src=- shape=bca41d35 vocab=30ff8770
-/
@[simp] theorem retargetInputStartedCfg_state (M : TM k) (y : List Bool)
    (realInput : Tape) :
    (retargetInputStartedCfg M y realInput).state = (retargetInputStarted M).qstart := rfl

/--
@isnad1 id=eq.0h4v.s5.95c8fca08005 from=translated src=- shape=36488845 vocab=fda320b6
-/
@[simp] theorem retargetInputStartedCfg_input (M : TM k) (y : List Bool)
    (realInput : Tape) :
    (retargetInputStartedCfg M y realInput).input = realInput := rfl

/--
@isnad1 id=eq.0h4v.s5.bb03242a188b from=translated src=- shape=934e8705 vocab=1654a913
-/
@[simp] theorem retargetInputStartedCfg_output (M : TM k) (y : List Bool)
    (realInput : Tape) :
    (retargetInputStartedCfg M y realInput).output =
      (Tape.init []).move Dir3.right := rfl

/--
@isnad1 id=eq.1h5v.s6.c9f09999a2b6 from=translated src=- shape=b17c687a vocab=160766bf
-/
theorem retargetInputStartedCfg_work_lt (M : TM k) (y : List Bool)
    (realInput : Tape) (i : Fin (k + 1)) (h : i.val < k) :
    (retargetInputStartedCfg M y realInput).work i =
      (Tape.init []).move Dir3.right := by
  simp [retargetInputStartedCfg, h]

/--
@isnad1 id=eq.0h4v.s6.33c0c62c8617 from=translated src=- shape=9664bb18 vocab=dc1d8a2f
-/
@[simp] theorem retargetInputStartedCfg_work_last (M : TM k) (y : List Bool)
    (realInput : Tape) :
    (retargetInputStartedCfg M y realInput).work ⟨k, by omega⟩ =
      (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
  simp [retargetInputStartedCfg]

end TM

end Complexity
