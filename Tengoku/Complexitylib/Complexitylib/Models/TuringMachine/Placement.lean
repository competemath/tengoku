/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Placement.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Placement.Internal

/-!
# Work-tape placement

This public surface exposes exact simulation theorems for `TM.placeWorkTM`.
The source machine occupies a contiguous middle block of physical work tapes;
prefix and suffix tapes form an arbitrary preserved frame whenever their heads
are parked away from the left-end marker.

## Main results

- `TM.placeWorkTM_step_placeWorkCfg` — exact step with an evolving frame
- `TM.placeWorkTM_reachesIn_placeWorkCfg_stable` — exact stable-frame simulation
- `TM.placeWorkTM_reachesIn_placeWorkParkedCfg` — canonical parked simulation
- `TM.placeWorkTM_computesInTime` — same-time preservation of computation
-/

public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A placed step simulates one source step while applying the prescribed idle
action to the arbitrary physical extra-tape frame.
@isnad1 id=eq.0h6v.s7.c05900e74c26 from=translated src=- shape=ca121214 vocab=badc8316
-/
theorem placeWorkTM_step_placeWorkCfg (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map
        (placeWorkCfg tm pre post (placeWorkFrameStep extras)) :=
  placeWorkTM_step_placeWorkCfg_internal tm pre post extras c

/-- If every extra tape reads a non-left-end symbol, its idle action is a
no-op and a placed step commutes through the unchanged frame.
@isnad1 id=eq.1h6v.s7.8d7c70e2161c from=translated src=- shape=08b152b8 vocab=79e49410
-/
theorem placeWorkTM_step_placeWorkCfg_stable (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q)
    (hextra : ∀ i, ¬placeWorkInMiddle pre n i → (extras i).read ≠ Γ.start) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map (placeWorkCfg tm pre post extras) :=
  placeWorkTM_step_placeWorkCfg_stable_internal tm pre post extras c hextra

/-- Start-invariant extra tapes whose heads are at positive positions form a
stable frame for one placed step.
@isnad1 id=eq.2h6v.s7.6918b4866e6d from=translated src=- shape=e08f61b4 vocab=44031648
-/
theorem placeWorkTM_step_placeWorkCfg_of_startInvariant (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q)
    (hinv : ∀ i, ¬placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre n i → 1 ≤ (extras i).head) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map (placeWorkCfg tm pre post extras) := by
  apply placeWorkTM_step_placeWorkCfg_stable tm pre post extras c
  intro i hi
  show (extras i).cells (extras i).head ≠ Γ.start
  exact (hinv i hi).2 (extras i).head (hhead i hi)

/-- A stable arbitrary frame is preserved exactly throughout a bounded source
run, with no time overhead.
@isnad1 id=reachesi.2h8v.s6.88de28808f65 from=translated src=- shape=a502b986 vocab=76c2b30a
-/
theorem placeWorkTM_reachesIn_placeWorkCfg_stable (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape)
    {t : ℕ} {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c')
    (hextra : ∀ i, ¬placeWorkInMiddle pre n i → (extras i).read ≠ Γ.start) :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkCfg tm pre post extras c)
      (placeWorkCfg tm pre post extras c') :=
  placeWorkTM_reachesIn_placeWorkCfg_stable_internal tm pre post extras hreach hextra

/-- Start-invariant positive-head extras remain an exact frame throughout a
bounded source run.
@isnad1 id=reachesi.3h8v.s7.ffc156ac1bdb from=translated src=- shape=80e633f7 vocab=b8edfa1a
-/
theorem placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape)
    {t : ℕ} {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c')
    (hinv : ∀ i, ¬placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre n i → 1 ≤ (extras i).head) :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkCfg tm pre post extras c)
      (placeWorkCfg tm pre post extras c') := by
  apply placeWorkTM_reachesIn_placeWorkCfg_stable tm pre post extras hreach
  intro i hi
  show (extras i).cells (extras i).head ≠ Γ.start
  exact (hinv i hi).2 (extras i).head (hhead i hi)

/-- The canonical parked embedding commutes with one source step.
@isnad1 id=eq.0h5v.s7.e2d2626641c3 from=translated src=- shape=bf738994 vocab=80e96606
-/
theorem placeWorkTM_step_placeWorkParkedCfg (tm : TM n) (pre post : ℕ)
    (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).step (placeWorkParkedCfg tm pre post c) =
      (tm.step c).map (placeWorkParkedCfg tm pre post) :=
  placeWorkTM_step_placeWorkParkedCfg_internal tm pre post c

/-- The canonical parked embedding simulates a bounded source run exactly.
@isnad1 id=reachesi.1h7v.s6.855aac027f1e from=translated src=- shape=9bea784c vocab=6346b6d6
-/
theorem placeWorkTM_reachesIn_placeWorkParkedCfg (tm : TM n)
    (pre post : ℕ) {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkParkedCfg tm pre post c)
      (placeWorkParkedCfg tm pre post c') :=
  placeWorkTM_reachesIn_placeWorkParkedCfg_internal tm pre post hreach

/-- A placed embedded configuration is halted exactly when its source
configuration is halted.
@isnad1 id=iff.0h6v.s6.f5ac0cdcac2b from=translated src=- shape=1be20529 vocab=006a2dd4
-/
@[simp] theorem placeWorkCfg_halted_iff (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).halted (placeWorkCfg tm pre post extras c) ↔
      tm.halted c := by
  rfl

/-- A bounded run from the source's ordinary initial configuration lifts with
the same duration. A positive run ends in the canonical parked embedding; at
time zero the placed machine remains at its own ordinary initial configuration.
@isnad1 id=ex.1h7v.s8.26b5e8247e05 from=translated src=- shape=beffe658 vocab=5cee15dd
-/
theorem placeWorkTM_reachesIn_init (tm : TM n) (pre post : ℕ)
    (x : List Bool) {t : ℕ} {c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c') :
    ∃ C' : Cfg (pre + n + post) (placeWorkTM pre post tm).Q,
      (placeWorkTM pre post tm).reachesIn t ((placeWorkTM pre post tm).initCfg x) C' ∧
      C'.state = c'.state ∧ C'.input = c'.input ∧ C'.output = c'.output ∧
      (t = 0 ∨ C' = placeWorkParkedCfg tm pre post c') :=
  placeWorkTM_reachesIn_init_internal tm pre post x hreach

/-- Work-tape placement preserves deterministic function computation with
exactly the same time bound. The surrounding blank tapes bounce off `▷`
during the source machine's own first step and then remain parked.
@isnad1 id=computes.1h6v.s5.b8f3179c01f1 from=translated src=- shape=af79c55c vocab=96280590
-/
theorem placeWorkTM_computesInTime (tm : TM n) (pre post : ℕ)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : tm.ComputesInTime f T) :
    (placeWorkTM pre post tm).ComputesInTime f T :=
  placeWorkTM_computesInTime_internal tm pre post hcomp

end TM

end Complexity
