/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.ChoiceTape

/-!
# Fixing a nondeterministic branch

An `NTM`'s transition function is a `Bool` away from a `TM`'s, so fixing the
`Bool` turns it into a deterministic machine. Unlike `NTM.choiceTM`, which reads
one choice bit per step off a tape and therefore runs a whole path, `branchTM`
fixes the *same* choice for every step: it is the one-step successor operator of
the configuration graph, not a path.

That is what a search of the configuration graph needs. Deterministic machinery
— the encoded step `Complexity.Cobham.stepFn` of Cobham's algebra above all —
applies to a `TM` and not to an `NTM`, so an edge of the graph is taken by one
of the two `branchTM`s (`Complexity.NTM.succ_iff`, where the graph is
defined).

## Main definitions

- `NTM.branchTM` — the deterministic machine that always takes branch `b`

## Main results

- `NTM.branchTM_stepCfg` — its step is the branch's step
- `NTM.branchTM_step`, `NTM.branchTM_step_of_halted` — the step, halted or not
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ}

/-- The deterministic machine that always takes branch `b`. -/
def branchTM (tm : NTM k) (b : Bool) : TM k where
  Q := tm.Q
  decEq := tm.decEq
  finQ := tm.finQ
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := tm.δ b
  δ_right_of_start := tm.δ_right_of_start b

/--
@isnad1 id=eq.0h3v.s4.8179c0f5b2ce from=translated src=- shape=50806d1e vocab=82537e1f
-/
@[simp] theorem branchTM_Q (tm : NTM k) (b : Bool) : (tm.branchTM b).Q = tm.Q := rfl

/--
@isnad1 id=eq.0h3v.s4.48c18c83f072 from=translated src=- shape=4c8cdbbe vocab=863f1b49
-/
@[simp] theorem branchTM_qstart (tm : NTM k) (b : Bool) :
    (tm.branchTM b).qstart = tm.qstart := rfl

/--
@isnad1 id=eq.0h3v.s4.dcaf3117085d from=translated src=- shape=4c8cdbbe vocab=f8d84a16
-/
@[simp] theorem branchTM_qhalt (tm : NTM k) (b : Bool) :
    (tm.branchTM b).qhalt = tm.qhalt := rfl

/--
@isnad1 id=eq.0h3v.s5.4450df4fe6a9 from=translated src=- shape=3c08e061 vocab=ca524a1f
-/
@[simp] theorem branchTM_δ (tm : NTM k) (b : Bool) : (tm.branchTM b).δ = tm.δ b := rfl

/-- One step of the fixed branch is one step of the nondeterministic machine on that
branch.
@isnad1 id=eq.0h4v.s5.0d132f8d9e38 from=translated src=- shape=413ebc6c vocab=2467ce8d
-/
@[simp] theorem branchTM_stepCfg (tm : NTM k) (b : Bool) (c : Cfg k tm.Q) :
    (tm.branchTM b).stepCfg c = tm.stepCfg b c := rfl

/-- A non-halted configuration steps to the branch's successor.
@isnad1 id=eq.1h4v.s5.48d14c0229dd from=translated src=- shape=407b669b vocab=94ca297a
-/
theorem branchTM_step (tm : NTM k) (b : Bool) {c : Cfg k tm.Q} (h : c.state ≠ tm.qhalt) :
    (tm.branchTM b).step c = some (tm.stepCfg b c) :=
  TM.step_of_not_halted _ h

/-- A halted configuration has no successor on either branch.
@isnad1 id=eq.1h4v.s5.b1932bce1916 from=translated src=- shape=6b7004d5 vocab=42fd4fec
-/
theorem branchTM_step_of_halted (tm : NTM k) (b : Bool) {c : Cfg k tm.Q}
    (h : c.state = tm.qhalt) : (tm.branchTM b).step c = none := by
  simp only [TM.step]
  exact ite_eq_left (show c.state = (tm.branchTM b).qhalt from h)

end NTM

end Complexity
