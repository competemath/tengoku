/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.OutputSemantics.Internal

/-!
# Pointwise output semantics for deterministic Turing machines

This module exposes total bounded execution and machine-relative relations for
programs that produce complete binary strings. These definitions make no
universality assumption, so they can be reused both for arbitrary description
machines and for later universal-machine invariance theorems.

## Main results

- `TM.runCfg_reachesIn` -- bounded evaluation agrees with relational execution
- `TM.HaltsInTime.iff_runCfg` -- executable bounded halting
- `TM.ProducesInTime.iff_runCfg` -- an executable characterization
- `TM.ProducesInTime.take_time` -- unread program suffixes can be truncated
- `TM.ProducesInTime.mono` -- increasing the clock preserves production
- `Tape.HasOutput.eq` -- a tape has at most one exact binary-string output
- `TM.computes_iff_forall_produces` -- pointwise production uniformizes by length
- `TM.produces_iff_exists_producesInTime` -- bounded and unbounded agreement
-/

public section

namespace Complexity

namespace TM

variable {n : ℕ}

/--
@isnad1 id=eq.0h3v.s4.23051b72e13b from=translated src=- shape=12b745ce vocab=788f137e
-/
@[simp] theorem runCfg_zero (tm : TM n) (c : Cfg n tm.Q) : tm.runCfg c 0 = c := rfl

/--
@isnad1 id=eq.0h4v.s5.9fd22d52b9a7 from=translated src=- shape=cc2a9ed3 vocab=e85e6879
-/
@[simp] theorem runCfg_succ (tm : TM n) (c : Cfg n tm.Q) (steps : ℕ) :
    tm.runCfg c (steps + 1) =
      (tm.step (tm.runCfg c steps)).getD (tm.runCfg c steps) := rfl

/-- Bounded execution composes by addition of clocks.
@isnad1 id=eq.0h5v.s5.2be22b7cc235 from=translated src=- shape=1cd5e42e vocab=0234df0d
-/
theorem runCfg_add (tm : TM n) (c : Cfg n tm.Q) (first second : ℕ) :
    tm.runCfg c (first + second) = tm.runCfg (tm.runCfg c first) second :=
  runCfg_add_internal tm c first second

/-- Once a configuration is halted, bounded execution stands still.
@isnad1 id=eq.1h4v.s4.a6dee0965fdf from=translated src=- shape=f3cba714 vocab=e7cf5df5
-/
theorem runCfg_of_halted (tm : TM n) {c : Cfg n tm.Q}
    (hhalt : tm.halted c) (steps : ℕ) : tm.runCfg c steps = c :=
  runCfg_of_halted_internal tm hhalt steps

/-- An exact relational run agrees with bounded execution at the same clock.
@isnad1 id=eq.1h5v.s5.c15de550bf9f from=translated src=- shape=ed773fee vocab=175bb385
-/
theorem runCfg_of_reachesIn (tm : TM n) {c c' : Cfg n tm.Q} {steps : ℕ}
    (hreach : tm.reachesIn steps c c') : tm.runCfg c steps = c' :=
  runCfg_of_reachesIn_internal tm hreach

/-- The bounded evaluator's endpoint is reachable within its clock.
@isnad1 id=ex.0h4v.s5.40cad18eeb24 from=translated src=- shape=f9372bb4 vocab=6618c70b
-/
theorem runCfg_reachesIn (tm : TM n) (c : Cfg n tm.Q) (time : ℕ) :
    ∃ steps, steps ≤ time ∧ tm.reachesIn steps c (tm.runCfg c time) :=
  runCfg_reachesIn_internal tm c time

/-- A halted exact-step endpoint remains the endpoint at every larger clock.
@isnad1 id=eq.3h6v.s5.3398e94870be from=translated src=- shape=3b4c6ccd vocab=3331e5d1
-/
theorem runCfg_eq_of_reachesIn_halted (tm : TM n) {c c' : Cfg n tm.Q}
    {steps time : ℕ} (hreach : tm.reachesIn steps c c') (hhalt : tm.halted c')
    (hsteps : steps ≤ time) : tm.runCfg c time = c' :=
  runCfg_eq_of_reachesIn_halted_internal tm hreach hhalt hsteps

/-- Bounded halting is exactly the decidable property that the bounded evaluator
has reached the halt state.
@isnad1 id=iff.0h4v.s4.2878a46b2fdd from=translated src=- shape=8b338d29 vocab=d6ffb5aa
-/
theorem HaltsInTime.iff_runCfg (tm : TM n) (program : List Bool) (time : ℕ) :
    tm.HaltsInTime program time ↔ tm.halted (tm.runCfg (tm.initCfg program) time) :=
  haltsInTime_iff_runCfg_internal tm program time

/-- Bounded halting is decidable by executing the advertised clock. -/
instance instDecidableHaltsInTime (tm : TM n) (program : List Bool) (time : ℕ) :
    Decidable (tm.HaltsInTime program time) :=
  decidable_of_iff _ (HaltsInTime.iff_runCfg tm program time).symm

/-- Increasing the clock preserves bounded halting.
@isnad1 id=haltsint.2h5v.s4.7175d313bdc4 from=translated src=- shape=f912f575 vocab=cac0bf9d
-/
theorem HaltsInTime.mono {tm : TM n} {program : List Bool} {first second : ℕ}
    (hbound : first ≤ second) (hhalt : tm.HaltsInTime program first) :
    tm.HaltsInTime program second :=
  haltsInTime_mono_internal hbound hhalt

/-- Forgetting a clock turns bounded halting into eventual halting.
@isnad1 id=halts.1h4v.s4.06d0bea8e55e from=translated src=- shape=2110917f vocab=fd8aecd9
-/
theorem halts_of_haltsInTime {tm : TM n} {program : List Bool} {time : ℕ}
    (hhalt : tm.HaltsInTime program time) : tm.Halts program :=
  halts_of_haltsInTime_internal hhalt

/-- Eventual halting is equivalent to halting under some finite clock.
@isnad1 id=iff.0h3v.s4.9e8f6c31f544 from=translated src=- shape=3736780a vocab=fd8aecd9
-/
theorem halts_iff_exists_haltsInTime (tm : TM n) (program : List Bool) :
    tm.Halts program ↔ ∃ time, tm.HaltsInTime program time :=
  halts_iff_exists_haltsInTime_internal tm program

/-- Pointwise bounded production is exactly the decidable property of the
bounded evaluator being halted with the requested output.
@isnad1 id=iff.0h5v.s5.68d8be2b771c from=translated src=- shape=e8c24e17 vocab=72cf8e86
-/
theorem ProducesInTime.iff_runCfg (tm : TM n) (program output : List Bool)
    (time : ℕ) :
    tm.ProducesInTime program output time ↔
      tm.halted (tm.runCfg (tm.initCfg program) time) ∧
        (tm.runCfg (tm.initCfg program) time).output.HasOutput output :=
  producesInTime_iff_runCfg_internal tm program output time

/-- Bounded runs on two inputs stay synchronized in state, work, and output
when the initialized input tapes agree on every cell reachable by the clock.
@isnad1 id=and.1h5v.s7.ab707cc48597 from=translated src=- shape=5de1224d vocab=042676ba
-/
theorem runCfg_initCfg_congr_of_input_cells (tm : TM n)
    (first second : List Bool) (time : ℕ)
    (hinput : ∀ position, position ≤ time →
      (tm.initCfg first).input.cells position =
        (tm.initCfg second).input.cells position) :
    (tm.runCfg (tm.initCfg first) time).state =
        (tm.runCfg (tm.initCfg second) time).state ∧
      (tm.runCfg (tm.initCfg first) time).work =
        (tm.runCfg (tm.initCfg second) time).work ∧
      (tm.runCfg (tm.initCfg first) time).output =
        (tm.runCfg (tm.initCfg second) time).output :=
  runCfg_initCfg_congr_of_input_cells_internal tm first second time hinput

/-- Truncating an input to the clock preserves every initialized input cell
that can be reached within that clock.
@isnad1 id=eq.1h5v.s5.ab297fb92172 from=translated src=- shape=c938f3da vocab=4e5d230d
-/
theorem initCfg_take_input_cells_le (tm : TM n)
    (program : List Bool) (time position : ℕ) (hposition : position ≤ time) :
    (tm.initCfg program).input.cells position =
      (tm.initCfg (program.take time)).input.cells position :=
  initCfg_take_input_cells_le_internal tm program time position hposition

/-- Pointwise bounded production is decidable by running the machine for its
clock and checking the resulting finite output claim. -/
instance instDecidableProducesInTime (tm : TM n) (program output : List Bool)
    (time : ℕ) : Decidable (tm.ProducesInTime program output time) :=
  decidable_of_iff _ (ProducesInTime.iff_runCfg tm program output time).symm

/-- No bounded computation can inspect more than the first `time` program
bits: truncating there preserves exact production within the same clock.
@isnad1 id=produces.1h5v.s4.68c6f3a308a3 from=translated src=- shape=d51adada vocab=d9d90330
-/
theorem ProducesInTime.take_time {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.ProducesInTime (program.take time) output time :=
  producesInTime_take_internal hproduce

/-- Increasing the clock preserves pointwise production.
@isnad1 id=produces.2h6v.s5.75a70b79eb31 from=translated src=- shape=400c4081 vocab=2404a7fa
-/
theorem ProducesInTime.mono {tm : TM n} {program output : List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hproduce : tm.ProducesInTime program output first) :
    tm.ProducesInTime program output second :=
  producesInTime_mono_internal hbound hproduce

/-- Forgetting a clock turns bounded production into eventual production.
@isnad1 id=produces.1h5v.s4.239d2dd3dd61 from=translated src=- shape=c325a0ef vocab=980537cd
-/
theorem produces_of_producesInTime {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.Produces program output :=
  produces_of_producesInTime_internal hproduce

/-- Producing an output within a clock entails halting within that clock.
@isnad1 id=haltsint.1h5v.s4.8bfe7a0dd6ea from=translated src=- shape=72aa1f2f vocab=6612c472
-/
theorem ProducesInTime.haltsInTime {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.HaltsInTime program time :=
  haltsInTime_of_producesInTime_internal hproduce

/-- Producing an output entails eventual halting.
@isnad1 id=halts.1h4v.s4.212e5738482c from=translated src=- shape=74da39c8 vocab=1f60dceb
-/
theorem Produces.halts {tm : TM n} {program output : List Bool}
    (hproduce : tm.Produces program output) : tm.Halts program :=
  halts_of_produces_internal hproduce

/-- Eventual production is equivalent to production under some finite clock.
@isnad1 id=iff.0h4v.s4.c13fb25e4624 from=translated src=- shape=1b2386e5 vocab=980537cd
-/
theorem produces_iff_exists_producesInTime (tm : TM n) (program output : List Bool) :
    tm.Produces program output ↔ ∃ time, tm.ProducesInTime program output time :=
  produces_iff_exists_producesInTime_internal tm program output

/-- Two exact output claims about the same tape have equal lengths.
@isnad1 id=eq.2h3v.s4.cd7eb2ad084a from=translated src=- shape=04458f23 vocab=b97548b6
-/
theorem Tape.HasOutput.length_eq {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) :
    left.length = right.length :=
  hasOutput_length_eq_internal hleft hright

/-- A tape has at most one exact binary-string output.
@isnad1 id=eq.2h3v.s4.98be25a6862d from=translated src=- shape=c6ae3d21 vocab=e09302b8
-/
theorem Tape.HasOutput.eq {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) : left = right :=
  hasOutput_eq_internal hleft hright

/-- A deterministic program cannot produce two different outputs, even when
the two production claims use different clocks.
@isnad1 id=eq.2h7v.s5.8bc7e8db72d1 from=translated src=- shape=c8fd1734 vocab=7ca6e36b
-/
theorem ProducesInTime.output_unique {tm : TM n} {program left right : List Bool}
    {leftTime rightTime : ℕ} (hleft : tm.ProducesInTime program left leftTime)
    (hright : tm.ProducesInTime program right rightTime) : left = right :=
  producesInTime_output_unique_internal hleft hright

/-- Eventual production by a deterministic program has a unique output.
@isnad1 id=eq.2h5v.s4.a076f5df9f68 from=translated src=- shape=9dba8bb2 vocab=3e48da16
-/
theorem Produces.output_unique {tm : TM n} {program left right : List Bool}
    (hleft : tm.Produces program left) (hright : tm.Produces program right) : left = right :=
  produces_output_unique_internal hleft hright

/-- Whole-function bounded computation is exactly pointwise bounded production
under the same length-indexed clock.
@isnad1 id=iff.0h4v.s5.dec4fb4a8099 from=translated src=- shape=5b740227 vocab=0b4fe5a7
-/
theorem computesInTime_iff_forall_producesInTime (tm : TM n)
    (function : List Bool → List Bool) (time : ℕ → ℕ) :
    tm.ComputesInTime function time ↔
      ∀ input, tm.ProducesInTime input (function input) (time input.length) :=
  computesInTime_iff_forall_producesInTime_internal tm function time

/-- A bounded whole-function computation produces the requested output on a
particular input.
@isnad1 id=produces.1h5v.s5.2bcc6b5ae60d from=translated src=- shape=6359665e vocab=0b4fe5a7
-/
theorem ComputesInTime.producesInTime {tm : TM n}
    {function : List Bool → List Bool} {time : ℕ → ℕ}
    (hcompute : tm.ComputesInTime function time) (input : List Bool) :
    tm.ProducesInTime input (function input) (time input.length) :=
  (computesInTime_iff_forall_producesInTime tm function time).mp hcompute input

/-- Eventual whole-function computation is equivalent to eventual pointwise
production. The reverse implication uniformizes halting times over the finite
set of Boolean strings at each input length.
@isnad1 id=iff.0h3v.s4.5063c60b6eef from=translated src=- shape=1b6be61a vocab=784d1425
-/
theorem computes_iff_forall_produces (tm : TM n) (function : List Bool → List Bool) :
    tm.Computes function ↔ ∀ input, tm.Produces input (function input) :=
  computes_iff_forall_produces_internal tm function

/-- A whole-function computation produces the requested output on a particular
input.
@isnad1 id=produces.1h4v.s4.c148fed5bac5 from=translated src=- shape=a9cdbbf9 vocab=784d1425
-/
theorem Computes.produces {tm : TM n} {function : List Bool → List Bool}
    (hcompute : tm.Computes function) (input : List Bool) :
    tm.Produces input (function input) :=
  (computes_iff_forall_produces tm function).mp hcompute input

end TM

end Complexity
