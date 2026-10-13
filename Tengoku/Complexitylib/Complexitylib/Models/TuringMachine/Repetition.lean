/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Repetition.Internal.ScheduleArithmetic

/-!
# Fixed-time probabilistic-machine repetition

This public surface records the exact arithmetic schedule of
`NTM.repeatAtTime` and connects its simulated-step positions to the generic
compact-seed projection from `Complexitylib.Classes.FiniteCounting`.

It deliberately makes no trace or acceptance claim: those require the
simulation invariants proved in the internal correctness layer.

## Main results

- `NTM.repeatAtTimeStride_zero`, `NTM.repeatAtTimeStride_succ` — stride arithmetic
- `NTM.repeatAtTimeSteps_zero`, `NTM.repeatAtTimeSteps_succ` — total-time arithmetic
- `NTM.repeatRandomSeed_apply_repeatChoiceIdx` — compact and machine schedules align
-/

public section

namespace Complexity

namespace NTM

/-! ### Exact schedule arithmetic -/

/-- With zero simulated steps, a stride consists only of rewind and finish.
@isnad1 id=eq.0h0v.s3.15f15469ec3b from=translated src=- shape=3c26ae4f vocab=d7b7ad44
-/
@[simp] theorem repeatAtTimeStride_zero : repeatAtTimeStride 0 = 2 :=
  repeatAtTimeStride_zero_internal

/-- Increasing the simulated time by one adds one simulation transition and one
rewind transition to every stride.
@isnad1 id=eq.0h1v.s5.02f7987387a6 from=translated src=- shape=c8634fc0 vocab=b509baf1
-/
theorem repeatAtTimeStride_succ (T : ℕ) :
    repeatAtTimeStride (T + 1) = repeatAtTimeStride T + 2 :=
  repeatAtTimeStride_succ_internal T

/-- Zero repetitions use exactly the two leading administrative transitions.
@isnad1 id=eq.0h1v.s4.0a7c74f0e2d0 from=translated src=- shape=fe2c2146 vocab=344603ab
-/
@[simp] theorem repeatAtTimeSteps_zero (T : ℕ) : repeatAtTimeSteps 0 T = 2 :=
  repeatAtTimeSteps_zero_internal T

/-- At zero simulated time, every repetition contributes its two administrative
transitions.
@isnad1 id=eq.0h1v.s5.0fe9b30552f5 from=translated src=- shape=1dff6a79 vocab=c5f5b627
-/
@[simp] theorem repeatAtTimeSteps_zero_time (k : ℕ) :
    repeatAtTimeSteps k 0 = 2 + k * 2 :=
  repeatAtTimeSteps_zero_time_internal k

/-- Adding one repetition appends exactly one stride.
@isnad1 id=eq.0h2v.s5.88e1b30cd49c from=translated src=- shape=6f629737 vocab=9253142f
-/
theorem repeatAtTimeSteps_succ (k T : ℕ) :
    repeatAtTimeSteps (k + 1) T = repeatAtTimeSteps k T + repeatAtTimeStride T :=
  repeatAtTimeSteps_succ_internal k T

/-! ### Compact-seed alignment -/

/-- The generic compact repetition seed selects exactly the global choice
position used by `repeatAtTime` for simulated step `t` of repetition `j`.
@isnad1 id=eq.0h5v.s6.3329a4bc7321 from=translated src=- shape=e1879709 vocab=9871ea82
-/
@[simp] theorem repeatRandomSeed_apply_repeatChoiceIdx (k T : ℕ)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) (t : Fin T) :
    repeatRandomSeed k T choices (finProdFinEquiv (j, t)) =
      choices (repeatChoiceIdx T j t) :=
  repeatRandomSeed_apply_repeatChoiceIdx_internal k T choices j t

end NTM

end Complexity
