/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Repetition.Defs

/-!
# Schedule arithmetic internals for fixed-time repetition

This module proves the arithmetic and compact-seed alignment facts shared by
the public repetition surface and the proof-internal schedule. Keeping these
proofs below the public surface prevents internal correctness modules from
depending on `Complexitylib.Models.TuringMachine.Repetition`.
-/

public section

namespace Complexity

namespace NTM

/-! ### Exact schedule arithmetic -/

/-- Internal form of the zero-time stride calculation.
@isnad1 id=eq.0h0v.s3.15f15469ec3b from=translated src=- shape=3c26ae4f vocab=d7b7ad44
-/
theorem repeatAtTimeStride_zero_internal : repeatAtTimeStride 0 = 2 := rfl

/-- Internal form of the successor-time stride calculation.
@isnad1 id=eq.0h1v.s5.02f7987387a6 from=translated src=- shape=c8634fc0 vocab=b509baf1
-/
theorem repeatAtTimeStride_succ_internal (T : ℕ) :
    repeatAtTimeStride (T + 1) = repeatAtTimeStride T + 2 := by
  simp only [repeatAtTimeStride]
  omega

/-- Internal form of the zero-repetition schedule calculation.
@isnad1 id=eq.0h1v.s4.0a7c74f0e2d0 from=translated src=- shape=fe2c2146 vocab=344603ab
-/
theorem repeatAtTimeSteps_zero_internal (T : ℕ) :
    repeatAtTimeSteps 0 T = 2 := by
  simp [repeatAtTimeSteps]

/-- Internal form of the zero-time schedule calculation.
@isnad1 id=eq.0h1v.s5.0fe9b30552f5 from=translated src=- shape=1dff6a79 vocab=c5f5b627
-/
theorem repeatAtTimeSteps_zero_time_internal (k : ℕ) :
    repeatAtTimeSteps k 0 = 2 + k * 2 := by
  simp [repeatAtTimeSteps, repeatAtTimeStride_zero_internal]

/-- Internal form of the successor-repetition schedule calculation.
@isnad1 id=eq.0h2v.s5.88e1b30cd49c from=translated src=- shape=6f629737 vocab=9253142f
-/
theorem repeatAtTimeSteps_succ_internal (k T : ℕ) :
    repeatAtTimeSteps (k + 1) T = repeatAtTimeSteps k T + repeatAtTimeStride T := by
  simp [repeatAtTimeSteps, Nat.add_mul, Nat.add_assoc]

/-! ### Compact-seed alignment -/

/-- Internal form of the compact-seed and machine-schedule alignment.
@isnad1 id=eq.0h5v.s6.3329a4bc7321 from=translated src=- shape=e1879709 vocab=9871ea82
-/
theorem repeatRandomSeed_apply_repeatChoiceIdx_internal (k T : ℕ)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) (t : Fin T) :
    repeatRandomSeed k T choices (finProdFinEquiv (j, t)) =
      choices (repeatChoiceIdx T j t) := by
  erw [repeatRandomSeed_apply]
  congr 1
  apply Fin.ext
  change 2 + (t.val + (2 * T + 2) * j.val) =
    2 + j.val * (2 * T + 2) + t.val
  rw [Nat.mul_comm (2 * T + 2) j.val]
  omega

end NTM

end Complexity
