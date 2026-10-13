/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Internal

/-!
# Linear-time canonical binary addition -- output discipline

The scan and its rewind wrapper leave the public output tape one-way, so both
machines satisfy the transducer discipline required by space-bounded function
computation.
-/

public section

namespace Complexity

namespace TM

/-- The ripple-add scan never moves the public output head left.
@isnad1 id=istransd.0h4v.s4.98564d0dff51 from=translated src=- shape=0b195b8b vocab=feef2c2e
-/
theorem binaryRippleAddScanTM_isTransducer_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleAddScanTM lhsIdx rhsIdx resultIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | scan carry =>
      simp only [binaryRippleAddScanTM]
      split
      · split
        · simp only
          simp [idleDir]
          split <;> decide
        · simp [allReadBack, idleDir]
          split <;> decide
      · simp only
        simp [idleDir]
        split <;> decide
  | done =>
      simp [binaryRippleAddScanTM, allIdle, idleDir]
      split <;> decide

/-- The scan followed by all three rewinds remains a transducer.
@isnad1 id=istransd.0h4v.s4.051116410af2 from=translated src=- shape=0b195b8b vocab=17a8832c
-/
theorem binaryRippleAddTM_isTransducer_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).IsTransducer := by
  exact (binaryRippleAddScanTM_isTransducer_internal lhsIdx rhsIdx resultIdx).seqTM
    ((rewindWorkTM_isTransducer_internal lhsIdx).seqTM
      ((rewindWorkTM_isTransducer_internal rhsIdx).seqTM
        (rewindWorkTM_isTransducer_internal resultIdx)))

end TM

end Complexity
