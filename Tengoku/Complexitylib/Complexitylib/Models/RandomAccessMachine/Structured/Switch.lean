/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Structured.Switch.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Structured.Switch.Internal

/-!
# Verified finite numeric switches for structured RAM programs

The theorem in this module gives exact source step accounting and explicit
logarithmic-cost and peak-space bounds for a finite numeric switch.
-/

public section

namespace Complexity

namespace RAM

namespace Structured

namespace Switch

open Internal

/-- A valid numeric code selects its corresponding branch, without requiring a
resource envelope. This semantic form supports composition before a larger
program chooses a shared cost and space bound.
@isnad1 id=ex.5h8v.s6.898821292047 from=translated src=- shape=96f867d1 vocab=7b42f693
-/
theorem select_exec {count test one : ℕ}
    (branch : Fin count → Cmd) (initial final : Store)
    {code branchSteps : ℕ}
    (hcode : code < count) (htest : initial test = code)
    (hone : initial one = 1) (hne : test ≠ one)
    (hbranch : ∃ cost space,
      Exec (branch ⟨code, hcode⟩) (cleared initial test) final
        branchSteps cost space) :
    ∃ cost space,
      Exec (select count test one branch) initial final
        (stepCount code branchSteps) cost space :=
  select_exec_internal branch initial final hcode htest hone hne hbranch

/-- A valid numeric code selects its corresponding branch. The selected branch
starts with the test register cleared, matching the decrementing implementation.
The result carries an exact transition count and envelope-based resource bounds.
@isnad1 id=measured.7h11v.s6.4d8cfeed7a23 from=translated src=- shape=e266ea72 vocab=551958d0
-/
theorem select_measured {count test one indexBound valueBound : ℕ}
    (branch : Fin count → Cmd) (initial final : Store)
    {code branchSteps branchCost : ℕ}
    (hcode : code < count) (htest : initial test = code)
    (hone : initial one = 1) (hne : test ≠ one)
    (htestIndex : test < indexBound)
    (hinitial : StoreEnvelope indexBound valueBound initial)
    (hbranch : MeasuredRuns (branch ⟨code, hcode⟩) (cleared initial test)
      final branchSteps branchCost (envelopeSpace indexBound valueBound)) :
    MeasuredRuns (select count test one branch) initial final
      (stepCount code branchSteps)
      (costBound code branchCost (valueWidth valueBound))
      (envelopeSpace indexBound valueBound) :=
  select_measured_internal branch initial final hcode htest hone hne
    htestIndex hinitial hbranch

end Switch

end Structured

end RAM

end Complexity
