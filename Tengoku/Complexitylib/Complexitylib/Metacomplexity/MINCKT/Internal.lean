/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal

/-!
# Minimum conditional time-bounded Kolmogorov complexity -- proof internals
-/

public section

namespace Complexity

namespace MINCKT

namespace Instance

variable {tapes : ℕ}

/--
@isnad1 id=eq.0h1v.s3.76ca2739bf4e from=translated src=- shape=981f0160 vocab=c5e831f1
-/
theorem length_unaryClock_internal (inst : Instance) :
    inst.unaryClock.length = inst.time := by
  simp [unaryClock]

/--
@isnad1 id=eq.0h1v.s3.0e1acf9f5955 from=translated src=- shape=edb93955 vocab=c00000d0
-/
theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨output, condition, time⟩
  simp [decode?, encode, unaryClock]

/--
@isnad1 id=iff.0h2v.s4.e924c9dcc2e3 from=translated src=- shape=94e3551a vocab=6ce39f1c
-/
theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases houter : unpair? bits with
    | none => simp [decode?, houter] at hdecode
    | some outerComponents =>
        rcases outerComponents with ⟨output, remaining⟩
        cases hinner : unpair? remaining with
        | none => simp [decode?, houter, hinner] at hdecode
        | some innerComponents =>
            rcases innerComponents with ⟨condition, clock⟩
            rw [decode?, houter] at hdecode
            dsimp only at hdecode
            rw [hinner] at hdecode
            change (if clock = List.replicate clock.length true then
                some (Instance.mk output condition clock.length)
              else none) = some inst at hdecode
            by_cases hclock : clock = List.replicate clock.length true
            · have hbits := eq_pair_of_unpair?_eq_some houter
              have hremaining := eq_pair_of_unpair?_eq_some hinner
              rw [ite_eq_left hclock] at hdecode
              cases hdecode
              calc
                bits = pair output remaining := hbits
                _ = pair output (pair condition clock) :=
                  congrArg (pair output) hremaining
                _ = pair output
                    (pair condition (List.replicate clock.length true)) := by
                  exact congrArg (fun current => pair output (pair condition current))
                    hclock
                _ = encode
                    { output, condition, time := clock.length } := rfl
            · rw [ite_eq_right hclock] at hdecode
              contradiction
  · rintro rfl
    exact decode?_encode_internal inst

/--
@isnad1 id=iff.0h1v.s4.2dd473a0371e from=translated src=- shape=65444e03 vocab=ca2604f3
-/
theorem decode?_eq_none_iff_internal (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode := by
  constructor
  · intro hnone ⟨inst, hbits⟩
    rw [hbits, decode?_encode_internal] at hnone
    contradiction
  · intro hnoncanonical
    cases hdecode : decode? bits with
    | none => rfl
    | some inst =>
        exact (hnoncanonical
          ⟨inst, (decode?_eq_some_iff_internal bits inst).mp hdecode⟩).elim

/--
@isnad1 id=injectiv.0h0v.s2.2a79c3ba67d2 from=translated src=- shape=4b736592 vocab=1d67db8c
-/
theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

/--
@isnad1 id=eq.0h1v.s6.74a9c910940d from=translated src=- shape=67f4ffe9 vocab=60a85912
-/
theorem length_encode_internal (inst : Instance) :
    inst.encode.length =
      2 * inst.output.length + 2 * inst.condition.length + inst.time + 4 := by
  simp [encode, length_unaryClock_internal]
  omega

/--
@isnad1 id=iff.0h4v.s4.7f08828e3156 from=translated src=- shape=40d6f6a0 vocab=a68a6227
-/
theorem isAtMost_iff_hasProgramAtMost_internal (inst : Instance)
    (machine : OracleTM tapes) (threshold : ℕ) :
    inst.IsAtMost machine threshold ↔
      inst.HasProgramAtMost machine threshold := by
  exact
    OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
      machine inst.output inst.condition inst.time threshold

/--
@isnad1 id=isatmost.2h6v.s5.8931db10c60a from=translated src=- shape=3526825c vocab=8989f136
-/
theorem isAtMost_withTime_mono_internal (inst : Instance)
    (machine : OracleTM tapes) (threshold : ℕ) {first second : ℕ}
    (hclock : first ≤ second)
    (hsmall : (inst.withTime first).IsAtMost machine threshold) :
    (inst.withTime second).IsAtMost machine threshold := by
  exact
    (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
      machine inst.output inst.condition hclock).trans hsmall

/--
@isnad1 id=isatmost.2h5v.s4.e682c7a19d57 from=translated src=- shape=77774028 vocab=5099eefd
-/
theorem isAtMost_threshold_mono_internal (inst : Instance)
    (machine : OracleTM tapes) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hsmall : inst.IsAtMost machine first) :
    inst.IsAtMost machine second := by
  exact hsmall.trans (WithTop.coe_le_coe.mpr hthreshold)

end Instance

end MINCKT

end Complexity
