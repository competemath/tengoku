/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Asymptotics.PolyBound
public import Tengoku.Complexitylib.Complexitylib.Classes.FNP.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINKT.Defs

/-!
# Minimum time-bounded Kolmogorov complexity -- proof internals

Proofs of canonical-code exactness, short-program semantics, and monotonicity
for the public MINKT API.
-/

public section

namespace Complexity

namespace MINKT

namespace Instance

variable {tapes : ℕ}

/--
@isnad1 id=eq.0h1v.s3.fe9f35fb0546 from=translated src=- shape=981f0160 vocab=7942dcaf
-/
theorem length_unaryClock_internal (inst : Instance) :
    inst.unaryClock.length = inst.time := by
  simp [unaryClock]

/--
@isnad1 id=eq.0h1v.s3.3065d5f66db7 from=translated src=- shape=edb93955 vocab=096a948a
-/
theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨output, time⟩
  simp [decode?, encode, unaryClock]

/--
@isnad1 id=iff.0h2v.s4.69f854f0ff52 from=translated src=- shape=94e3551a vocab=a5681545
-/
theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases hpair : unpair? bits with
    | none => simp [decode?, hpair] at hdecode
    | some components =>
        rcases components with ⟨output, clock⟩
        by_cases hclock : clock = List.replicate clock.length true
        · have hbits := eq_pair_of_unpair?_eq_some hpair
          rw [decode?, hpair] at hdecode
          change (if clock = List.replicate clock.length true then
              some { output := output, time := clock.length } else none) =
            some inst at hdecode
          rw [ite_eq_left hclock] at hdecode
          cases hdecode
          calc
            bits = pair output clock := hbits
            _ = pair output (List.replicate clock.length true) :=
              congrArg (pair output) hclock
            _ = encode { output, time := clock.length } := rfl
        · rw [decode?, hpair] at hdecode
          change (if clock = List.replicate clock.length true then
              some { output := output, time := clock.length } else none) =
            some inst at hdecode
          rw [ite_eq_right hclock] at hdecode
          contradiction
  · rintro rfl
    exact decode?_encode_internal inst

/--
@isnad1 id=iff.0h1v.s4.2c1a028d79cc from=translated src=- shape=65444e03 vocab=9ad33a30
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
@isnad1 id=injectiv.0h0v.s2.3b639a255484 from=translated src=- shape=4b736592 vocab=7e18db67
-/
theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

/--
@isnad1 id=eq.0h1v.s5.6a0b39ac473d from=translated src=- shape=1163f848 vocab=969d85b1
-/
theorem length_encode_internal (inst : Instance) :
    inst.encode.length = 2 * inst.output.length + 2 + inst.time := by
  simp [encode, length_unaryClock_internal]

/--
@isnad1 id=iff.0h4v.s4.36d5af9f52ce from=translated src=- shape=22e7e485 vocab=f8123b63
-/
theorem isBelow_iff_hasProgramShorterThan_internal (inst : Instance)
    (machine : TM tapes) (threshold : ℕ → ℕ) :
    inst.IsBelow machine threshold ↔
      inst.HasProgramShorterThan machine threshold := by
  exact TM.timeBoundedKolmogorovComplexity_lt_coe_iff_internal
    machine inst.output inst.time (threshold inst.output.length)

/--
@isnad1 id=isbelow.2h6v.s5.21fe974452cf from=translated src=- shape=73700a4e vocab=a6c4c939
-/
theorem isBelow_withTime_mono_internal (inst : Instance)
    (machine : TM tapes) (threshold : ℕ → ℕ) {first second : ℕ}
    (hclock : first ≤ second)
    (hsmall : (inst.withTime first).IsBelow machine threshold) :
    (inst.withTime second).IsBelow machine threshold := by
  exact (TM.timeBoundedKolmogorovComplexity_mono_internal
    machine inst.output hclock).trans_lt hsmall

/--
@isnad1 id=isbelow.2h5v.s5.18060988fbb4 from=translated src=- shape=0a445f46 vocab=1110755e
-/
theorem isBelow_threshold_mono_internal (inst : Instance)
    (machine : TM tapes) {first second : ℕ → ℕ}
    (hthreshold : ∀ length, first length ≤ second length)
    (hsmall : inst.IsBelow machine first) :
    inst.IsBelow machine second := by
  exact hsmall.trans_le (WithTop.coe_le_coe.mpr (hthreshold inst.output.length))

end Instance

/--
@isnad1 id=le.2h6v.s5.83d5008f7a75 from=translated src=- shape=0d8e8749 vocab=d2bbd678
-/
theorem programWitnessRelation_length_le_polynomial_internal
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (polynomial : Polynomial ℕ)
    (hthreshold : ∀ length, threshold length ≤ polynomial.eval length)
    {bits program : List Bool}
    (hrelation : ProgramWitnessRelation machine threshold bits program) :
    program.length ≤ polynomial.eval bits.length := by
  obtain ⟨inst, hdecode, hlength, _hproduce⟩ := hrelation
  have hcanonical := (Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
  rw [hcanonical]
  have houtputLength : inst.output.length ≤ inst.encode.length := by
    rw [Instance.length_encode_internal]
    omega
  exact (Nat.le_of_lt hlength).trans
    ((hthreshold inst.output.length).trans
      (polynomial_eval_mono_nat polynomial houtputLength))

/--
@isnad1 id=polybala.1h3v.s4.22c8a6738f2d from=translated src=- shape=3ddb185e vocab=abdb0582
-/
theorem programWitnessRelation_polyBalanced_internal
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (hthreshold : PolyBound threshold) :
    PolyBalanced (ProgramWitnessRelation machine threshold) := by
  obtain ⟨polynomial, hpolynomial⟩ := hthreshold
  exact ⟨polynomial, fun _bits _program hrelation =>
    programWitnessRelation_length_le_polynomial_internal
      machine threshold polynomial hpolynomial hrelation⟩

/--
@isnad1 id=mem.2h3v.s5.ba46126dd0cb from=translated src=- shape=8c5d3d6c vocab=6395a964
-/
theorem programWitnessRelation_mem_FNP_of_pairLang_mem_P_internal
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (hthreshold : PolyBound threshold)
    (hverifier : pairLang (ProgramWitnessRelation machine threshold) ∈ P) :
    ProgramWitnessRelation machine threshold ∈ FNP :=
  ⟨programWitnessRelation_polyBalanced_internal machine threshold hthreshold,
    hverifier⟩

end MINKT

end Complexity
