/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.FNP.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINKT.Gap.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINKT.Internal

/-!
# Gap MINKT -- proof internals

Proofs of codec exactness, direct program characterizations, widening-based
disjointness, and totality of the finite-complexity search relation.
-/

public section

namespace Complexity

namespace GapMINKT

namespace Instance

variable {tapes : ℕ}

/--
@isnad1 id=eq.0h1v.s3.ebcc3c77dc29 from=translated src=- shape=981f0160 vocab=565c09c3
-/
theorem length_unaryThreshold_internal (inst : Instance) :
    inst.unaryThreshold.length = inst.threshold := by
  simp [unaryThreshold]

/--
@isnad1 id=eq.0h1v.s3.13efcaf17f0d from=translated src=- shape=edb93955 vocab=a8529ec1
-/
theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨output, time, threshold⟩
  rw [encode, decode?, unpair?_pair]
  simp only [base, unaryThreshold]
  change (do
      let baseInst ← MINKT.Instance.decode?
        ({ output := output, time := time } : MINKT.Instance).encode
      if List.replicate threshold true =
          List.replicate (List.replicate threshold true).length true then
        some
          ({ output := baseInst.output
             time := baseInst.time
             threshold := (List.replicate threshold true).length } : Instance)
      else none) = some ({ output, time, threshold } : Instance)
  rw [MINKT.Instance.decode?_encode_internal]
  simp

/--
@isnad1 id=iff.0h2v.s4.a0a883a2953b from=translated src=- shape=94e3551a vocab=9b29f02d
-/
theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases hpair : unpair? bits with
    | none => simp [decode?, hpair] at hdecode
    | some components =>
        rcases components with ⟨baseBits, thresholdBits⟩
        cases hbase : MINKT.Instance.decode? baseBits with
        | none => simp [decode?, hpair, hbase] at hdecode
        | some baseInst =>
            by_cases hthreshold :
                thresholdBits = List.replicate thresholdBits.length true
            · have hbits := eq_pair_of_unpair?_eq_some hpair
              rw [decode?, hpair] at hdecode
              change (MINKT.Instance.decode? baseBits).bind (fun base =>
                  if thresholdBits = List.replicate thresholdBits.length true then
                    some
                      { output := base.output
                        time := base.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [hbase] at hdecode
              change (if thresholdBits =
                  List.replicate thresholdBits.length true then
                    some
                      { output := baseInst.output
                        time := baseInst.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [ite_eq_left hthreshold] at hdecode
              cases hdecode
              have hbaseBits :=
                (MINKT.Instance.decode?_eq_some_iff_internal
                  baseBits baseInst).mp hbase
              calc
                bits = pair baseBits thresholdBits := hbits
                _ = pair baseInst.encode thresholdBits := by rw [hbaseBits]
                _ = pair baseInst.encode
                    (List.replicate thresholdBits.length true) :=
                  congrArg (pair baseInst.encode) hthreshold
                _ = encode
                    { output := baseInst.output
                      time := baseInst.time
                      threshold := thresholdBits.length } := rfl
            · rw [decode?, hpair] at hdecode
              change (MINKT.Instance.decode? baseBits).bind (fun base =>
                  if thresholdBits = List.replicate thresholdBits.length true then
                    some
                      { output := base.output
                        time := base.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [hbase] at hdecode
              change (if thresholdBits =
                  List.replicate thresholdBits.length true then
                    some
                      { output := baseInst.output
                        time := baseInst.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [ite_eq_right hthreshold] at hdecode
              contradiction
  · rintro rfl
    exact decode?_encode_internal inst

/--
@isnad1 id=iff.0h1v.s4.e87b5bf77abf from=translated src=- shape=65444e03 vocab=56ec3e80
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
@isnad1 id=injectiv.0h0v.s2.5de231b8bad7 from=translated src=- shape=4b736592 vocab=4cc9dce7
-/
theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

/--
@isnad1 id=eq.0h1v.s6.968910f64c3c from=translated src=- shape=aec7c53a vocab=6c8dbd5b
-/
theorem length_encode_internal (inst : Instance) :
    inst.encode.length =
      4 * inst.output.length + 2 * inst.time + inst.threshold + 6 := by
  rw [encode, pair_length, length_unaryThreshold_internal,
    MINKT.Instance.length_encode_internal]
  change 2 * (2 * inst.output.length + 2 + inst.time) + 2 + inst.threshold =
    4 * inst.output.length + 2 * inst.time + inst.threshold + 6
  omega

/--
@isnad1 id=iff.0h3v.s5.fe9c25ef0178 from=translated src=- shape=1c677833 vocab=fd13be2c
-/
theorem isYes_iff_exists_program_internal (inst : Instance)
    (machine : TM tapes) :
    inst.IsYes machine ↔
      ∃ program, program.length ≤ inst.threshold ∧
        machine.ProducesInTime program inst.output inst.time :=
  TM.timeBoundedKolmogorovComplexity_le_coe_iff_internal
    machine inst.output inst.time inst.threshold

/--
@isnad1 id=iff.0h4v.s4.b0c8e0c9abb3 from=translated src=- shape=aa472f79 vocab=610438e4
-/
theorem isNo_iff_no_relaxedWitness_internal (inst : Instance)
    (machine : TM tapes) (parameters : Parameters) :
    inst.IsNo machine parameters ↔
      ¬∃ program, inst.IsRelaxedWitness machine parameters program := by
  constructor
  · intro hno ⟨program, hlength, hproduce⟩
    have hcomplexity :=
      (TM.timeBoundedKolmogorovComplexity_le_internal hproduce).trans
        (WithTop.coe_le_coe.mpr hlength)
    exact (not_lt_of_ge hcomplexity) hno
  · intro hnone
    apply lt_of_not_ge
    intro hcomplexity
    obtain ⟨program, hlength, hproduce⟩ :=
      (TM.timeBoundedKolmogorovComplexity_le_coe_iff_internal
        machine inst.output
          (parameters.clock inst.output.length inst.time)
          (parameters.description inst.output.length inst.threshold)).mp
        hcomplexity
    exact hnone ⟨program, hlength, hproduce⟩

/--
@isnad1 id=not.2h4v.s4.412a073065f2 from=translated src=- shape=9bbc9066 vocab=c750c9f2
-/
theorem not_isNo_of_isYes_internal (inst : Instance)
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) (hyes : inst.IsYes machine) :
    ¬inst.IsNo machine parameters := by
  intro hno
  have hclock := TM.timeBoundedKolmogorovComplexity_mono_internal
    machine inst.output (hwidening.2 inst.output.length inst.time)
  have hdescription :
      (inst.threshold : WithTop ℕ) ≤
        (parameters.description inst.output.length inst.threshold : WithTop ℕ) :=
    WithTop.coe_le_coe.mpr
      (hwidening.1 inst.output.length inst.threshold)
  exact (not_lt_of_ge (hclock.trans (hyes.trans hdescription))) hno

end Instance

/--
@isnad1 id=iff.0h3v.s4.fbe3ed1fb678 from=translated src=- shape=a584a54e vocab=24ff15b8
-/
theorem yesLanguage_mem_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (inst : Instance) :
    inst.encode ∈ yesLanguage machine ↔ inst.IsYes machine := by
  simp [yesLanguage, Instance.decode?_encode_internal]

/--
@isnad1 id=iff.0h4v.s4.98e8f6f6e09e from=translated src=- shape=c66ee9b8 vocab=a5bcaf23
-/
theorem noLanguage_mem_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance) :
    inst.encode ∈ noLanguage machine parameters ↔
      inst.IsNo machine parameters := by
  simp [noLanguage, Instance.decode?_encode_internal]

/--
@isnad1 id=disjoint.1h3v.s5.7adb977ba3a0 from=translated src=- shape=7c376f8b vocab=21d000b1
-/
theorem disjoint_yesLanguage_noLanguage_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) :
    Disjoint (yesLanguage machine) (noLanguage machine parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hyes hno
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes : inst.IsYes machine := by
        simpa [yesLanguage, hdecode] using hyes
      change machine.timeBoundedKolmogorovComplexity inst.output inst.time ≤
        (inst.threshold : WithTop ℕ) at hisYes
      have hisNo : inst.IsNo machine parameters := by
        simpa [noLanguage, hdecode] using hno
      exact Instance.not_isNo_of_isYes_internal
        inst machine parameters hwidening hisYes hisNo

/--
@isnad1 id=iff.0h3v.s4.ae87cc246f0a from=translated src=- shape=ddc5e375 vocab=45edd0cc
-/
theorem mem_yesLanguage_iff_exists_program_internal {tapes : ℕ}
    (machine : TM tapes) (bits : List Bool) :
    bits ∈ yesLanguage machine ↔
      ∃ program, YesWitnessRelation machine bits program := by
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, YesWitnessRelation, hdecode]
  | some inst =>
      rw [show bits ∈ yesLanguage machine ↔ inst.IsYes machine by
        simp [yesLanguage, hdecode],
        Instance.isYes_iff_exists_program_internal]
      constructor
      · rintro ⟨program, hlength, hproduce⟩
        exact ⟨program, inst, hdecode, hlength, hproduce⟩
      · rintro ⟨program, decoded, hdecoded, hlength, hproduce⟩
        have : decoded = inst := Option.some.inj (hdecoded.symm.trans hdecode)
        subst decoded
        exact ⟨program, hlength, hproduce⟩

/--
@isnad1 id=le.1h4v.s4.374b5587a802 from=translated src=- shape=cb7e8640 vocab=84c41160
-/
theorem yesWitnessRelation_length_le_input_internal {tapes : ℕ}
    (machine : TM tapes) {bits program : List Bool}
    (hrelation : YesWitnessRelation machine bits program) :
    program.length ≤ bits.length := by
  obtain ⟨inst, hdecode, hlength, _hproduce⟩ := hrelation
  have hcanonical :=
    (Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
  rw [hcanonical, Instance.length_encode_internal]
  omega

/--
@isnad1 id=polybala.0h2v.s3.f562c7b3d0bf from=translated src=- shape=1f8e965c vocab=b5f1714b
-/
theorem yesWitnessRelation_polyBalanced_internal {tapes : ℕ}
    (machine : TM tapes) :
    PolyBalanced (YesWitnessRelation machine) := by
  refine ⟨Polynomial.X, ?_⟩
  intro bits program hrelation
  simpa only [Polynomial.eval_X] using
    yesWitnessRelation_length_le_input_internal machine hrelation

/--
@isnad1 id=mem.1h2v.s5.f875f94ace78 from=translated src=- shape=94c3f606 vocab=1fb5101a
-/
theorem yesWitnessRelation_mem_FNP_of_pairLang_mem_P_internal {tapes : ℕ}
    (machine : TM tapes)
    (hverifier : pairLang (YesWitnessRelation machine) ∈ P) :
    YesWitnessRelation machine ∈ FNP :=
  ⟨yesWitnessRelation_polyBalanced_internal machine, hverifier⟩

/--
@isnad1 id=iff.1h4v.s5.396285339274 from=translated src=- shape=7fbb2bfe vocab=cc9436e9
-/
theorem exists_searchRelation_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : MINKT.Instance) :
    (∃ program, SearchRelation machine parameters inst program) ↔
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ := by
  constructor
  · rintro ⟨program, optimum, hcomplexity, _hlength, _hproduce⟩ htop
    rw [htop] at hcomplexity
    exact WithTop.coe_ne_top hcomplexity.symm
  · intro hfinite
    obtain ⟨program, hlength, hproduce⟩ :=
      TM.timeBoundedKolmogorovComplexity_witness_internal
        machine inst.output inst.time hfinite
    obtain ⟨optimum, hoptimum⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hcomplexity :
        machine.timeBoundedKolmogorovComplexity inst.output inst.time =
          (optimum : WithTop ℕ) := hoptimum.symm
    have hprogramLength : program.length = optimum := by
      exact WithTop.coe_eq_coe.mp (hlength.trans hcomplexity)
    refine ⟨program, optimum, hcomplexity, ?_, ?_⟩
    · rw [hprogramLength]
      exact hwidening.1 inst.output.length optimum
    · exact hproduce.mono (hwidening.2 inst.output.length inst.time)

/--
@isnad1 id=iff.0h5v.s4.19b72c4ed489 from=translated src=- shape=968edfff vocab=4b489873
-/
theorem encodedSearchRelation_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (inst : MINKT.Instance) (program : List Bool) :
    EncodedSearchRelation machine parameters inst.encode program ↔
      SearchRelation machine parameters inst program := by
  simp [EncodedSearchRelation, MINKT.Instance.decode?_encode_internal]

/--
@isnad1 id=iff.1h4v.s5.016f56374f4e from=translated src=- shape=e196b010 vocab=0c12966a
-/
theorem exists_encodedSearchRelation_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : MINKT.Instance) :
    (∃ program, EncodedSearchRelation machine parameters inst.encode program) ↔
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ := by
  rw [show (∃ program,
      EncodedSearchRelation machine parameters inst.encode program) ↔
        ∃ program, SearchRelation machine parameters inst program by
      simp only [encodedSearchRelation_encode_iff_internal]]
  exact exists_searchRelation_iff_internal machine parameters hwidening inst

/--
@isnad1 id=le.3h7v.s6.e7fd8bb5acbe from=translated src=- shape=d539ccde vocab=e293da3c
-/
theorem encodedSearchRelation_length_le_polynomial_internal
    {tapes : ℕ} (machine : TM tapes) (parameters : Parameters)
    (descriptionPolynomial sourcePolynomial : Polynomial ℕ)
    (hdescription : ∀ length optimum,
      parameters.description length optimum ≤
        descriptionPolynomial.eval (length + optimum))
    (hsource : ∀ inst : MINKT.Instance, ∀ optimum : ℕ,
      machine.timeBoundedKolmogorovComplexity inst.output inst.time =
          (optimum : WithTop ℕ) →
        optimum ≤ sourcePolynomial.eval inst.encode.length)
    {bits program : List Bool}
    (hrelation : EncodedSearchRelation machine parameters bits program) :
    program.length ≤
      (descriptionPolynomial.comp (Polynomial.X + sourcePolynomial)).eval
        bits.length := by
  cases hdecode : MINKT.Instance.decode? bits with
  | none => simp [EncodedSearchRelation, hdecode] at hrelation
  | some inst =>
      simp only [EncodedSearchRelation, hdecode] at hrelation
      obtain ⟨optimum, hcomplexity, hlength, _hproduce⟩ := hrelation
      have hcanonical :=
        (MINKT.Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
      rw [hcanonical]
      have houtput : inst.output.length ≤ inst.encode.length := by
        rw [MINKT.Instance.length_encode_internal]
        omega
      have hoptimum := hsource inst optimum hcomplexity
      have hargument :
          inst.output.length + optimum ≤
            inst.encode.length + sourcePolynomial.eval inst.encode.length :=
        Nat.add_le_add houtput hoptimum
      calc
        program.length ≤
            parameters.description inst.output.length optimum := hlength
        _ ≤ descriptionPolynomial.eval (inst.output.length + optimum) :=
          hdescription inst.output.length optimum
        _ ≤ descriptionPolynomial.eval
            (inst.encode.length + sourcePolynomial.eval inst.encode.length) :=
          polynomial_eval_mono_nat descriptionPolynomial hargument
        _ = (descriptionPolynomial.comp
              (Polynomial.X + sourcePolynomial)).eval inst.encode.length := by
          simp [Polynomial.eval_comp]

/--
@isnad1 id=polybala.2h3v.s4.b0d8a0628edb from=translated src=- shape=e4ce152c vocab=3da5d9e5
-/
theorem encodedSearchRelation_polyBalanced_internal
    {tapes : ℕ} (machine : TM tapes) (parameters : Parameters)
    (hdescription : parameters.DescriptionPolyBound)
    (hsource : SourceComplexityPolyBound machine) :
    PolyBalanced (EncodedSearchRelation machine parameters) := by
  obtain ⟨descriptionPolynomial, hdescription⟩ := hdescription
  obtain ⟨sourcePolynomial, hsource⟩ := hsource
  exact ⟨descriptionPolynomial.comp (Polynomial.X + sourcePolynomial),
    fun _bits _program hrelation =>
      encodedSearchRelation_length_le_polynomial_internal
        machine parameters descriptionPolynomial sourcePolynomial
          hdescription hsource hrelation⟩

/--
@isnad1 id=sourceco.0h2v.s3.3ea9be18d980 from=translated src=- shape=b3b449db vocab=ae3e6f17
-/
theorem sourceComplexityPolyBound_internal {tapes : ℕ} (machine : TM tapes) :
    SourceComplexityPolyBound machine := by
  refine ⟨Polynomial.X, ?_⟩
  intro inst optimum hcomplexity
  have hfinite :
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ := by
    rw [hcomplexity]
    exact WithTop.coe_ne_top
  have htime := TM.timeBoundedKolmogorovComplexity_le_time_internal
    machine inst.output inst.time hfinite
  rw [hcomplexity] at htime
  have hoptimum : optimum ≤ inst.time := WithTop.coe_le_coe.mp htime
  simp only [Polynomial.eval_X]
  rw [MINKT.Instance.length_encode_internal]
  omega

/--
@isnad1 id=polybala.1h3v.s3.77abe91742fd from=translated src=- shape=9d0d0cf2 vocab=f6bf5d05
-/
theorem encodedSearchRelation_polyBalanced_of_description_internal
    {tapes : ℕ} (machine : TM tapes) (parameters : Parameters)
    (hdescription : parameters.DescriptionPolyBound) :
    PolyBalanced (EncodedSearchRelation machine parameters) :=
  encodedSearchRelation_polyBalanced_internal
    machine parameters hdescription (sourceComplexityPolyBound_internal machine)

/--
@isnad1 id=iff.0h5v.s4.0e025cf9f7fb from=translated src=- shape=a38f539d vocab=2286c926
-/
theorem verifyRelaxedWitness_eq_true_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance)
    (program : List Bool) :
    verifyRelaxedWitness machine parameters inst program = true ↔
      inst.IsRelaxedWitness machine parameters program := by
  simp [verifyRelaxedWitness, Instance.IsRelaxedWitness]

/--
@isnad1 id=iff.0h5v.s4.6d8032cb01eb from=translated src=- shape=b694c820 vocab=483ba35a
-/
theorem verifyRelaxedWitness_eq_false_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance)
    (program : List Bool) :
    verifyRelaxedWitness machine parameters inst program = false ↔
      ¬inst.IsRelaxedWitness machine parameters program := by
  rw [Bool.eq_false_iff]
  exact not_congr
    (verifyRelaxedWitness_eq_true_iff_internal machine parameters inst program)

/--
@isnad1 id=eq.3h5v.s5.8e5b4cf09f32 from=translated src=- shape=90b2d41b vocab=56740c27
-/
theorem decisionOfSearch_eq_true_of_mem_yesLanguage_internal
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    {search : SearchAlgorithm}
    (hdescription : parameters.DescriptionMonotone)
    (hsearch : SolvesSearchOnFinite machine parameters search)
    {bits : List Bool} (hyes : bits ∈ yesLanguage machine) :
    decisionOfSearch machine parameters search bits = true := by
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes : inst.IsYes machine := by
        simpa [yesLanguage, hdecode] using hyes
      change machine.timeBoundedKolmogorovComplexity inst.output inst.time ≤
        (inst.threshold : WithTop ℕ) at hisYes
      have hfinite :
          machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ := by
        intro htop
        rw [htop] at hisYes
        exact WithTop.not_top_le_coe inst.threshold hisYes
      obtain ⟨optimum, hcomplexity, hlength, hproduce⟩ :=
        hsearch inst.base hfinite
      change machine.timeBoundedKolmogorovComplexity inst.output inst.time =
        (optimum : WithTop ℕ) at hcomplexity
      change (search inst.base).length ≤
        parameters.description inst.output.length optimum at hlength
      change machine.ProducesInTime (search inst.base) inst.output
        (parameters.clock inst.output.length inst.time) at hproduce
      have hoptimum : optimum ≤ inst.threshold := by
        have hbound := hisYes
        rw [hcomplexity] at hbound
        exact WithTop.coe_le_coe.mp hbound
      have hrelaxed : inst.IsRelaxedWitness machine parameters (search inst.base) := by
        constructor
        · exact hlength.trans (hdescription inst.output.length hoptimum)
        · exact hproduce
      rw [decisionOfSearch, hdecode]
      exact (verifyRelaxedWitness_eq_true_iff_internal
        machine parameters inst (search inst.base)).mpr hrelaxed

/--
@isnad1 id=eq.1h5v.s5.b0b4ac5946a9 from=translated src=- shape=ac81ff11 vocab=d9a5ee40
-/
theorem decisionOfSearch_eq_false_of_mem_noLanguage_internal
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    (search : SearchAlgorithm) {bits : List Bool}
    (hno : bits ∈ noLanguage machine parameters) :
    decisionOfSearch machine parameters search bits = false := by
  cases hdecode : Instance.decode? bits with
  | none => simp [noLanguage, hdecode] at hno
  | some inst =>
      have hisNo : inst.IsNo machine parameters := by
        simpa [noLanguage, hdecode] using hno
      have hnone :=
        (Instance.isNo_iff_no_relaxedWitness_internal
          inst machine parameters).mp hisNo
      rw [decisionOfSearch, hdecode]
      exact (verifyRelaxedWitness_eq_false_iff_internal
        machine parameters inst (search inst.base)).mpr
          (fun hrelaxed => hnone ⟨search inst.base, hrelaxed⟩)

end GapMINKT

end Complexity
