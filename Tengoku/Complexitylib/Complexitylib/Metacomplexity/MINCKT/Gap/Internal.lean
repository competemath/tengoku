/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Gap.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Depth.Internal

/-!
# Gap conditional MinKT -- proof internals
-/

public section

namespace Complexity

private theorem withTopNat_add_le_add_internal
    {first second third fourth : WithTop ℕ}
    (hfirst : first ≤ third) (hsecond : second ≤ fourth) :
    first + second ≤ third + fourth := by
  induction first using WithTop.recTopCoe with
  | top =>
      have hthird : third = ⊤ := top_unique hfirst
      subst third
      simp
  | coe firstValue =>
      induction second using WithTop.recTopCoe with
      | top =>
          have hfourth : fourth = ⊤ := top_unique hsecond
          subst fourth
          simp
      | coe secondValue =>
          induction third using WithTop.recTopCoe with
          | top => simp
          | coe thirdValue =>
              induction fourth using WithTop.recTopCoe with
              | top => simp
              | coe fourthValue =>
                  exact WithTop.coe_le_coe.mpr <|
                    Nat.add_le_add (WithTop.coe_le_coe.mp hfirst)
                      (WithTop.coe_le_coe.mp hsecond)

private theorem withTopNat_le_add_right_internal
    (first second : WithTop ℕ) : first ≤ first + second := by
  calc
    first = first + 0 := (add_zero first).symm
    _ ≤ first + second :=
      withTopNat_add_le_add_internal le_rfl bot_le

namespace GapMINCKT

namespace Parameters

/--
@isnad1 id=isadmiss.0h0v.s1.1b175af4ad6b from=translated src=- shape=49959d42 vocab=2e3f71fe
-/
theorem identity_isAdmissible_internal : identity.IsAdmissible := by
  constructor
  · intro outputLength conditionLength time
    exact le_rfl
  · refine ⟨1, 1, ?_⟩
    intro outputLength conditionLength time
    simp [identity]
    omega

end Parameters

namespace Instance

variable {ordinaryTapes conditionalTapes : ℕ}

/--
@isnad1 id=eq.0h1v.s3.2ef10d703e70 from=translated src=- shape=981f0160 vocab=91876396
-/
theorem length_unaryThreshold_internal (inst : Instance) :
    inst.unaryThreshold.length = inst.threshold := by
  simp [unaryThreshold]

/--
@isnad1 id=eq.0h1v.s3.b49e6dcca4b5 from=translated src=- shape=edb93955 vocab=e2ce2480
-/
theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨output, condition, time, threshold⟩
  rw [encode, decode?, unpair?_pair]
  simp only [base, unaryThreshold]
  change (do
      let baseInst ← MINCKT.Instance.decode?
        ({ output := output
           condition := condition
           time := time } : MINCKT.Instance).encode
      if List.replicate threshold true =
          List.replicate (List.replicate threshold true).length true then
        some
          ({ output := baseInst.output
             condition := baseInst.condition
             time := baseInst.time
             threshold := (List.replicate threshold true).length } : Instance)
      else none) = some ({ output, condition, time, threshold } : Instance)
  rw [MINCKT.Instance.decode?_encode_internal]
  simp

/--
@isnad1 id=iff.0h2v.s4.71c5f740c7da from=translated src=- shape=94e3551a vocab=4b165dc4
-/
theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases hpair : unpair? bits with
    | none => simp [decode?, hpair] at hdecode
    | some components =>
        rcases components with ⟨baseBits, thresholdBits⟩
        cases hbase : MINCKT.Instance.decode? baseBits with
        | none => simp [decode?, hpair, hbase] at hdecode
        | some baseInst =>
            by_cases hthreshold :
                thresholdBits = List.replicate thresholdBits.length true
            · have hbits := eq_pair_of_unpair?_eq_some hpair
              rw [decode?, hpair] at hdecode
              change (MINCKT.Instance.decode? baseBits).bind (fun base =>
                  if thresholdBits = List.replicate thresholdBits.length true then
                    some
                      { output := base.output
                        condition := base.condition
                        time := base.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [hbase] at hdecode
              change (if thresholdBits =
                  List.replicate thresholdBits.length true then
                    some
                      { output := baseInst.output
                        condition := baseInst.condition
                        time := baseInst.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [ite_eq_left hthreshold] at hdecode
              cases hdecode
              have hbaseBits :=
                (MINCKT.Instance.decode?_eq_some_iff_internal
                  baseBits baseInst).mp hbase
              calc
                bits = pair baseBits thresholdBits := hbits
                _ = pair baseInst.encode thresholdBits := by rw [hbaseBits]
                _ = pair baseInst.encode
                    (List.replicate thresholdBits.length true) :=
                  congrArg (pair baseInst.encode) hthreshold
                _ = encode
                    { output := baseInst.output
                      condition := baseInst.condition
                      time := baseInst.time
                      threshold := thresholdBits.length } := rfl
            · rw [decode?, hpair] at hdecode
              change (MINCKT.Instance.decode? baseBits).bind (fun base =>
                  if thresholdBits = List.replicate thresholdBits.length true then
                    some
                      { output := base.output
                        condition := base.condition
                        time := base.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [hbase] at hdecode
              change (if thresholdBits =
                  List.replicate thresholdBits.length true then
                    some
                      { output := baseInst.output
                        condition := baseInst.condition
                        time := baseInst.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [ite_eq_right hthreshold] at hdecode
              contradiction
  · rintro rfl
    exact decode?_encode_internal inst

/--
@isnad1 id=iff.0h1v.s4.cb850aaff4b4 from=translated src=- shape=65444e03 vocab=aff63183
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
@isnad1 id=injectiv.0h0v.s2.08abf9f65d59 from=translated src=- shape=4b736592 vocab=22b722f4
-/
theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

/--
@isnad1 id=eq.0h1v.s6.15279e2d42cf from=translated src=- shape=f89ddee8 vocab=a18160ff
-/
theorem length_encode_internal (inst : Instance) :
    inst.encode.length =
      4 * inst.output.length + 4 * inst.condition.length +
        2 * inst.time + inst.threshold + 10 := by
  rw [encode, pair_length, length_unaryThreshold_internal,
    MINCKT.Instance.length_encode_internal]
  simp only [base]
  omega

/--
@isnad1 id=le.1h2v.s3.29b0bb82bad9 from=translated src=- shape=39a6aa4a vocab=dfd90baa
-/
theorem laterTime_ge_internal (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : Instance) :
    inst.time ≤ inst.laterTime parameters :=
  hwidening inst.output.length inst.condition.length inst.time

/--
@isnad1 id=eq.1h4v.s5.c87001c296aa from=translated src=- shape=9f526d5a vocab=bb11c54e
-/
theorem conditionDepth_add_later_internal (ordinaryMachine : TM ordinaryTapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening)
    (inst : Instance) :
    inst.conditionDepth ordinaryMachine parameters +
        ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
          (inst.laterTime parameters) =
      ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition inst.time :=
  TM.computationalDepthBetween_add_later_internal ordinaryMachine inst.condition
    (laterTime_ge_internal parameters hwidening inst)

/--
@isnad1 id=iff.0h6v.s5.cfd5c3239637 from=translated src=- shape=d33dd347 vocab=f8cb8274
-/
theorem isYes_iff_exists_adjustedWitness_internal (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) :
    inst.IsYes ordinaryMachine conditionalMachine parameters ↔
      ∃ program,
        inst.IsAdjustedWitness ordinaryMachine conditionalMachine parameters
          program := by
  constructor
  · intro hyes
    have hfinite : inst.base.complexity conditionalMachine ≠ ⊤ := by
      intro htop
      rw [IsYes, htop, WithTop.top_add] at hyes
      exact WithTop.not_top_le_coe inst.threshold hyes
    obtain ⟨program, hlength, hproduce⟩ :=
      OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_witness_internal
        conditionalMachine inst.output inst.condition inst.time hfinite
    refine ⟨program, ?_, hproduce⟩
    rw [hlength]
    exact hyes
  · rintro ⟨program, hbudget, hproduce⟩
    have hcomplexity :=
      OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_internal
        hproduce
    exact (withTopNat_add_le_add_internal hcomplexity le_rfl).trans hbudget

/--
@isnad1 id=isatmost.1h6v.s4.7b8728e77af6 from=translated src=- shape=024c94f3 vocab=5c44e253
-/
theorem isYes_implies_base_isAtMost_internal (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    inst.base.IsAtMost conditionalMachine inst.threshold := by
  exact (withTopNat_le_add_right_internal
    (inst.base.complexity conditionalMachine)
    (inst.conditionDepth ordinaryMachine parameters)).trans hyes

/--
@isnad1 id=iff.0h4v.s4.b7c1013638cd from=translated src=- shape=aa472f79 vocab=f351961f
-/
theorem isNo_iff_no_relaxedWitness_internal (inst : Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) :
    inst.IsNo conditionalMachine parameters ↔
      ¬∃ program, inst.IsRelaxedWitness conditionalMachine parameters program := by
  constructor
  · intro hno ⟨program, hlength, hproduce⟩
    have hcomplexity :=
      (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_internal
        hproduce).trans (WithTop.coe_le_coe.mpr hlength)
    exact (not_lt_of_ge hcomplexity) hno
  · intro hnone
    apply lt_of_not_ge
    intro hcomplexity
    obtain ⟨program, hlength, hproduce⟩ :=
      (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
        conditionalMachine inst.output inst.condition
          (inst.laterTime parameters)
          (inst.threshold + inst.logSlack parameters)).mp hcomplexity
    exact hnone ⟨program, hlength, hproduce⟩

/--
@isnad1 id=isyes.2h8v.s5.4f735a6c1705 from=translated src=- shape=da2df3b2 vocab=d06c7a4a
-/
theorem IsYes.withThreshold_mono_internal (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hyes : (inst.withThreshold first).IsYes ordinaryMachine
      conditionalMachine parameters) :
    (inst.withThreshold second).IsYes ordinaryMachine conditionalMachine
      parameters := by
  exact hyes.trans (WithTop.coe_le_coe.mpr hthreshold)

/--
@isnad1 id=isno.2h6v.s5.cca899d4fac3 from=translated src=- shape=bdd676b9 vocab=5271bc02
-/
theorem IsNo.withThreshold_anti_internal (inst : Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hno : (inst.withThreshold second).IsNo conditionalMachine parameters) :
    (inst.withThreshold first).IsNo conditionalMachine parameters := by
  exact lt_of_le_of_lt
    (WithTop.coe_le_coe.mpr
      (Nat.add_le_add_right hthreshold (inst.logSlack parameters))) hno

/--
@isnad1 id=not.2h6v.s4.632e07b2d81a from=translated src=- shape=e3eb40b2 vocab=5538c59a
-/
theorem not_isNo_of_isYes_internal (inst : Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    ¬inst.IsNo conditionalMachine parameters := by
  intro hno
  have hsource := isYes_implies_base_isAtMost_internal inst ordinaryMachine
    conditionalMachine parameters hyes
  have hclock :=
    OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
      conditionalMachine inst.output inst.condition
        (laterTime_ge_internal parameters hwidening inst)
  have hslack : (inst.threshold : WithTop ℕ) ≤
      (inst.threshold + inst.logSlack parameters : ℕ) :=
    WithTop.coe_le_coe.mpr (Nat.le_add_right _ _)
  exact (not_lt_of_ge (hclock.trans (hsource.trans hslack))) hno

end Instance

/--
@isnad1 id=le.2h7v.s5.7da71c359f94 from=translated src=- shape=a5928eae vocab=467dbe04
-/
theorem estimator_le_threshold_of_isYes_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters)
    (inst : Instance)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    estimate inst.base ≤ inst.threshold := by
  have hupper := (hestimate inst.base).1
  have hyes' :
      inst.base.complexity conditionalMachine +
          ordinaryMachine.computationalDepthBetween inst.condition inst.time
            (parameters.transformedTime inst.base) ≤
        (inst.threshold : WithTop ℕ) := by
    simpa [Instance.IsYes, Instance.conditionDepth, Instance.laterTime] using
      hyes
  exact WithTop.coe_le_coe.mp (hupper.trans hyes')

/--
@isnad1 id=lt.2h7v.s5.4c3900eee022 from=translated src=- shape=e1ad7b8b vocab=16fe30c2
-/
theorem threshold_lt_estimator_of_isNo_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters)
    (inst : Instance) (hno : inst.IsNo conditionalMachine parameters) :
    inst.threshold < estimate inst.base := by
  apply Nat.lt_of_not_ge
  intro hthreshold
  have hlower := (hestimate inst.base).2
  have hsum :
      estimate inst.base + parameters.logarithmicSlack inst.base ≤
        inst.threshold + parameters.logarithmicSlack inst.base :=
    Nat.add_le_add_right hthreshold _
  have hlater :
      (inst.base.withTime (parameters.transformedTime inst.base)).complexity
          conditionalMachine ≤
        (inst.threshold + parameters.logarithmicSlack inst.base : ℕ) :=
    hlower.trans (WithTop.coe_le_coe.mpr hsum)
  have hno' :
      (inst.threshold + parameters.logarithmicSlack inst.base : ℕ) <
        (inst.base.withTime (parameters.transformedTime inst.base)).complexity
          conditionalMachine := by
    simpa [Instance.IsNo, Instance.laterTime, Instance.logSlack] using hno
  exact (not_lt_of_ge hlater) hno'

/--
@isnad1 id=iff.0h6v.s5.7ae08b81986e from=translated src=- shape=72d4b66b vocab=0abb2a65
-/
theorem yesLanguage_mem_encode_iff_internal
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (inst : Instance) :
    inst.encode ∈ yesLanguage ordinaryMachine conditionalMachine parameters ↔
      inst.IsYes ordinaryMachine conditionalMachine parameters := by
  simp [yesLanguage, Instance.decode?_encode_internal]

/--
@isnad1 id=iff.0h4v.s4.9ce1488e91dc from=translated src=- shape=c66ee9b8 vocab=8de6cb9f
-/
theorem noLanguage_mem_encode_iff_internal {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (inst : Instance) :
    inst.encode ∈ noLanguage conditionalMachine parameters ↔
      inst.IsNo conditionalMachine parameters := by
  simp [noLanguage, Instance.decode?_encode_internal]

/--
@isnad1 id=disjoint.1h5v.s5.ca405b6a6998 from=translated src=- shape=0be29178 vocab=b9a709dc
-/
theorem disjoint_yesLanguage_noLanguage_internal
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : Parameters) (hwidening : parameters.IsWidening) :
    Disjoint (yesLanguage ordinaryMachine conditionalMachine parameters)
      (noLanguage conditionalMachine parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hyes hno
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes :
          inst.IsYes ordinaryMachine conditionalMachine parameters := by
        simpa [yesLanguage, hdecode] using hyes
      have hisNo : inst.IsNo conditionalMachine parameters := by
        simpa [noLanguage, hdecode] using hno
      exact Instance.not_isNo_of_isYes_internal inst ordinaryMachine
        conditionalMachine parameters hwidening hisYes hisNo

/--
@isnad1 id=iff.0h2v.s4.f35bde14789c from=translated src=- shape=e31b9f63 vocab=196f2eec
-/
theorem estimatorLanguage_mem_encode_iff_internal (estimate : Estimator)
    (inst : Instance) :
    inst.encode ∈ estimatorLanguage estimate ↔
      estimate inst.base ≤ inst.threshold := by
  simp [estimatorLanguage, Instance.decode?_encode_internal]

/--
@isnad1 id=iff.0h2v.s4.f00559f1c3a8 from=translated src=- shape=f2f3bfeb vocab=49d2fc34
-/
theorem decisionOfEstimator_eq_true_iff_internal (estimate : Estimator)
    (bits : List Bool) :
    decisionOfEstimator estimate bits = true ↔
      bits ∈ estimatorLanguage estimate := by
  cases hdecode : Instance.decode? bits with
  | none => simp [decisionOfEstimator, estimatorLanguage, hdecode]
  | some inst => simp [decisionOfEstimator, estimatorLanguage, hdecode]

/--
@isnad1 id=le.1h6v.s5.b59c7ba47c79 from=translated src=- shape=d747c9c7 vocab=a8333aee
-/
theorem yesLanguage_subset_estimatorLanguage_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) :
    yesLanguage ordinaryMachine conditionalMachine parameters ⊆
      estimatorLanguage estimate := by
  intro bits hyes
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes :
          inst.IsYes ordinaryMachine conditionalMachine parameters := by
        simpa [yesLanguage, hdecode] using hyes
      have hbound := estimator_le_threshold_of_isYes_internal
        hestimate inst hisYes
      simpa [estimatorLanguage, hdecode] using hbound

/--
@isnad1 id=disjoint.1h6v.s5.cebee76c1dc0 from=translated src=- shape=ed9c0c91 vocab=b7c8d472
-/
theorem disjoint_estimatorLanguage_noLanguage_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) :
    Disjoint (estimatorLanguage estimate)
      (noLanguage conditionalMachine parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hestimateLanguage hno
  cases hdecode : Instance.decode? bits with
  | none => simp [estimatorLanguage, hdecode] at hestimateLanguage
  | some inst =>
      have hle : estimate inst.base ≤ inst.threshold := by
        simpa [estimatorLanguage, hdecode] using hestimateLanguage
      have hisNo : inst.IsNo conditionalMachine parameters := by
        simpa [noLanguage, hdecode] using hno
      have hlt := threshold_lt_estimator_of_isNo_internal
        hestimate inst hisNo
      omega

/--
@isnad1 id=eq.2h7v.s5.0454d41d138b from=translated src=- shape=c7426dfc vocab=d8b62c67
-/
theorem decisionOfEstimator_eq_true_of_mem_yesLanguage_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) {bits : List Bool}
    (hyes : bits ∈ yesLanguage ordinaryMachine conditionalMachine parameters) :
    decisionOfEstimator estimate bits = true :=
  (decisionOfEstimator_eq_true_iff_internal estimate bits).mpr
    (yesLanguage_subset_estimatorLanguage_internal hestimate hyes)

/--
@isnad1 id=eq.2h7v.s5.79b8f3931245 from=translated src=- shape=6f12bc4a vocab=d4130c3d
-/
theorem decisionOfEstimator_eq_false_of_mem_noLanguage_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {estimate : Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters) {bits : List Bool}
    (hno : bits ∈ noLanguage conditionalMachine parameters) :
    decisionOfEstimator estimate bits = false := by
  cases hvalue : decisionOfEstimator estimate bits with
  | false => rfl
  | true =>
      have hmem :=
        (decisionOfEstimator_eq_true_iff_internal estimate bits).mp hvalue
      exact (Set.disjoint_left.mp
        (disjoint_estimatorLanguage_noLanguage_internal hestimate)
          hmem hno).elim

end GapMINCKT

end Complexity
