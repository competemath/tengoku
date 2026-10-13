/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Encoding.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Internal

/-!
# Bit encoding of explicit NW reconstruction programs -- proof internals
-/

public section

namespace Complexity

namespace NWDesign

/--
@isnad1 id=eq.0h5v.s9.c393d08aac4b from=translated src=- shape=73bd1bfe vocab=3b2cd2d1
-/
theorem card_reconstructionPayloadIndex_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    Fintype.card (ReconstructionPayloadIndex design current) =
      design.reconstructionDataBitsAt current := by
  simp [ReconstructionPayloadIndex,
    ReconstructionPredecessorPayloadIndex,
    BooleanDependency.OrderedAssignment.card_internal,
    reconstructionDataBitsAt, predecessorTableEntriesAt]
  have hsum := Finset.sum_attach (Finset.Iio current)
    (fun previous =>
      2 ^ (design.challengeOverlap current previous).card)
  rw [hsum]
  omega

/--
@isnad1 id=eq.0h5v.s5.778229caa02a from=translated src=- shape=f7fa98fc vocab=1be914ea
-/
theorem length_encodeBooleanPayload_internal
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encodeBooleanPayload.length =
      design.reconstructionDataBitsAt program.current := by
  unfold ReconstructionProgram.encodeBooleanPayload
  rw [BooleanDependency.length_encodeOrderedFunction_internal,
    card_reconstructionPayloadIndex_internal]

/--
@isnad1 id=eq.0h5v.s5.24f526392339 from=translated src=- shape=981cb501 vocab=61a1db69
-/
theorem length_encodeBooleanPayload_eq_booleanPayloadSize_internal
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encodeBooleanPayload.length = program.booleanPayloadSize := by
  rw [length_encodeBooleanPayload_internal,
    ReconstructionProgram.booleanPayloadSize_eq_internal]

/--
@isnad1 id=eq.0h5v.s5.095eb1a22e87 from=translated src=- shape=a6be608f vocab=f2cc2624
-/
theorem ReconstructionProgram.length_encode_internal
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encode.length =
      1 + Fin.bitWidth outputLength +
        design.reconstructionDataBitsAt program.current := by
  simp [ReconstructionProgram.encode,
    Complexity.NWDesign.length_encodeBooleanPayload_internal]
  omega

/--
@isnad1 id=eq.0h5v.s5.373a18948619 from=translated src=- shape=102a4b17 vocab=bd784d18
-/
theorem decodeReconstructionBooleanPayload?_encode_internal
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    decodeReconstructionBooleanPayload? design program.complement
      program.current program.encodeBooleanPayload = some program := by
  cases program with
  | mk complement current predecessor outside later candidate =>
      simp [decodeReconstructionBooleanPayload?,
        ReconstructionProgram.encodeBooleanPayload,
        BooleanDependency.decodeOrderedFunction?_encodeOrderedFunction_internal,
        ReconstructionProgram.booleanPayload, predecessorPayloadIndex,
        outsidePayloadIndex, laterPayloadIndex, candidatePayloadIndex]

/--
@isnad1 id=eq.0h5v.s5.357c05b17565 from=translated src=- shape=f2b83de1 vocab=a3145f7f
-/
theorem decodeReconstructionProgram?_encode_internal
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    decodeReconstructionProgram? design program.encode = some program := by
  simp [decodeReconstructionProgram?, ReconstructionProgram.encode,
    decodeReconstructionBooleanPayload?_encode_internal]

/--
@isnad1 id=iff.0h7v.s5.e195f4a5d885 from=translated src=- shape=6b92876a vocab=7c0e6264
-/
theorem decodeReconstructionBooleanPayload?_eq_none_iff_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (complement : Bool) (current : Fin outputLength) (bits : List Bool) :
    decodeReconstructionBooleanPayload? design complement current bits = none ↔
      bits.length ≠ design.reconstructionDataBitsAt current := by
  unfold decodeReconstructionBooleanPayload?
  cases hdecode : BooleanDependency.decodeOrderedFunction?
      (index := ReconstructionPayloadIndex design current) bits with
  | none =>
      have hlength :=
        (BooleanDependency.decodeOrderedFunction?_eq_none_iff_internal
          (index := ReconstructionPayloadIndex design current) bits).mp hdecode
      rw [card_reconstructionPayloadIndex_internal] at hlength
      constructor
      · intro _hdecode
        exact hlength
      · intro _hlength
        rfl
  | some payload =>
      have hlength :
          bits.length = design.reconstructionDataBitsAt current := by
        by_contra hne
        have hnone :=
          (BooleanDependency.decodeOrderedFunction?_eq_none_iff_internal
            (index := ReconstructionPayloadIndex design current) bits).mpr (by
              rwa [card_reconstructionPayloadIndex_internal])
        rw [hdecode] at hnone
        contradiction
      constructor
      · intro hnone
        contradiction
      · intro hne
        exact (hne hlength).elim

/--
@isnad1 id=and.2h11v.s7.20b55feba707 from=translated src=- shape=3194d4bb vocab=5ea5a23f
-/
theorem findGoodReconstructionCertificate_encodedProgram_sound_internal
    {outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? hardFunction test
      agreementThreshold batch = some certificate) :
    agreementThreshold ≤
        (certificate.toProgram design hardFunction).agreementProbability
          hardFunction test ∧
      (certificate.toProgram design hardFunction).encodeBooleanPayload.length ≤
        budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hagreement, hsize⟩ :=
    findGoodReconstructionCertificate_program_sound_internal design
      hardFunction test agreementThreshold hbudget batch certificate hfind
  exact ⟨hagreement, by
    rw [length_encodeBooleanPayload_eq_booleanPayloadSize_internal]
    exact hsize⟩

/--
@isnad1 id=and.2h11v.s7.2a7349465568 from=translated src=- shape=b616bb91 vocab=cd10194e
-/
theorem findGoodReconstructionCertificate_fullyEncodedProgram_sound_internal
    {outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ)
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? hardFunction test
      agreementThreshold batch = some certificate) :
    agreementThreshold ≤
        (certificate.toProgram design hardFunction).agreementProbability
          hardFunction test ∧
      (certificate.toProgram design hardFunction).encode.length ≤
        1 + Fin.bitWidth outputLength +
          (budget + (seedLength - inputLength) + 1) := by
  obtain ⟨hagreement, hpayload⟩ :=
    findGoodReconstructionCertificate_encodedProgram_sound_internal design
      hardFunction test agreementThreshold hbudget batch certificate hfind
  refine ⟨hagreement, ?_⟩
  simp only [ReconstructionProgram.encode, List.length_cons,
    List.length_append, Fin.length_toBits]
  omega

/--
@isnad1 id=and.6h12v.s8.4577b9005a9b from=translated src=- shape=b020fbbd vocab=2e887945
-/
theorem half_le_encodedReconstructionProgram_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).encodeBooleanPayload.length ≤
            budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_checkedReconstructionBatch_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_encodedProgram_sound_internal
    design hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

/--
@isnad1 id=and.6h12v.s8.a3cbba1b316a from=translated src=- shape=1e078cb7 vocab=28816432
-/
theorem half_le_fullyEncodedReconstructionProgram_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).encode.length ≤
            1 + Fin.bitWidth outputLength +
              (budget + (seedLength - inputLength) + 1) := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_fullyEncodedProgram_sound_internal
    design hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

/--
@isnad1 id=and.7h12v.s8.d368a81fa4cc from=translated src=- shape=184c85e8 vocab=856c8656
-/
theorem half_le_encodedReconstructionProgram_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density) (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).encodeBooleanPayload.length ≤
            budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_checkedReconstructionBatch_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_encodedProgram_sound_internal
    design hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

/--
@isnad1 id=and.7h12v.s8.fdd7c76a323c from=translated src=- shape=f019b27b vocab=365de149
-/
theorem half_le_fullyEncodedReconstructionProgram_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density) (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability hardFunction test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? hardFunction test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        1 / 2 + (density / (outputLength : ℚ)) / 2 ≤
            (certificate.toProgram design hardFunction).agreementProbability
              hardFunction test ∧
          (certificate.toProgram design hardFunction).encode.length ≤
            1 + Fin.bitWidth outputLength +
              (budget + (seedLength - inputLength) + 1) := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_fullyEncodedProgram_sound_internal
    design hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

end NWDesign

end Complexity
