/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Universality.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.ListDecoding.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Oracle.Internal
import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.OutputSemantics.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Internal

/-!
# List decoding explicit NW reconstruction programs -- proof internals
-/

public section

namespace Complexity

namespace NWDesign

/--
@isnad1 id=eq.0h6v.s5.dfbc3c7a9b64 from=translated src=- shape=85817bb0 vocab=4d9b7828
-/
theorem IndexedReconstructionProgram.length_encodeBooleanPayload_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    program.encodeBooleanPayload.length =
      design.reconstructionDataBitsAt program.reconstruction.current +
        BooleanListCode.decoderIndexBitWidth listSize := by
  simp [IndexedReconstructionProgram.encodeBooleanPayload,
    Complexity.NWDesign.length_encodeBooleanPayload_internal,
    BooleanListCode.length_encodeDecoderIndex_internal]

/--
@isnad1 id=eq.0h6v.s6.a7b08ccbb788 from=translated src=- shape=87f1cfe3 vocab=d6925ae3
-/
theorem IndexedReconstructionProgram.length_encode_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    program.encode.length =
      1 + Fin.bitWidth outputLength +
        design.reconstructionDataBitsAt program.reconstruction.current +
          BooleanListCode.decoderIndexBitWidth listSize := by
  simp [IndexedReconstructionProgram.encode,
    IndexedReconstructionProgram.length_encodeBooleanPayload_internal]
  omega

/--
@isnad1 id=eq.0h6v.s6.6f746bd986c7 from=translated src=- shape=24d95d38 vocab=82de047d
-/
theorem decodeIndexedReconstructionBooleanPayload?_encode_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    decodeIndexedReconstructionBooleanPayload? design listSize
      program.reconstruction.complement program.reconstruction.current
        program.encodeBooleanPayload = some program := by
  simp [decodeIndexedReconstructionBooleanPayload?,
    IndexedReconstructionProgram.encodeBooleanPayload,
    Complexity.NWDesign.length_encodeBooleanPayload_internal,
    decodeReconstructionBooleanPayload?_encode_internal,
    BooleanListCode.decodeDecoderIndex?_encodeDecoderIndex_internal]

/--
@isnad1 id=eq.0h6v.s5.6ed806a648f8 from=translated src=- shape=070ec3d7 vocab=20399db4
-/
theorem decodeIndexedReconstructionProgram?_encode_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    decodeIndexedReconstructionProgram? design listSize program.encode =
      some program := by
  simp [decodeIndexedReconstructionProgram?,
    IndexedReconstructionProgram.encode,
    decodeIndexedReconstructionBooleanPayload?_encode_internal]

/--
@isnad1 id=eq.0h9v.s6.f296f6545bad from=translated src=- shape=de9034d1 vocab=5097a3f4
-/
theorem decodeIndexedMessage?_encode_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (test : Finset (Fin outputLength → Bool)) :
    decodeIndexedMessage? design code test program.encode =
      some (program.decodedMessage code test) := by
  simp [decodeIndexedMessage?,
    decodeIndexedReconstructionProgram?_encode_internal]

/--
@isnad1 id=le.1h11v.s6.77b6d533cb29 from=translated src=- shape=1f39f735 vocab=c9be9f27
-/
theorem HasEncodedMessageCertificateWithin.timeBoundedKolmogorovComplexity_le_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : EncodedMessageDecoderRealization design code test)
    (hcertificate : HasEncodedMessageCertificateWithin
      design code test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (List.ofFn message) (realization.time bound) ≤
      (bound : WithTop ℕ) := by
  obtain ⟨description, hdecode, hlength⟩ := hcertificate
  have hproduce := realization.correct description message hdecode
  have hproduceBound := TM.producesInTime_mono_internal
    (realization.time_mono hlength) hproduce
  exact le_trans
    (TM.timeBoundedKolmogorovComplexity_le_internal hproduceBound)
    (by exact_mod_cast hlength)

namespace HasEncodedMessageCertificateWithin

/--
@isnad1 id=le.1h11v.s6.8d8c8fc497f4 from=translated src=- shape=168e76b2 vocab=c07e7f8c
-/
theorem oracleTimeBoundedKolmogorovComplexity_le_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : OracleEncodedMessageDecoderRealization design code)
    (hcertificate : HasEncodedMessageCertificateWithin
      design code test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (finiteTestOracle test) (List.ofFn message) (realization.time bound) ≤
      (bound : WithTop ℕ) := by
  obtain ⟨description, hdecode, hlength⟩ := hcertificate
  have hproduce := realization.correct test description message hdecode
  have hproduceBound := hproduce.mono (realization.time_mono hlength)
  exact le_trans
    (OracleTM.timeBoundedKolmogorovComplexity_le_internal hproduceBound)
    (by exact_mod_cast hlength)

end HasEncodedMessageCertificateWithin

namespace OracleEncodedMessageDecoderRealization

/--
@isnad1 id=ex.1h10v.s7.6510d00bde15 from=translated src=- shape=87d408c8 vocab=4118215c
-/
theorem efficientlyUniversal_transfer_internal
    {messageLength listSize outputLength inputLength seedLength
      universalTapes : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    (realization : OracleEncodedMessageDecoderRealization design code)
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal) :
    ∃ constant coefficient exponent,
      ∀ (test : Finset (Fin outputLength → Bool))
        (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design code test message bound →
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle test) (List.ofFn message)
              (coefficient *
                (bound + realization.time bound + 1) ^ exponent) ≤
            (bound + constant : ℕ) := by
  obtain ⟨compile, constant, clock, -, _hsim, hlength, htimed, hclock⟩ :=
    huniversal realization.tapes realization.machine
  obtain ⟨coefficient, exponent, htransfer⟩ :=
    OracleTM.polynomialTimeOverhead_kolmogorov_transfer_internal
      htimed hlength hclock
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro test message bound hcertificate
  exact htransfer (finiteTestOracle test) (List.ofFn message)
    (realization.time bound) bound
    (hcertificate.oracleTimeBoundedKolmogorovComplexity_le_internal
      realization)

end OracleEncodedMessageDecoderRealization

/--
@isnad1 id=ex.1h11v.s7.7c03b60cd02c from=translated src=- shape=c30128af vocab=b959be81
-/
theorem EncodedMessageDecoderRealization.efficientlyUniversal_transfer_internal
    {messageLength listSize outputLength inputLength seedLength
      universalTapes : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {test : Finset (Fin outputLength → Bool)}
    (realization : EncodedMessageDecoderRealization design code test)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent,
      ∀ (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design code test message bound →
          universal.timeBoundedKolmogorovComplexity (List.ofFn message)
              (coefficient *
                (bound + realization.time bound + 1) ^ exponent) ≤
            (bound + constant : ℕ) := by
  obtain ⟨compile, constant, clock, -, _hsim, hlength, htimed, hclock⟩ :=
    huniversal realization.tapes realization.machine
  obtain ⟨coefficient, exponent, htransfer⟩ :=
    TM.polynomialTimeOverhead_kolmogorov_transfer_internal
      htimed hlength hclock
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro message bound hcertificate
  exact htransfer (List.ofFn message) (realization.time bound) bound
    (HasEncodedMessageCertificateWithin.timeBoundedKolmogorovComplexity_le_internal
      realization hcertificate)

/--
@isnad1 id=eq.0h10v.s6.5a4cd241ff54 from=translated src=- shape=78b439df vocab=d4d62ad9
-/
theorem ReconstructionProgram.agreementProbability_eq_listCode_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) :
    program.agreementProbability (code.encode message) test =
      BooleanListCode.agreementProbability (code.encode message)
        (program.predictor test) := by
  unfold ReconstructionProgram.agreementProbability
  unfold BooleanListCode.agreementProbability
  congr 1
  ext challenge
  simp [eq_comm]

/--
@isnad1 id=and.2h11v.s7.9c38f0947d74 from=translated src=- shape=8c64539c vocab=3ad4673a
-/
theorem ReconstructionProgram.mem_listDecoderCandidates_and_card_le_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hagreement : 1 / 2 + margin ≤
      program.agreementProbability (code.encode message) test) :
    message ∈ program.listDecoderCandidates code test ∧
      (program.listDecoderCandidates code test).card ≤ listSize := by
  have hresult :=
    BooleanListCode.mem_candidates_and_card_le_of_half_add_margin_internal
      hcode message (program.predictor test) (by
        rwa [← program.agreementProbability_eq_listCode_internal])
  simpa [ReconstructionProgram.listDecoderCandidates] using hresult

/--
@isnad1 id=ex.2h11v.s7.96069fa3d573 from=translated src=- shape=fdc61bd3 vocab=0aeea208
-/
theorem ReconstructionProgram.exists_indexedProgram_of_half_add_margin_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hagreement : 1 / 2 + margin ≤
      program.agreementProbability (code.encode message) test) :
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction = program ∧
        indexed.decodedMessage code test = message ∧
          indexed.encodeBooleanPayload.length =
            program.encodeBooleanPayload.length +
              BooleanListCode.decoderIndexBitWidth listSize := by
  have hcodeAgreement : 1 / 2 + margin ≤
      BooleanListCode.agreementProbability (code.encode message)
        (program.predictor test) := by
    rwa [← program.agreementProbability_eq_listCode_internal]
  have hradius : 1 - (1 / 2 - margin) ≤
      BooleanListCode.agreementProbability (code.encode message)
        (program.predictor test) := by
    convert hcodeAgreement using 1
    ring
  obtain ⟨index, hdecode⟩ :=
    BooleanListCode.exists_decoder_index_of_agreementProbability_ge_internal
      hcode message (program.predictor test) hradius
  refine ⟨{ reconstruction := program, decoderIndex := index }, rfl,
    hdecode, ?_⟩
  simp [IndexedReconstructionProgram.encodeBooleanPayload,
    BooleanListCode.length_encodeDecoderIndex_internal]

/--
@isnad1 id=ex.3h14v.s8.f066f6ba11a7 from=translated src=- shape=bf1ad31b vocab=7a4e956c
-/
theorem findGoodReconstructionCertificate_indexedProgram_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction =
          certificate.toProgram design (code.encode message) ∧
        indexed.decodedMessage code test = message ∧
          indexed.encodeBooleanPayload.length ≤
            budget + (seedLength - inputLength) + 1 +
              BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hagreement, hpayload⟩ :=
    findGoodReconstructionCertificate_encodedProgram_sound_internal design
      (code.encode message) test (1 / 2 + margin) hbudget batch
      certificate hfind
  obtain ⟨indexed, hreconstruction, hdecode, hlength⟩ :=
    (certificate.toProgram design
      (code.encode message)).exists_indexedProgram_of_half_add_margin_internal
        code message test margin hcode hagreement
  refine ⟨indexed, hreconstruction, hdecode, ?_⟩
  rw [hlength]
  exact Nat.add_le_add_right hpayload _

/--
@isnad1 id=ex.3h14v.s8.faee2ee8fa2f from=translated src=- shape=bd6283f5 vocab=04f5b20c
-/
theorem findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction =
          certificate.toProgram design (code.encode message) ∧
        indexed.decodedMessage code test = message ∧
          indexed.encode.length ≤
            1 + Fin.bitWidth outputLength +
              (budget + (seedLength - inputLength) + 1) +
                BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨indexed, hreconstruction, hdecode, hpayload⟩ :=
    findGoodReconstructionCertificate_indexedProgram_sound_internal
      design code message test margin hcode hbudget batch certificate hfind
  refine ⟨indexed, hreconstruction, hdecode, ?_⟩
  simp only [IndexedReconstructionProgram.encode, List.length_cons,
    List.length_append, Fin.length_toBits]
  omega

/--
@isnad1 id=ex.3h14v.s7.340372a098fd from=translated src=- shape=6d3bd817 vocab=bdd0a412
-/
theorem findGoodReconstructionCertificate_encodedMessage_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    ∃ description : List Bool,
      decodeIndexedMessage? design code test description = some message ∧
        description.length ≤
          1 + Fin.bitWidth outputLength +
            (budget + (seedLength - inputLength) + 1) +
              BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨indexed, _hreconstruction, hdecode, hlength⟩ :=
    findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
      design code message test margin hcode hbudget batch certificate hfind
  refine ⟨indexed.encode, ?_, hlength⟩
  rw [decodeIndexedMessage?_encode_internal, hdecode]

/--
@isnad1 id=and.3h14v.s8.5e38d5fed8be from=translated src=- shape=e694716a vocab=27fb4e27
-/
theorem findGoodReconstructionCertificate_listDecoding_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    message ∈ (certificate.toProgram design
        (code.encode message)).listDecoderCandidates code test ∧
      ((certificate.toProgram design
        (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
      (certificate.toProgram design
        (code.encode message)).encodeBooleanPayload.length ≤
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hagreement, hpayload⟩ :=
    findGoodReconstructionCertificate_encodedProgram_sound_internal design
      (code.encode message) test (1 / 2 + margin) hbudget batch
      certificate hfind
  obtain ⟨hmessage, hcard⟩ :=
    (certificate.toProgram design
      (code.encode message)).mem_listDecoderCandidates_and_card_le_internal
        code message test margin hcode hagreement
  exact ⟨hmessage, hcard, hpayload⟩

/--
@isnad1 id=and.7h15v.s8.ba9fadb7de98 from=translated src=- shape=6ca5f46d vocab=b424aa00
-/
theorem half_le_listDecodedReconstructionProgram_of_randomTest_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator (code.encode message)).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        message ∈ (certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test ∧
          ((certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
          (certificate.toProgram design
            (code.encode message)).encodeBooleanPayload.length ≤
              budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_listDecoding_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

/--
@isnad1 id=and.7h15v.s8.c96685e6186c from=translated src=- shape=fb0f2e45 vocab=d9a36a0a
-/
theorem half_le_indexedReconstructionProgram_of_randomTest_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator (code.encode message)).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encodeBooleanPayload.length ≤
                budget + (seedLength - inputLength) + 1 +
                  BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_indexedProgram_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

/--
@isnad1 id=and.7h15v.s8.5d837d199d26 from=translated src=- shape=275e3460 vocab=745f1e85
-/
theorem half_le_fullyEncodedIndexedReconstructionProgram_of_randomTest_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator (code.encode message)).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength - inputLength) + 1) +
                    BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_indexedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hcode hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact
    findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
      design code message test ((density / (outputLength : ℚ)) / 2)
        hcode hbudget batch certificate hfind

/--
@isnad1 id=and.8h15v.s9.ab601c100882 from=translated src=- shape=9c624260 vocab=4b838474
-/
theorem half_le_listDecodedReconstructionProgram_of_seedDescriptions_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator (code.encode message) seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        message ∈ (certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test ∧
          ((certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
          (certificate.toProgram design
            (code.encode message)).encodeBooleanPayload.length ≤
              budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_listDecoding_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

/--
@isnad1 id=and.8h15v.s8.2ac936c72e49 from=translated src=- shape=136e6458 vocab=353f63c2
-/
theorem half_le_indexedReconstructionProgram_of_seedDescriptions_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator (code.encode message) seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encodeBooleanPayload.length ≤
                budget + (seedLength - inputLength) + 1 +
                  BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_indexedProgram_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

end NWDesign

end Complexity
