/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Internal

/-!
# Bit encoding of explicit NW reconstruction programs

The stored predecessor tables, outside seed, later tail, and candidate are
serialized as one canonical flat bit string. A complete program encoding
prefixes its polarity and a ceiling-logarithmic hybrid coordinate, leaving
only the ambient design parameters external to the decoder.
-/

public section

namespace Complexity

namespace NWDesign

/-- The total payload-index type has exactly the previously derived number of
Boolean reconstruction entries.
@isnad1 id=eq.0h5v.s9.c393d08aac4b from=translated src=- shape=73bd1bfe vocab=3b2cd2d1
-/
theorem card_reconstructionPayloadIndex
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    Fintype.card (ReconstructionPayloadIndex design current) =
      design.reconstructionDataBitsAt current :=
  card_reconstructionPayloadIndex_internal design current

/-- The canonical flat payload has exactly the reconstruction entry count.
@isnad1 id=eq.0h5v.s5.778229caa02a from=translated src=- shape=f7fa98fc vocab=1be914ea
-/
@[simp] theorem length_encodeBooleanPayload
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encodeBooleanPayload.length =
      design.reconstructionDataBitsAt program.current :=
  length_encodeBooleanPayload_internal program

/-- Flat payload length agrees exactly with the explicit program's semantic
Boolean payload size.
@isnad1 id=eq.0h5v.s5.24f526392339 from=translated src=- shape=981cb501 vocab=61a1db69
-/
theorem length_encodeBooleanPayload_eq_booleanPayloadSize
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encodeBooleanPayload.length = program.booleanPayloadSize :=
  length_encodeBooleanPayload_eq_booleanPayloadSize_internal program

/-- A complete reconstruction-program encoding pays one polarity bit and a
ceiling-logarithmic hybrid coordinate beyond its Boolean payload.
@isnad1 id=eq.0h5v.s5.095eb1a22e87 from=translated src=- shape=a6be608f vocab=f2cc2624
-/
@[simp] theorem ReconstructionProgram.length_encode
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.encode.length =
      1 + Fin.bitWidth outputLength +
        design.reconstructionDataBitsAt program.current :=
  program.length_encode_internal

/-- Exact round trip for the reconstruction Boolean payload when its polarity
and coordinate metadata are supplied.
@isnad1 id=eq.0h5v.s5.373a18948619 from=translated src=- shape=102a4b17 vocab=bd784d18
-/
@[simp] theorem decodeReconstructionBooleanPayload?_encode
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    decodeReconstructionBooleanPayload? design program.complement
      program.current program.encodeBooleanPayload = some program :=
  decodeReconstructionBooleanPayload?_encode_internal program

/-- Complete reconstruction-program encoding round-trips from the ambient
design alone.
@isnad1 id=eq.0h5v.s5.357c05b17565 from=translated src=- shape=f2b83de1 vocab=a3145f7f
-/
@[simp] theorem decodeReconstructionProgram?_encode
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    decodeReconstructionProgram? design program.encode = some program :=
  decodeReconstructionProgram?_encode_internal program

/-- Payload decoding fails exactly on strings whose length differs from the
exact reconstruction entry count.
@isnad1 id=iff.0h7v.s5.e195f4a5d885 from=translated src=- shape=6b92876a vocab=7c0e6264
-/
@[simp] theorem decodeReconstructionBooleanPayload?_eq_none_iff
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (complement : Bool) (current : Fin outputLength) (bits : List Bool) :
    decodeReconstructionBooleanPayload? design complement current bits = none ↔
      bits.length ≠ design.reconstructionDataBitsAt current :=
  decodeReconstructionBooleanPayload?_eq_none_iff_internal
    design complement current bits

/-- A selected certificate materializes to a predictor meeting the agreement
threshold whose actual flat payload obeys the weak-design length bound.
@isnad1 id=and.2h11v.s7.20b55feba707 from=translated src=- shape=3194d4bb vocab=5ea5a23f
-/
theorem findGoodReconstructionCertificate_encodedProgram_sound
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
        budget + (seedLength - inputLength) + 1 :=
  findGoodReconstructionCertificate_encodedProgram_sound_internal design
    hardFunction test agreementThreshold hbudget batch certificate hfind

/-- The same checked certificate bound for the complete program encoding,
including polarity and hybrid-coordinate metadata.
@isnad1 id=and.2h11v.s7.2a7349465568 from=translated src=- shape=b616bb91 vocab=cd10194e
-/
theorem findGoodReconstructionCertificate_fullyEncodedProgram_sound
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
          (budget + (seedLength - inputLength) + 1) :=
  findGoodReconstructionCertificate_fullyEncodedProgram_sound_internal design
    hardFunction test agreementThreshold hbudget batch certificate hfind

/-- End-to-end encoded reconstruction: canonical checked sampling succeeds
with probability at least one half and every selected stored predictor has
agreement `1/2 + δ/(2m)` and the claimed actual payload length.
@isnad1 id=and.6h12v.s8.4577b9005a9b from=translated src=- shape=b020fbbd vocab=2e887945
-/
theorem half_le_encodedReconstructionProgram_of_randomTest
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
            budget + (seedLength - inputLength) + 1 :=
  half_le_encodedReconstructionProgram_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- End-to-end reconstruction with the polarity and hybrid coordinate included
in every selected program's actual encoding.
@isnad1 id=and.6h12v.s8.a3cbba1b316a from=translated src=- shape=1e078cb7 vocab=28816432
-/
theorem half_le_fullyEncodedReconstructionProgram_of_randomTest
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
              (budget + (seedLength - inputLength) + 1) :=
  half_le_fullyEncodedReconstructionProgram_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- The encoded reconstruction theorem with low generator complexity
discharged by direct short-seed descriptions.
@isnad1 id=and.7h12v.s8.d368a81fa4cc from=translated src=- shape=184c85e8 vocab=856c8656
-/
theorem half_le_encodedReconstructionProgram_of_seedDescriptions
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
            budget + (seedLength - inputLength) + 1 :=
  half_le_encodedReconstructionProgram_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

/-- The fully encoded reconstruction theorem with generator complexity
discharged by direct short-seed descriptions.
@isnad1 id=and.7h12v.s8.fdd7c76a323c from=translated src=- shape=f019b27b vocab=365de149
-/
theorem half_le_fullyEncodedReconstructionProgram_of_seedDescriptions
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
              (budget + (seedLength - inputLength) + 1) :=
  half_le_fullyEncodedReconstructionProgram_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
