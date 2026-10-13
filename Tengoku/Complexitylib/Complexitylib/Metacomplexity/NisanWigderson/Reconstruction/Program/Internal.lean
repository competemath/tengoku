/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Internal

/-!
# Explicit NW reconstruction programs -- proof internals
-/

public section

namespace Complexity

namespace NWDesign

/--
@isnad1 id=eq.0h9v.s8.935ded1f5b5a from=translated src=- shape=c67b16e2 vocab=18b889a6
-/
theorem materializeReconstructionProgram_query_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current)
    (challenge : Fin inputLength → Bool) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).query challenge =
      design.reconstructionQuery hardFunction current advice.1 advice.2.1
        challenge advice.2.2 := by
  funext output
  by_cases houtput : output.val < current.val
  · have hmem : output ∈ Finset.Iio current := by
      simpa using houtput
    simp [ReconstructionProgram.query, materializeReconstructionProgram,
      reconstructionQuery, hmem, houtput]
  · have hmem : output ∉ Finset.Iio current := by
      simpa using houtput
    simp [ReconstructionProgram.query, materializeReconstructionProgram,
      reconstructionQuery, hmem, houtput]

/--
@isnad1 id=eq.0h9v.s8.d4ae00178321 from=translated src=- shape=aa61ed50 vocab=af57449e
-/
theorem materializeReconstructionProgram_predictor_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).predictor test =
      design.reconstructionPredictor hardFunction
        (BitGenerator.orientTest test complement) current advice.1
        advice.2.1 advice.2.2 := by
  funext challenge
  change NextBitPrediction.predictFromTest
      (decide ((design.materializeReconstructionProgram hardFunction
        complement current advice).query challenge ∈
          BitGenerator.orientTest test complement)) advice.2.2 =
    NextBitPrediction.predictFromTest
      (decide (design.reconstructionQuery hardFunction current advice.1
        advice.2.1 challenge advice.2.2 ∈
          BitGenerator.orientTest test complement)) advice.2.2
  rw [materializeReconstructionProgram_query_internal]

/--
@isnad1 id=eq.0h9v.s6.f3e5ec60099d from=translated src=- shape=719d2f60 vocab=e85e18db
-/
theorem materializeReconstructionProgram_agreementProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (complement : Bool) (current : Fin outputLength)
    (advice : design.ReconstructionAdvice current) :
    (design.materializeReconstructionProgram hardFunction complement current
        advice).agreementProbability hardFunction test =
      design.reconstructionAgreementProbability hardFunction
        (BitGenerator.orientTest test complement) current advice := by
  unfold ReconstructionProgram.agreementProbability
  unfold reconstructionAgreementProbability
  rw [materializeReconstructionProgram_predictor_internal]

/--
@isnad1 id=eq.0h7v.s5.344c33b45915 from=translated src=- shape=036ff367 vocab=3d2ac09d
-/
theorem reconstructionCertificate_toProgram_agreementProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (certificate : ReconstructionCertificate outputLength seedLength) :
    (certificate.toProgram design hardFunction).agreementProbability
        hardFunction test =
      design.reconstructionTrialAgreementProbability hardFunction
        (BitGenerator.orientTest test certificate.complement)
        certificate.trial := by
  unfold ReconstructionCertificate.toProgram
  unfold reconstructionTrialAgreementProbability
  exact materializeReconstructionProgram_agreementProbability_internal
    design hardFunction test certificate.complement certificate.trial.1
      (design.reconstructionAdviceOfTrial certificate.trial)

/--
@isnad1 id=eq.0h5v.s5.e8fd7d4fd37e from=translated src=- shape=e8bf21bd vocab=eb3acd1e
-/
theorem ReconstructionProgram.booleanPayloadSize_eq_internal
    {outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram) :
    program.booleanPayloadSize =
      design.reconstructionDataBitsAt program.current := by
  simp [ReconstructionProgram.booleanPayloadSize,
    reconstructionDataBitsAt, predecessorTableEntriesAt]
  have hsum := Finset.sum_attach (Finset.Iio program.current)
    (fun previous =>
      2 ^ (design.challengeOverlap program.current previous).card)
  rw [hsum]
  omega

/--
@isnad1 id=and.2h11v.s7.f101cbf83dd2 from=translated src=- shape=9bca3781 vocab=a27f478e
-/
theorem findGoodReconstructionCertificate_program_sound_internal
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
      (certificate.toProgram design hardFunction).booleanPayloadSize ≤
        budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hgood, _index⟩ :=
    findGoodReconstructionCertificate_sound_internal design hardFunction test
      agreementThreshold batch certificate hfind
  constructor
  · rw [reconstructionCertificate_toProgram_agreementProbability_internal]
    exact hgood
  · rw [ReconstructionProgram.booleanPayloadSize_eq_internal]
    exact reconstructionDataBitsAt_le_of_hasOverlapBudget_internal
      hbudget certificate.trial.1

/--
@isnad1 id=and.6h12v.s8.faf09882f851 from=translated src=- shape=f2907ba7 vocab=99e95228
-/
theorem half_le_materializedReconstructionProgram_of_randomTest_internal
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
          (certificate.toProgram design hardFunction).booleanPayloadSize ≤
            budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_checkedReconstructionBatch_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_program_sound_internal design
    hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

/--
@isnad1 id=and.7h12v.s8.e0d4be695aea from=translated src=- shape=48991dc5 vocab=2b0fc04c
-/
theorem half_le_materializedReconstructionProgram_of_seedDescriptions_internal
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
          (certificate.toProgram design hardFunction).booleanPayloadSize ≤
            budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_checkedReconstructionBatch_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_program_sound_internal design
    hardFunction test
      (1 / 2 + (density / (outputLength : ℚ)) / 2) hbudget batch
      certificate hfind

end NWDesign

end Complexity
