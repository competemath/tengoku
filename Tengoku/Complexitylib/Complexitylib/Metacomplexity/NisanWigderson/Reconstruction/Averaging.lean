/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Internal

/-!
# Averaging NW reconstruction to fixed advice

Uniform NW seeds split bijectively into the challenge block and outside seed
coordinates, while a normalized hybrid tail splits into irrelevant earlier bits
and the later bits used by reconstruction. Consequently the global next-bit
success probability is exactly the joint fixed-advice agreement probability,
and averaging fixes one advice choice with no loss in agreement. A finite
reverse-averaging bound additionally quantifies the probability that a uniform
advice draw retains half of the advantage.
-/

public section

namespace Complexity

namespace NWDesign

/-- The canonical next-bit success probability is exactly average agreement of
the reconstructed fixed-advice predictors with the hard function.
@isnad1 id=eq.0h7v.s7.6aa241f5b44a from=translated src=- shape=890c8cf1 vocab=aa96241f
-/
theorem predictionSuccessProbability_eq_averageReconstructionAgreement
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) :
    NextBitPrediction.successProbability
        ((design.generator hardFunction).targetBit current)
        ((design.generator hardFunction).testAtCandidate test current) =
      design.averageReconstructionAgreement hardFunction test current :=
  predictionSuccessProbability_eq_averageReconstructionAgreement_internal
    design hardFunction test current

/-- Some fixed outside seed, later tail, and candidate preserve at least the
global next-bit success probability over uniform challenges.
@isnad1 id=ex.0h7v.s7.86ce9b427995 from=translated src=- shape=c03d2f13 vocab=70ca183c
-/
theorem exists_reconstructionAdvice_agreement_ge
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) :
    ∃ advice : design.ReconstructionAdvice current,
      NextBitPrediction.successProbability
          ((design.generator hardFunction).targetBit current)
          ((design.generator hardFunction).testAtCandidate test current) ≤
        design.reconstructionAgreementProbability hardFunction test current
          advice :=
  exists_reconstructionAdvice_agreement_ge_internal
    design hardFunction test current

/-- Joint reconstruction agreement is the uniform mean of the fixed-advice
agreement probabilities.
@isnad1 id=eq.0h7v.s8.3afb1b492ea9 from=translated src=- shape=c49ce832 vocab=a0ab35ad
-/
theorem averageReconstructionAgreement_eq_uniformMean
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) :
    design.averageReconstructionAgreement hardFunction test current =
      uniformMean (fun advice : design.ReconstructionAdvice current =>
        design.reconstructionAgreementProbability hardFunction test current
          advice) :=
  averageReconstructionAgreement_eq_uniformMean_internal
    design hardFunction test current

/-- Exact reverse-averaging bound for sampling a fixed advice choice above a
given agreement threshold.
@isnad1 id=le.1h8v.s6.e69c6a14099c from=translated src=- shape=2b170a3a vocab=18615653
-/
theorem average_sub_div_le_goodReconstructionAdviceProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (hthreshold : agreementThreshold < 1) :
    (design.averageReconstructionAgreement hardFunction test current -
        agreementThreshold) / (1 - agreementThreshold) ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold :=
  average_sub_div_le_goodReconstructionAdviceProbability_internal
    design hardFunction test current agreementThreshold hthreshold

/-- If mean agreement is `1/2 + ε`, at least an `ε/2` fraction of advice
choices have agreement `1/2 + ε/2`.
@isnad1 id=le.2h8v.s7.41d4085f3226 from=translated src=- shape=dea9e175 vocab=d70e60ea
-/
theorem half_advantage_le_goodReconstructionAdviceProbability
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (advantage : ℚ)
    (hadvantage : 0 ≤ advantage)
    (haverage : 1 / 2 + advantage ≤
      design.averageReconstructionAgreement hardFunction test current) :
    advantage / 2 ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        (1 / 2 + advantage / 2) :=
  half_advantage_le_goodReconstructionAdviceProbability_internal
    design hardFunction test current advantage hadvantage haverage

/-- End-to-end finite NW reconstruction: a dense random test and weak-design
budget yield one fixed predictor with the hybrid agreement advantage and an
exact non-codec payload bound.
@isnad1 id=ex.5h12v.s7.2ade9f388a3f from=translated src=- shape=d750e4aa vocab=5639b9f5
-/
theorem exists_fixed_reconstruction_of_randomTest
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength)
        (advice : design.ReconstructionAdvice current),
      1 / 2 + density / (outputLength : ℚ) ≤
          design.reconstructionAgreementProbability hardFunction
            (BitGenerator.orientTest test complement) current advice ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 :=
  exists_fixed_reconstruction_of_randomTest_internal
    houtputLength hlow hrandom hdense hbudget

/-- The same fixed-predictor theorem with generator low complexity discharged
by direct descriptions shorter than the randomness threshold.
@isnad1 id=ex.6h12v.s7.23f5cc843ed3 from=translated src=- shape=0d12a99e vocab=871ca937
-/
theorem exists_fixed_reconstruction_of_seedDescriptions
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength)
        (advice : design.ReconstructionAdvice current),
      1 / 2 + density / (outputLength : ℚ) ≤
          design.reconstructionAgreementProbability hardFunction
            (BitGenerator.orientTest test complement) current advice ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 :=
  exists_fixed_reconstruction_of_seedDescriptions_internal
    houtputLength hseedLength hproduces hrandom hdense hbudget

/-- Hirahara's randomized-certificate sampling bound: for the selected hybrid
coordinate, a uniform advice draw achieves half the agreement advantage with
probability at least half that advantage.
@isnad1 id=ex.6h12v.s7.18cabd285eb6 from=translated src=- shape=a2fd876e vocab=46b0a2c8
-/
theorem exists_goodAdviceProbability_ge_of_randomTest
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      (density / (outputLength : ℚ)) / 2 ≤
          design.goodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 :=
  exists_goodAdviceProbability_ge_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- The randomized advice-sampling bound with low complexity discharged by
direct short-seed descriptions.
@isnad1 id=ex.7h12v.s7.56edd6096990 from=translated src=- shape=c14d7467 vocab=accddd47
-/
theorem exists_goodAdviceProbability_ge_of_seedDescriptions
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density) (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      (density / (outputLength : ℚ)) / 2 ≤
          design.goodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 :=
  exists_goodAdviceProbability_ge_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
