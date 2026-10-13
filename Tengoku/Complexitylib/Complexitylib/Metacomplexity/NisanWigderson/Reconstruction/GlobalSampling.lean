/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.GlobalSampling.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.GlobalSampling.Internal

/-!
# Globally sampling NW reconstruction coordinates and advice

This layer represents Hirahara's random coordinate, outside seed, later tail,
and candidate bit by one fixed-width finite trial. Uniform restriction ensures
that conditioning on any coordinate gives exactly the corresponding uniform
reconstruction-advice distribution.
-/

public section

namespace Complexity

namespace NWDesign

/-- For a fixed coordinate, restricting uniform fixed-width raw advice gives
exactly the canonical uniform reconstruction-advice probability.
@isnad1 id=eq.0h8v.s7.0a9bca2a41f7 from=translated src=- shape=7cdabb5d vocab=a2c735f9
-/
theorem goodRawAdviceProbability_eq
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ) :
    uniformProbability (Finset.univ.filter fun raw :
        RawReconstructionAdvice outputLength seedLength =>
      agreementThreshold ≤
        design.reconstructionAgreementProbability hardFunction test current
          (design.reconstructionAdviceOfRaw current raw)) =
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold :=
  goodRawAdviceProbability_eq_internal
    design hardFunction test current agreementThreshold

/-- A global fixed-width trial chooses the hybrid coordinate uniformly and
then realizes that coordinate's uniform reconstruction-advice distribution.
@isnad1 id=eq.1h7v.s6.59ee73915913 from=translated src=- shape=b65c8f91 vocab=e085c12f
-/
theorem goodReconstructionTrialProbability_eq_average
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) (houtputLength : 0 < outputLength) :
    design.goodReconstructionTrialProbability hardFunction test
        agreementThreshold =
      (∑ current : Fin outputLength,
        design.goodReconstructionAdviceProbability hardFunction test current
          agreementThreshold) / outputLength :=
  goodReconstructionTrialProbability_eq_average_internal
    design hardFunction test agreementThreshold houtputLength

/-- The total oriented distinguishing advantage lower-bounds the sum of the
coordinate-wise average reconstruction agreements above the half baseline.
@isnad1 id=ex.1h7v.s6.f7d439af6090 from=translated src=- shape=ae49589e vocab=e252d51d
-/
theorem exists_orientation_sum_averageReconstructionAgreement_ge
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool)) (advantage : ℚ)
    (hadvantage : advantage ≤
      (design.generator hardFunction).distinguishingAdvantage test) :
    ∃ complement : Bool,
      (outputLength : ℚ) / 2 + advantage ≤
        ∑ current : Fin outputLength,
          design.averageReconstructionAgreement hardFunction
            (BitGenerator.orientTest test complement) current :=
  exists_orientation_sum_averageReconstructionAgreement_ge_internal
    design hardFunction test advantage hadvantage

/-- Hirahara's one-tuple Markov bound: sampling the coordinate together with
fixed-width raw advice produces a predictor with half the average advantage
with probability at least half the average advantage.
@isnad1 id=ex.4h7v.s7.bd8722cef367 from=translated src=- shape=8477c44e vocab=58dd8a3e
-/
theorem exists_orientation_goodReconstructionTrialProbability_ge
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool)) (density : ℚ)
    (houtputLength : 0 < outputLength) (hdensity : 0 ≤ density)
    (hdensityLeOne : density ≤ 1)
    (hadvantage : density ≤
      (design.generator hardFunction).distinguishingAdvantage test) :
    ∃ complement : Bool,
      (density / (outputLength : ℚ)) / 2 ≤
        design.goodReconstructionTrialProbability hardFunction
          (BitGenerator.orientTest test complement)
          (1 / 2 + (density / (outputLength : ℚ)) / 2) :=
  exists_orientation_goodReconstructionTrialProbability_ge_internal
    design hardFunction test density houtputLength hdensity hdensityLeOne
      hadvantage

/-- Exact independent-repetition law for globally sampled reconstruction
coordinates and raw advice.
@isnad1 id=eq.1h8v.s6.25e20b2e7dcf from=translated src=- shape=09087699 vocab=6943599b
-/
theorem repeatedGoodReconstructionTrialProbability_eq_one_sub_pow
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) (trials : ℕ)
    (houtputLength : 0 < outputLength) :
    design.repeatedGoodReconstructionTrialProbability hardFunction test
        agreementThreshold trials =
      1 - (1 - design.goodReconstructionTrialProbability hardFunction test
        agreementThreshold) ^ trials :=
  repeatedGoodReconstructionTrialProbability_eq_one_sub_pow_internal
    design hardFunction test agreementThreshold trials houtputLength

/-- A dense random test yields one test orientation for which a single global
trial succeeds with probability at least `δ/(2m)`; every trial coordinate has
the same weak-design payload bound.
@isnad1 id=ex.6h12v.s7.97a526b7e13a from=translated src=- shape=c2a6ae55 vocab=aac8e147
-/
theorem exists_goodReconstructionTrialProbability_ge_of_randomTest
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
    ∃ complement : Bool,
      (density / (outputLength : ℚ)) / 2 ≤
          design.goodReconstructionTrialProbability hardFunction
            (BitGenerator.orientTest test complement)
            (1 / 2 + (density / (outputLength : ℚ)) / 2) ∧
        ∀ trial : ReconstructionTrial outputLength seedLength,
          design.reconstructionDataBitsAt trial.1 ≤
            budget + (seedLength - inputLength) + 1 :=
  exists_goodReconstructionTrialProbability_ge_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- Fully global `O(m/δ)` advice search: `ceil(2m/δ)` independent fixed-width
trials, each sampling its own coordinate and raw advice, find a predictor of
agreement `1/2 + δ/(2m)` with probability at least one half.
@isnad1 id=ex.6h12v.s7.6cf9580444ec from=translated src=- shape=b62db4f2 vocab=5e5833b4
-/
theorem exists_half_le_canonicalRepeatedGoodTrial_of_randomTest
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
    ∃ complement : Bool,
      1 / 2 ≤
          design.repeatedGoodReconstructionTrialProbability hardFunction
            (BitGenerator.orientTest test complement)
            (1 / 2 + (density / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength density) ∧
        ∀ trial : ReconstructionTrial outputLength seedLength,
          design.reconstructionDataBitsAt trial.1 ≤
            budget + (seedLength - inputLength) + 1 :=
  exists_half_le_canonicalRepeatedGoodTrial_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- The fully global canonical-count search with generator complexity
discharged by direct short-seed descriptions.
@isnad1 id=ex.7h12v.s7.b232c3f121ed from=translated src=- shape=81d20527 vocab=985ae4ee
-/
theorem exists_half_le_canonicalRepeatedGoodTrial_of_seedDescriptions
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
    ∃ complement : Bool,
      1 / 2 ≤
          design.repeatedGoodReconstructionTrialProbability hardFunction
            (BitGenerator.orientTest test complement)
            (1 / 2 + (density / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength density) ∧
        ∀ trial : ReconstructionTrial outputLength seedLength,
          design.reconstructionDataBitsAt trial.1 ≤
            budget + (seedLength - inputLength) + 1 :=
  exists_half_le_canonicalRepeatedGoodTrial_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
