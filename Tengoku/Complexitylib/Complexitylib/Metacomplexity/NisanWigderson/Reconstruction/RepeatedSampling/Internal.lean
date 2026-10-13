/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Defs
import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Internal

/-!
# Repeated sampling of NW reconstruction advice -- proof internals

The exact finite repetition law and its quantitative reciprocal bound are
specialized to the advice event produced by NW reconstruction averaging.
-/

public section

namespace Complexity

namespace NWDesign

/--
@isnad1 id=le.0h2v.s5.c9dd522451d2 from=translated src=- shape=ba6a1666 vocab=078b385f
-/
theorem ratio_le_reconstructionAdviceTrialCount_internal
    (outputLength : ℕ) (density : ℚ) :
    2 * (outputLength : ℚ) / density ≤
      (reconstructionAdviceTrialCount outputLength density : ℚ) := by
  exact Nat.le_ceil _

/--
@isnad1 id=lt.1h2v.s5.2ed417611cda from=translated src=- shape=dca91398 vocab=05985b4c
-/
theorem reconstructionAdviceTrialCount_lt_ratio_add_one_internal
    (outputLength : ℕ) (density : ℚ) (hdensity : 0 < density) :
    (reconstructionAdviceTrialCount outputLength density : ℚ) <
      2 * (outputLength : ℚ) / density + 1 := by
  exact Nat.ceil_lt_add_one (by positivity)

/--
@isnad1 id=le.2h2v.s6.c7254821e233 from=translated src=- shape=414c7289 vocab=d2c2908a
-/
theorem one_le_reconstructionAdviceTrialCount_mul_halfAdvantage_internal
    (outputLength : ℕ) (density : ℚ)
    (houtputLength : 0 < outputLength) (hdensity : 0 < density) :
    1 ≤ (reconstructionAdviceTrialCount outputLength density : ℚ) *
      ((density / (outputLength : ℚ)) / 2) := by
  have hceil :=
    ratio_le_reconstructionAdviceTrialCount_internal outputLength density
  have hfactor : 0 ≤ (density / (outputLength : ℚ)) / 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hceil hfactor
  calc
    1 = (2 * (outputLength : ℚ) / density) *
        ((density / (outputLength : ℚ)) / 2) := by
      field_simp
    _ ≤ _ := hmul

/--
@isnad1 id=eq.0h9v.s6.cbc3a63de129 from=translated src=- shape=51a19dde vocab=ba823198
-/
theorem repeatedGoodReconstructionAdviceProbability_eq_one_sub_pow_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) :
    design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials =
      1 - (1 - design.goodReconstructionAdviceProbability hardFunction test
        current agreementThreshold) ^ trials := by
  simpa [repeatedGoodReconstructionAdviceProbability,
    goodReconstructionAdviceEvent, goodReconstructionAdviceProbability] using
    uniformAtLeastOneProbability_eq_one_sub_pow_internal
      (design.goodReconstructionAdviceEvent hardFunction test current
        agreementThreshold)
      trials

/--
@isnad1 id=le.1h10v.s6.69eeec36612f from=translated src=- shape=74907022 vocab=6e36791f
-/
theorem one_sub_pow_le_repeatedGoodReconstructionAdviceProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold) :
    1 - (1 - singleDrawLower) ^ trials ≤
      design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials := by
  exact one_sub_pow_le_uniformAtLeastOneProbability_internal
    (design.goodReconstructionAdviceEvent hardFunction test current
      agreementThreshold)
    trials singleDrawLower (by
      simpa [goodReconstructionAdviceEvent,
        goodReconstructionAdviceProbability] using hlower)

/--
@isnad1 id=le.2h10v.s6.a1b191a74ef6 from=translated src=- shape=8b1a9181 vocab=a2399104
-/
theorem half_le_repeatedGoodReconstructionAdviceProbability_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold)
    (htrials : 1 ≤ (trials : ℚ) * singleDrawLower) :
    1 / 2 ≤
      design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials := by
  exact half_le_uniformAtLeastOneProbability_of_singleDrawLower_internal
    (design.goodReconstructionAdviceEvent hardFunction test current
      agreementThreshold)
    trials singleDrawLower (by
      simpa [goodReconstructionAdviceEvent,
        goodReconstructionAdviceProbability] using hlower)
    htrials

/--
@isnad1 id=ex.6h13v.s8.c750ae4bee7f from=translated src=- shape=391add5e vocab=c1fc546e
-/
theorem exists_repeatedGoodAdviceProbability_ge_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
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
      1 - (1 - (density / (outputLength : ℚ)) / 2) ^ trials ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, current, hsingle, hdata⟩ :=
    exists_goodAdviceProbability_ge_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  exact ⟨complement, current,
    one_sub_pow_le_repeatedGoodReconstructionAdviceProbability_internal
      design hardFunction (BitGenerator.orientTest test complement) current
      (1 / 2 + (density / (outputLength : ℚ)) / 2) trials
      ((density / (outputLength : ℚ)) / 2) hsingle,
    hdata⟩

/--
@isnad1 id=ex.7h13v.s8.670de7085fa2 from=translated src=- shape=1b4700ec vocab=29670c43
-/
theorem exists_half_le_repeatedGoodAdviceProbability_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density)
    (htrials : 1 ≤ (trials : ℚ) *
      ((density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      1 / 2 ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, current, hsingle, hdata⟩ :=
    exists_goodAdviceProbability_ge_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  exact ⟨complement, current,
    half_le_repeatedGoodReconstructionAdviceProbability_internal
      design hardFunction (BitGenerator.orientTest test complement) current
      (1 / 2 + (density / (outputLength : ℚ)) / 2) trials
      ((density / (outputLength : ℚ)) / 2) hsingle htrials,
    hdata⟩

/--
@isnad1 id=ex.6h12v.s7.0ba82f6ff29f from=translated src=- shape=28e67f9c vocab=5b4429df
-/
theorem exists_half_le_canonicalRepeatedGoodAdvice_of_randomTest_internal
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
    ∃ (complement : Bool) (current : Fin outputLength),
      1 / 2 ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength density) ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  exact exists_half_le_repeatedGoodAdviceProbability_of_randomTest_internal
    houtputLength hdensity.le
    (one_le_reconstructionAdviceTrialCount_mul_halfAdvantage_internal
      outputLength density houtputLength hdensity)
    hlow hrandom hdense hbudget

/--
@isnad1 id=ex.7h13v.s8.a024717d1dea from=translated src=- shape=aec7549c vocab=a701cb20
-/
theorem exists_repeatedGoodAdviceProbability_ge_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
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
      1 - (1 - (density / (outputLength : ℚ)) / 2) ^ trials ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  apply exists_repeatedGoodAdviceProbability_ge_of_randomTest_internal
    houtputLength hdensity (hrandom := hrandom) (hdense := hdense)
    (hbudget := hbudget)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

/--
@isnad1 id=ex.8h13v.s8.81dbf65150bb from=translated src=- shape=8647bddc vocab=6aa0114e
-/
theorem exists_half_le_repeatedGoodAdviceProbability_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget trials : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density)
    (htrials : 1 ≤ (trials : ℚ) *
      ((density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ (complement : Bool) (current : Fin outputLength),
      1 / 2 ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2) trials ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  apply exists_half_le_repeatedGoodAdviceProbability_of_randomTest_internal
    houtputLength hdensity htrials (hrandom := hrandom) (hdense := hdense)
    (hbudget := hbudget)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

/--
@isnad1 id=ex.7h12v.s7.d273516e8ef5 from=translated src=- shape=e20bd5e8 vocab=d2852e4b
-/
theorem exists_half_le_canonicalRepeatedGoodAdvice_of_seedDescriptions_internal
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
    ∃ (complement : Bool) (current : Fin outputLength),
      1 / 2 ≤
          design.repeatedGoodReconstructionAdviceProbability hardFunction
            (BitGenerator.orientTest test complement) current
            (1 / 2 + (density / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength density) ∧
        design.reconstructionDataBitsAt current ≤
          budget + (seedLength - inputLength) + 1 := by
  exact exists_half_le_repeatedGoodAdviceProbability_of_seedDescriptions_internal
    houtputLength hdensity.le
    (one_le_reconstructionAdviceTrialCount_mul_halfAdvantage_internal
      outputLength density houtputLength hdensity)
    hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
