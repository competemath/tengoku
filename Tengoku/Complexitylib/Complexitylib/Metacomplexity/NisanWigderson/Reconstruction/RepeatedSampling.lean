/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Internal

/-!
# Repeated sampling of NW reconstruction advice

The probability of finding at least one good reconstruction advice choice in
`k` independent trials is exactly `1 - (1 - p)^k`, where `p` is the one-draw
success probability. In particular, `k * p ≥ 1` gives success probability at
least one half. Combined with the NW averaging bound `p ≥ δ / (2m)`, this is a
finite, explicit form of Hirahara's `O(m / δ)` randomized advice search.
-/

public section

namespace Complexity

namespace NWDesign

/-- The canonical trial count is at least the exact ratio `2m / δ`.
@isnad1 id=le.0h2v.s5.c9dd522451d2 from=translated src=- shape=ba6a1666 vocab=078b385f
-/
theorem ratio_le_reconstructionAdviceTrialCount
    (outputLength : ℕ) (density : ℚ) :
    2 * (outputLength : ℚ) / density ≤
      (reconstructionAdviceTrialCount outputLength density : ℚ) :=
  ratio_le_reconstructionAdviceTrialCount_internal outputLength density

/-- For positive density, the canonical trial count is strictly below
`2m / δ + 1`, making its `O(m / δ)` cost explicit.
@isnad1 id=lt.1h2v.s5.2ed417611cda from=translated src=- shape=dca91398 vocab=05985b4c
-/
theorem reconstructionAdviceTrialCount_lt_ratio_add_one
    (outputLength : ℕ) (density : ℚ) (hdensity : 0 < density) :
    (reconstructionAdviceTrialCount outputLength density : ℚ) <
      2 * (outputLength : ℚ) / density + 1 :=
  reconstructionAdviceTrialCount_lt_ratio_add_one_internal
    outputLength density hdensity

/-- The canonical ceiling trial count meets the repetition threshold exactly
needed for half-success advice search.
@isnad1 id=le.2h2v.s6.c7254821e233 from=translated src=- shape=414c7289 vocab=d2c2908a
-/
theorem one_le_reconstructionAdviceTrialCount_mul_halfAdvantage
    (outputLength : ℕ) (density : ℚ)
    (houtputLength : 0 < outputLength) (hdensity : 0 < density) :
    1 ≤ (reconstructionAdviceTrialCount outputLength density : ℚ) *
      ((density / (outputLength : ℚ)) / 2) :=
  one_le_reconstructionAdviceTrialCount_mul_halfAdvantage_internal
    outputLength density houtputLength hdensity

/-- Exact independent-repetition law for sampling good reconstruction advice.
@isnad1 id=eq.0h9v.s6.cbc3a63de129 from=translated src=- shape=51a19dde vocab=ba823198
-/
theorem repeatedGoodReconstructionAdviceProbability_eq_one_sub_pow
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ)
    (trials : ℕ) :
    design.repeatedGoodReconstructionAdviceProbability hardFunction test
        current agreementThreshold trials =
      1 - (1 - design.goodReconstructionAdviceProbability hardFunction test
        current agreementThreshold) ^ trials :=
  repeatedGoodReconstructionAdviceProbability_eq_one_sub_pow_internal
    design hardFunction test current agreementThreshold trials

/-- Any certified one-draw success lower bound lifts to the exact independent
repetition lower bound.
@isnad1 id=le.1h10v.s6.69eeec36612f from=translated src=- shape=74907022 vocab=6e36791f
-/
theorem one_sub_pow_le_repeatedGoodReconstructionAdviceProbability
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
        current agreementThreshold trials :=
  one_sub_pow_le_repeatedGoodReconstructionAdviceProbability_internal
    design hardFunction test current agreementThreshold trials
      singleDrawLower hlower

/-- If `trials` times a one-draw success lower bound is at least one, repeated
advice sampling finds a good predictor with probability at least one half.
@isnad1 id=le.2h10v.s6.a1b191a74ef6 from=translated src=- shape=8b1a9181 vocab=a2399104
-/
theorem half_le_repeatedGoodReconstructionAdviceProbability
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
        current agreementThreshold trials :=
  half_le_repeatedGoodReconstructionAdviceProbability_internal
    design hardFunction test current agreementThreshold trials
      singleDrawLower hlower htrials

/-- End-to-end repeated advice search from a dense random test, with the exact
geometric success lower bound and the fixed predictor payload bound.
@isnad1 id=ex.6h13v.s8.c750ae4bee7f from=translated src=- shape=391add5e vocab=c1fc546e
-/
theorem exists_repeatedGoodAdviceProbability_ge_of_randomTest
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
          budget + (seedLength - inputLength) + 1 :=
  exists_repeatedGoodAdviceProbability_ge_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- Hirahara's `O(m / δ)` advice-search step in explicit finite form: when
`trials * (δ / (2m)) ≥ 1`, repeated sampling finds a predictor with agreement
`1/2 + δ / (2m)` with probability at least one half.
@isnad1 id=ex.7h13v.s8.670de7085fa2 from=translated src=- shape=1b4700ec vocab=29670c43
-/
theorem exists_half_le_repeatedGoodAdviceProbability_of_randomTest
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
          budget + (seedLength - inputLength) + 1 :=
  exists_half_le_repeatedGoodAdviceProbability_of_randomTest_internal
    houtputLength hdensity htrials hlow hrandom hdense hbudget

/-- The canonical `ceil(2m / δ)` advice count finds a reconstruction predictor
of agreement `1/2 + δ/(2m)` with probability at least one half.
@isnad1 id=ex.6h12v.s7.0ba82f6ff29f from=translated src=- shape=28e67f9c vocab=5b4429df
-/
theorem exists_half_le_canonicalRepeatedGoodAdvice_of_randomTest
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
          budget + (seedLength - inputLength) + 1 :=
  exists_half_le_canonicalRepeatedGoodAdvice_of_randomTest_internal
    houtputLength hdensity hlow hrandom hdense hbudget

/-- Exact repeated advice-search bound when generator complexity is discharged
by direct short-seed descriptions.
@isnad1 id=ex.7h13v.s8.a024717d1dea from=translated src=- shape=aec7549c vocab=a701cb20
-/
theorem exists_repeatedGoodAdviceProbability_ge_of_seedDescriptions
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
          budget + (seedLength - inputLength) + 1 :=
  exists_repeatedGoodAdviceProbability_ge_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

/-- Half-success repeated advice search with low complexity discharged by
direct short-seed descriptions.
@isnad1 id=ex.8h13v.s8.81dbf65150bb from=translated src=- shape=8647bddc vocab=6aa0114e
-/
theorem exists_half_le_repeatedGoodAdviceProbability_of_seedDescriptions
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
          budget + (seedLength - inputLength) + 1 :=
  exists_half_le_repeatedGoodAdviceProbability_of_seedDescriptions_internal
    houtputLength hdensity htrials hseedLength hproduces hrandom hdense hbudget

/-- Canonical-count half-success advice search with low complexity discharged
by direct short-seed descriptions.
@isnad1 id=ex.7h12v.s7.d273516e8ef5 from=translated src=- shape=e20bd5e8 vocab=d2852e4b
-/
theorem exists_half_le_canonicalRepeatedGoodAdvice_of_seedDescriptions
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
          budget + (seedLength - inputLength) + 1 :=
  exists_half_le_canonicalRepeatedGoodAdvice_of_seedDescriptions_internal
    houtputLength hdensity hseedLength hproduces hrandom hdense hbudget

end NWDesign

end Complexity
