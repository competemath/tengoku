/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Incompressibility.Internal

/-!
# Finite statistical tests for binary generators -- proof internals

The central fact is disjointness: a test containing only strings of complexity
at least `threshold` cannot accept an output whose complexity is strictly below
`threshold`. Exact zero generated mass and the density-to-advantage bound then
follow by finite counting.
-/

public section

namespace Complexity

namespace BitGenerator

/--
@isnad1 id=iff.0h6v.s5.e8a8049e1660 from=translated src=- shape=3712648b vocab=8767f736
-/
theorem isTimeBoundedRandomTest_iff_subset_internal
    {outputLength tapes time threshold : ℕ}
    {test : Finset (Fin outputLength → Bool)} {machine : TM tapes} :
    IsTimeBoundedRandomTest test machine time threshold ↔
      test ⊆ machine.timeBoundedRandomStrings
        outputLength time threshold := by
  constructor
  · intro hrandom output hmember
    apply (TM.mem_timeBoundedRandomStrings_iff_internal
      machine outputLength time threshold output).mpr
    exact hrandom output hmember
  · intro hsubset output hmember
    apply (TM.mem_timeBoundedRandomStrings_iff_internal
      machine outputLength time threshold output).mp
    exact hsubset hmember

/--
@isnad1 id=istimebo.0h5v.s4.38cdbe4bca05 from=translated src=- shape=b879f85b vocab=fe7fe89e
-/
theorem timeBoundedRandomStrings_isRandomTest_internal
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsTimeBoundedRandomTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      machine time threshold := by
  apply isTimeBoundedRandomTest_iff_subset_internal.mpr
  exact Finset.Subset.rfl

/--
@isnad1 id=isdenset.0h5v.s6.2776a0c9e14a from=translated src=- shape=7a0f3e49 vocab=a3d250ef
-/
theorem timeBoundedRandomStrings_isDenseTest_internal
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsDenseTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      (1 - ((2 ^ threshold - 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ outputLength) :=
  TM.eventProb_timeBoundedRandomStrings_ge_internal
    machine outputLength time threshold

/--
@isnad1 id=haslowti.2h7v.s5.d407b167c0e8 from=translated src=- shape=d2c4d482 vocab=55916521
-/
theorem hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    generator.HasLowTimeBoundedComplexity machine time threshold := by
  intro seed
  apply (TM.timeBoundedKolmogorovComplexity_lt_coe_iff_internal
    machine (List.ofFn (generator seed)) time threshold).mpr
  exact ⟨List.ofFn seed, by simpa using hseedLength, hproduces seed⟩

/--
@isnad1 id=not.2h9v.s6.4343b80e6856 from=translated src=- shape=4e9162b1 vocab=dccc6c7f
-/
theorem output_not_mem_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (seed : Fin seedLength → Bool) :
    generator seed ∉ test := by
  intro hmember
  exact (not_lt_of_ge (hrandom (generator seed) hmember)) (hlow seed)

/--
@isnad1 id=eq.2h8v.s5.9f40c0629409 from=translated src=- shape=1a5f82ff vocab=40f8cb0c
-/
theorem acceptedSeeds_eq_empty_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.acceptedSeeds test = ∅ := by
  ext seed
  simp [acceptedSeeds,
    output_not_mem_of_randomTest_internal hlow hrandom seed]

/--
@isnad1 id=eq.2h8v.s5.76bc5bf709d6 from=translated src=- shape=184353a0 vocab=18d7e68a
-/
theorem generatedAcceptanceProbability_eq_zero_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.generatedAcceptanceProbability test = 0 := by
  rw [generatedAcceptanceProbability,
    acceptedSeeds_eq_empty_of_randomTest_internal hlow hrandom,
    eventProb_empty]

/--
@isnad1 id=eq.2h8v.s5.592ef80a4b0c from=translated src=- shape=638fb1e1 vocab=cefdf5ba
-/
theorem distinguishingAdvantage_eq_uniform_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.distinguishingAdvantage test =
      uniformAcceptanceProbability test := by
  rw [distinguishingAdvantage,
    generatedAcceptanceProbability_eq_zero_of_randomTest_internal hlow hrandom,
    sub_zero, abs_of_nonneg]
  exact eventProb_nonneg test

/--
@isnad1 id=le.3h9v.s5.abc62a1b84e2 from=translated src=- shape=fa0aeb56 vocab=5b6baea4
-/
theorem density_le_distinguishingAdvantage_of_randomTest_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test := by
  rw [distinguishingAdvantage_eq_uniform_of_randomTest_internal hlow hrandom]
  exact hdense

/--
@isnad1 id=le.4h9v.s6.0c22fdaaa19f from=translated src=- shape=a5b01ad7 vocab=287cef23
-/
theorem density_le_distinguishingAdvantage_of_seedDescriptions_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test := by
  apply density_le_distinguishingAdvantage_of_randomTest_internal
    (hrandom := hrandom) (hdense := hdense)
  exact hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

/--
@isnad1 id=le.1h7v.s6.5b390b37d3af from=translated src=- shape=0169674a vocab=88188d88
-/
theorem incompressibilityBound_le_distinguishingAdvantage_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) := by
  exact density_le_distinguishingAdvantage_of_randomTest_internal
    hlow
    (timeBoundedRandomStrings_isRandomTest_internal
      machine outputLength time threshold)
    (timeBoundedRandomStrings_isDenseTest_internal
      machine outputLength time threshold)

/--
@isnad1 id=le.2h7v.s6.4adc6105c3e7 from=translated src=- shape=44140cf1 vocab=9c9bd802
-/
theorem incompressibilityBound_le_distinguishingAdvantage_of_seedDescriptions_internal
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) := by
  apply incompressibilityBound_le_distinguishingAdvantage_internal
  exact hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

end BitGenerator

end Complexity
