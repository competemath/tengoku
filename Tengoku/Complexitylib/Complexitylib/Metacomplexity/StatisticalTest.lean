/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Oracle
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Hybrid
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Prediction

/-!
# Finite statistical tests for binary generators

This module formalizes the first finite step in Hirahara's 2018
Nisan--Wigderson reconstruction argument. A dense set of strings that are
random for a time-bounded Kolmogorov threshold is a statistical test against
any generator whose outputs all lie strictly below that threshold.

In particular, if the machine directly produces each generated output from
its seed within the clock and the seed length is strictly below the randomness
threshold, the test has zero acceptance probability on generated outputs. Its
distinguishing advantage therefore equals its uniform density exactly.

Every finite test also has a canonical total Boolean oracle: fixed-length
queries receive their membership bit and malformed lengths are rejected.
-/

public section

namespace Complexity

namespace BitGenerator

/-- Being a time-bounded random-string test is exactly finite-set inclusion in
the canonical set of strings at or above the chosen complexity threshold.
@isnad1 id=iff.0h6v.s5.e8a8049e1660 from=translated src=- shape=3712648b vocab=8767f736
-/
theorem isTimeBoundedRandomTest_iff_subset
    {outputLength tapes time threshold : ℕ}
    {test : Finset (Fin outputLength → Bool)} {machine : TM tapes} :
    IsTimeBoundedRandomTest test machine time threshold ↔
      test ⊆ machine.timeBoundedRandomStrings
        outputLength time threshold :=
  isTimeBoundedRandomTest_iff_subset_internal

/-- The full canonical set of threshold-random strings is a random-string
test.
@isnad1 id=istimebo.0h5v.s4.38cdbe4bca05 from=translated src=- shape=b879f85b vocab=fe7fe89e
-/
theorem timeBoundedRandomStrings_isRandomTest
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsTimeBoundedRandomTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      machine time threshold :=
  timeBoundedRandomStrings_isRandomTest_internal
    machine outputLength time threshold

/-- The full random-string test has the quantitative uniform density supplied
by strict finite incompressibility.
@isnad1 id=isdenset.0h5v.s6.2776a0c9e14a from=translated src=- shape=7a0f3e49 vocab=a3d250ef
-/
theorem timeBoundedRandomStrings_isDenseTest
    {tapes : ℕ} (machine : TM tapes) (outputLength time threshold : ℕ) :
    IsDenseTest
      (machine.timeBoundedRandomStrings outputLength time threshold)
      (1 - ((2 ^ threshold - 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ outputLength) :=
  timeBoundedRandomStrings_isDenseTest_internal
    machine outputLength time threshold

/-- If the machine produces every generated output directly from its seed and
the seed is shorter than the threshold, every output has complexity below the
threshold. This is the finite description step used for efficiently computable
short-seed generators.
@isnad1 id=haslowti.2h7v.s5.d407b167c0e8 from=translated src=- shape=d2c4d482 vocab=55916521
-/
theorem hasLowTimeBoundedComplexity_of_seedDescriptions
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    generator.HasLowTimeBoundedComplexity machine time threshold :=
  hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

/-- A low-complexity generator output cannot belong to a test containing only
strings at or above the same complexity threshold.
@isnad1 id=not.2h9v.s6.4343b80e6856 from=translated src=- shape=4e9162b1 vocab=dccc6c7f
-/
theorem output_not_mem_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (seed : Fin seedLength → Bool) :
    generator seed ∉ test :=
  output_not_mem_of_randomTest_internal hlow hrandom seed

/-- The test accepts no seed of a low-complexity generator.
@isnad1 id=eq.2h8v.s5.9f40c0629409 from=translated src=- shape=1a5f82ff vocab=40f8cb0c
-/
theorem acceptedSeeds_eq_empty_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.acceptedSeeds test = ∅ :=
  acceptedSeeds_eq_empty_of_randomTest_internal hlow hrandom

/-- A random-string test has exactly zero acceptance probability under any
generator whose outputs are all below its complexity threshold.
@isnad1 id=eq.2h8v.s5.76bc5bf709d6 from=translated src=- shape=184353a0 vocab=18d7e68a
-/
theorem generatedAcceptanceProbability_eq_zero_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.generatedAcceptanceProbability test = 0 :=
  generatedAcceptanceProbability_eq_zero_of_randomTest_internal hlow hrandom

/-- For a random-string test against a low-complexity generator, the absolute
distinguishing advantage is exactly the test's uniform acceptance probability.
@isnad1 id=eq.2h8v.s5.592ef80a4b0c from=translated src=- shape=638fb1e1 vocab=cefdf5ba
-/
theorem distinguishingAdvantage_eq_uniform_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold) :
    generator.distinguishingAdvantage test =
      uniformAcceptanceProbability test :=
  distinguishingAdvantage_eq_uniform_of_randomTest_internal hlow hrandom

/-- A `density`-dense random-string test distinguishes every low-complexity
generator with advantage at least `density`.
@isnad1 id=le.3h9v.s5.abc62a1b84e2 from=translated src=- shape=fa0aeb56 vocab=5b6baea4
-/
theorem density_le_distinguishingAdvantage_of_randomTest
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test :=
  density_le_distinguishingAdvantage_of_randomTest_internal
    hlow hrandom hdense

/-- Hirahara's finite statistical-test step: a dense random-string test has
advantage at least its density against a generator whose short seeds directly
describe its outputs within the chosen clock.
@isnad1 id=le.4h9v.s6.0c22fdaaa19f from=translated src=- shape=a5b01ad7 vocab=287cef23
-/
theorem density_le_distinguishingAdvantage_of_seedDescriptions
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    {test : Finset (Fin outputLength → Bool)} {density : ℚ}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time)
    (hrandom : IsTimeBoundedRandomTest test machine time threshold)
    (hdense : IsDenseTest test density) :
    density ≤ generator.distinguishingAdvantage test :=
  density_le_distinguishingAdvantage_of_seedDescriptions_internal
    hseedLength hproduces hrandom hdense

/-- The canonical random-string test distinguishes every generator whose
outputs are below the threshold by the full strict-incompressibility lower
bound. No computability property of the test is asserted here.
@isnad1 id=le.1h7v.s6.5b390b37d3af from=translated src=- shape=0169674a vocab=88188d88
-/
theorem incompressibilityBound_le_distinguishingAdvantage
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hlow : generator.HasLowTimeBoundedComplexity machine time threshold) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) :=
  incompressibilityBound_le_distinguishingAdvantage_internal hlow

/-- A directly seed-described generator is distinguished by the canonical
random-string test with the explicit strict-incompressibility advantage.
@isnad1 id=le.2h7v.s6.4adc6105c3e7 from=translated src=- shape=44140cf1 vocab=9c9bd802
-/
theorem incompressibilityBound_le_distinguishingAdvantage_of_seedDescriptions
    {seedLength outputLength tapes time threshold : ℕ}
    {generator : BitGenerator seedLength outputLength} {machine : TM tapes}
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (generator seed)) time) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      generator.distinguishingAdvantage
        (machine.timeBoundedRandomStrings outputLength time threshold) :=
  incompressibilityBound_le_distinguishingAdvantage_of_seedDescriptions_internal
    hseedLength hproduces

end BitGenerator

end Complexity
