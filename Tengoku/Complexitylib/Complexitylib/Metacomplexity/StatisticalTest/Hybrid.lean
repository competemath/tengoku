/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Internal

/-!
# Hybrid distributions for finite binary generators

This module gives the exact finite hybrid argument used at the start of the
Nisan--Wigderson reconstruction. The zero hybrid is uniform, the final hybrid
is the generator distribution, and the adjacent gaps telescope. Consequently,
any positive absolute distinguishing advantage can be oriented by optionally
complementing the test, after which one adjacent hybrid gap is at least the
advantage divided by the output length.
-/

public section

namespace Complexity

namespace BitGenerator

/--
@isnad1 id=eq.0h2v.s4.6f4eaa07fd37 from=translated src=- shape=e682e438 vocab=5a2b3b89
-/
@[simp] theorem orientTest_false {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test false = test :=
  orientTest_false_internal test

/--
@isnad1 id=eq.0h2v.s6.635877b12067 from=translated src=- shape=687d2d15 vocab=1cee39ff
-/
@[simp] theorem orientTest_true {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test true = testᶜ :=
  orientTest_true_internal test

/-- Accepted seeds for the complementary test are exactly the complement of
the accepted-seed event.
@isnad1 id=eq.0h4v.s7.0d7218f2ce5d from=translated src=- shape=565bc8de vocab=79869fec
-/
theorem acceptedSeeds_compl {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.acceptedSeeds testᶜ = (generator.acceptedSeeds test)ᶜ :=
  acceptedSeeds_compl_internal generator test

/-- Complementing a test complements its uniform acceptance probability.
@isnad1 id=eq.0h2v.s6.f823617b59a9 from=translated src=- shape=e00dfac1 vocab=d0e43a2c
-/
theorem uniformAcceptanceProbability_compl {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    uniformAcceptanceProbability testᶜ =
      1 - uniformAcceptanceProbability test :=
  uniformAcceptanceProbability_compl_internal test

/-- Complementing a test complements its generated acceptance probability.
@isnad1 id=eq.0h4v.s6.9ce11aa0b844 from=translated src=- shape=4afbbe7e vocab=3149b7db
-/
theorem generatedAcceptanceProbability_compl
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.generatedAcceptanceProbability testᶜ =
      1 - generator.generatedAcceptanceProbability test :=
  generatedAcceptanceProbability_compl_internal generator test

/-- One polarity of a test realizes its absolute distinguishing advantage as
an oriented generated-minus-uniform gap.
@isnad1 id=ex.1h5v.s5.641f3c20b631 from=translated src=- shape=a72f049d vocab=80b37369
-/
theorem exists_orientation_of_distinguishingAdvantage
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ complement : Bool,
      advantage ≤
        generator.generatedAcceptanceProbability
            (orientTest test complement) -
          uniformAcceptanceProbability (orientTest test complement) :=
  exists_orientation_of_distinguishingAdvantage_internal
    generator test hadvantage

/-- The zero hybrid is exactly the independent uniform-output block.
@isnad1 id=eq.0h4v.s5.1815e3cd7dd4 from=translated src=- shape=523a3e2f vocab=1298c0ee
-/
theorem hybridOutput_zero {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput 0 randomness =
      blockSnd seedLength outputLength randomness :=
  hybridOutput_zero_internal generator randomness

/-- The final hybrid is exactly the generator output.
@isnad1 id=eq.0h4v.s5.5e0d9fe3e22e from=translated src=- shape=3fc8061d vocab=9da552bb
-/
theorem hybridOutput_outputLength {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput outputLength randomness =
      generator (blockFst seedLength outputLength randomness) :=
  hybridOutput_outputLength_internal generator randomness

/-- Test acceptance on the zero hybrid is its uniform acceptance probability.
@isnad1 id=eq.0h4v.s4.e4fa71d5fc9e from=translated src=- shape=a219118b vocab=12ee9a1b
-/
theorem hybridAcceptanceProbability_zero
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test 0 =
      uniformAcceptanceProbability test :=
  hybridAcceptanceProbability_zero_internal generator test

/-- Test acceptance on the final hybrid is its generated acceptance
probability.
@isnad1 id=eq.0h4v.s4.db4dc1c9ece7 from=translated src=- shape=52491adb vocab=57120b11
-/
theorem hybridAcceptanceProbability_outputLength
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test outputLength =
      generator.generatedAcceptanceProbability test :=
  hybridAcceptanceProbability_outputLength_internal generator test

/-- Adjacent hybrid gaps telescope exactly to the oriented distinguishing
gap between generated and uniform outputs.
@isnad1 id=eq.0h4v.s5.f5bab34cf7bb from=translated src=- shape=cf36495f vocab=5b6c63c6
-/
theorem sum_hybridGap {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    ∑ step ∈ Finset.range outputLength, generator.hybridGap test step =
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test :=
  sum_hybridGap_internal generator test

/-- If the oriented distinguishing gap is at least `advantage`, one adjacent
hybrid gap is at least `advantage / outputLength`.
@isnad1 id=ex.2h5v.s6.1967661ca87b from=translated src=- shape=86a9f65e vocab=ec70a742
-/
theorem exists_hybridGap_ge_average
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test) :
    ∃ step < outputLength,
      advantage / (outputLength : ℚ) ≤ generator.hybridGap test step :=
  exists_hybridGap_ge_average_internal
    generator test houtputLength hadvantage

/-- Finite Yao hybrid step: every absolute distinguishing advantage admits a
polarity and an adjacent hybrid whose gap is at least the average advantage.
@isnad1 id=ex.2h5v.s6.40c16a3b64bc from=translated src=- shape=386b23fa vocab=2874c891
-/
theorem exists_oriented_hybridGap_ge_average
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        advantage / (outputLength : ℚ) ≤
          generator.hybridGap (orientTest test complement) step :=
  exists_oriented_hybridGap_ge_average_internal
    generator test houtputLength hadvantage

end BitGenerator

end Complexity
