/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Defs

/-!
# Hybrid distributions for finite binary generators -- proof internals
-/

public section

namespace Complexity

namespace BitGenerator

/--
@isnad1 id=eq.0h2v.s4.6f4eaa07fd37 from=translated src=- shape=e682e438 vocab=5a2b3b89
-/
theorem orientTest_false_internal {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test false = test := by
  rfl

/--
@isnad1 id=eq.0h2v.s6.635877b12067 from=translated src=- shape=687d2d15 vocab=1cee39ff
-/
theorem orientTest_true_internal {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    orientTest test true = testᶜ := by
  rfl

/--
@isnad1 id=eq.0h4v.s7.0d7218f2ce5d from=translated src=- shape=565bc8de vocab=79869fec
-/
theorem acceptedSeeds_compl_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.acceptedSeeds testᶜ = (generator.acceptedSeeds test)ᶜ := by
  ext seed
  simp [acceptedSeeds]

/--
@isnad1 id=eq.0h2v.s6.f823617b59a9 from=translated src=- shape=e00dfac1 vocab=d0e43a2c
-/
theorem uniformAcceptanceProbability_compl_internal {outputLength : ℕ}
    (test : Finset (Fin outputLength → Bool)) :
    uniformAcceptanceProbability testᶜ =
      1 - uniformAcceptanceProbability test := by
  exact eventProb_compl test

/--
@isnad1 id=eq.0h4v.s6.9ce11aa0b844 from=translated src=- shape=4afbbe7e vocab=3149b7db
-/
theorem generatedAcceptanceProbability_compl_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.generatedAcceptanceProbability testᶜ =
      1 - generator.generatedAcceptanceProbability test := by
  change eventProb (generator.acceptedSeeds testᶜ) =
    1 - eventProb (generator.acceptedSeeds test)
  rw [acceptedSeeds_compl_internal, eventProb_compl]

/--
@isnad1 id=ex.1h5v.s5.641f3c20b631 from=translated src=- shape=a72f049d vocab=80b37369
-/
theorem exists_orientation_of_distinguishingAdvantage_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ complement : Bool,
      advantage ≤
        generator.generatedAcceptanceProbability
            (orientTest test complement) -
          uniformAcceptanceProbability (orientTest test complement) := by
  by_cases hnonnegative :
      0 ≤ uniformAcceptanceProbability test -
        generator.generatedAcceptanceProbability test
  · refine ⟨true, ?_⟩
    rw [orientTest_true_internal,
      generatedAcceptanceProbability_compl_internal,
      uniformAcceptanceProbability_compl_internal]
    rw [distinguishingAdvantage,
      abs_of_nonneg hnonnegative] at hadvantage
    linarith
  · refine ⟨false, ?_⟩
    rw [orientTest_false_internal]
    have hnegative :
        uniformAcceptanceProbability test -
            generator.generatedAcceptanceProbability test < 0 :=
      lt_of_not_ge hnonnegative
    rw [distinguishingAdvantage, abs_of_neg hnegative] at hadvantage
    linarith

/--
@isnad1 id=eq.0h4v.s5.1815e3cd7dd4 from=translated src=- shape=523a3e2f vocab=1298c0ee
-/
theorem hybridOutput_zero_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput 0 randomness =
      blockSnd seedLength outputLength randomness := by
  funext coordinate
  simp [hybridOutput]

/--
@isnad1 id=eq.0h4v.s5.5e0d9fe3e22e from=translated src=- shape=3fc8061d vocab=9da552bb
-/
theorem hybridOutput_outputLength_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    generator.hybridOutput outputLength randomness =
      generator (blockFst seedLength outputLength randomness) := by
  funext coordinate
  simp [hybridOutput, coordinate.isLt]

/--
@isnad1 id=eq.0h4v.s4.e4fa71d5fc9e from=translated src=- shape=a219118b vocab=12ee9a1b
-/
theorem hybridAcceptanceProbability_zero_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test 0 =
      uniformAcceptanceProbability test := by
  change eventProb (generator.hybridAcceptedRandomness test 0) =
    uniformAcceptanceProbability test
  have hevent :
      generator.hybridAcceptedRandomness test 0 =
        Finset.univ.filter fun randomness :
            Fin (seedLength + outputLength) → Bool =>
          True ∧ blockSnd seedLength outputLength randomness ∈ test := by
    ext randomness
    simp [hybridAcceptedRandomness, hybridOutput_zero_internal]
  rw [hevent]
  calc
    eventProb (Finset.univ.filter fun randomness :
          Fin (seedLength + outputLength) → Bool =>
        True ∧ blockSnd seedLength outputLength randomness ∈ test) =
        eventProb (Finset.univ.filter
          (fun _seed : Fin seedLength → Bool => True)) *
        eventProb (Finset.univ.filter
          (fun output : Fin outputLength → Bool => output ∈ test)) := by
      simpa only using eventProb_block
        (fun _seed : Fin seedLength → Bool => True)
        (fun output : Fin outputLength → Bool => output ∈ test)
    _ = uniformAcceptanceProbability test := by
      simp [uniformAcceptanceProbability]

/--
@isnad1 id=eq.0h4v.s4.db4dc1c9ece7 from=translated src=- shape=52491adb vocab=57120b11
-/
theorem hybridAcceptanceProbability_outputLength_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    generator.hybridAcceptanceProbability test outputLength =
      generator.generatedAcceptanceProbability test := by
  change eventProb
      (generator.hybridAcceptedRandomness test outputLength) =
    generator.generatedAcceptanceProbability test
  have hevent :
      generator.hybridAcceptedRandomness test outputLength =
        Finset.univ.filter fun randomness :
            Fin (seedLength + outputLength) → Bool =>
          generator (blockFst seedLength outputLength randomness) ∈ test ∧
            True := by
    ext randomness
    simp [hybridAcceptedRandomness,
      hybridOutput_outputLength_internal]
  rw [hevent]
  calc
    eventProb (Finset.univ.filter fun randomness :
          Fin (seedLength + outputLength) → Bool =>
        generator (blockFst seedLength outputLength randomness) ∈ test ∧
          True) =
        eventProb (Finset.univ.filter
          (fun seed : Fin seedLength → Bool => generator seed ∈ test)) *
        eventProb (Finset.univ.filter
          (fun _output : Fin outputLength → Bool => True)) := by
      simpa only using eventProb_block
        (fun seed : Fin seedLength → Bool => generator seed ∈ test)
        (fun _output : Fin outputLength → Bool => True)
    _ = generator.generatedAcceptanceProbability test := by
      simp [generatedAcceptanceProbability, acceptedSeeds]

/--
@isnad1 id=eq.0h4v.s5.f5bab34cf7bb from=translated src=- shape=cf36495f vocab=5b6c63c6
-/
theorem sum_hybridGap_internal {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) :
    ∑ step ∈ Finset.range outputLength, generator.hybridGap test step =
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test := by
  change
    ∑ step ∈ Finset.range outputLength,
        (generator.hybridAcceptanceProbability test (step + 1) -
          generator.hybridAcceptanceProbability test step) = _
  rw [Finset.sum_range_sub,
    hybridAcceptanceProbability_outputLength_internal,
    hybridAcceptanceProbability_zero_internal]

/--
@isnad1 id=ex.2h5v.s6.1967661ca87b from=translated src=- shape=86a9f65e vocab=ec70a742
-/
theorem exists_hybridGap_ge_average_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤
      generator.generatedAcceptanceProbability test -
        uniformAcceptanceProbability test) :
    ∃ step < outputLength,
      advantage / (outputLength : ℚ) ≤ generator.hybridGap test step := by
  have hsum :
      advantage ≤
        ∑ step ∈ Finset.range outputLength,
          generator.hybridGap test step := by
    rw [sum_hybridGap_internal]
    exact hadvantage
  have hnonzero : (outputLength : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt houtputLength)
  have hconstant :
      ∑ _step ∈ Finset.range outputLength,
          advantage / (outputLength : ℚ) = advantage := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hle :
      ∑ _step ∈ Finset.range outputLength,
          advantage / (outputLength : ℚ) ≤
        ∑ step ∈ Finset.range outputLength,
          generator.hybridGap test step := by
    rw [hconstant]
    exact hsum
  obtain ⟨step, hstep, hgap⟩ :=
    Finset.exists_le_of_sum_le
      (⟨0, Finset.mem_range.mpr houtputLength⟩ :
        (Finset.range outputLength).Nonempty) hle
  exact ⟨step, Finset.mem_range.mp hstep, hgap⟩

/--
@isnad1 id=ex.2h5v.s6.40c16a3b64bc from=translated src=- shape=386b23fa vocab=2874c891
-/
theorem exists_oriented_hybridGap_ge_average_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool)) {advantage : ℚ}
    (houtputLength : 0 < outputLength)
    (hadvantage : advantage ≤ generator.distinguishingAdvantage test) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        advantage / (outputLength : ℚ) ≤
          generator.hybridGap (orientTest test complement) step := by
  obtain ⟨complement, horiented⟩ :=
    exists_orientation_of_distinguishingAdvantage_internal
      generator test hadvantage
  obtain ⟨step, hstep, hgap⟩ :=
    exists_hybridGap_ge_average_internal generator
      (orientTest test complement) houtputLength horiented
  exact ⟨complement, step, hstep, hgap⟩

end BitGenerator

end Complexity
