/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Internal

/-!
# Nisan--Wigderson set systems and generators -- proof internals
-/

public section

namespace Complexity

namespace NWDesign

/--
@isnad1 id=eq.0h5v.s4.8df320ca3e22 from=translated src=- shape=3043b3c7 vocab=229f1560
-/
theorem card_support_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) :
    (design.support output).card = inputLength := by
  simp [support]

/--
@isnad1 id=iff.0h6v.s6.e3117299263e from=translated src=- shape=597e35a0 vocab=71780821
-/
theorem mem_support_iff_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (coordinate : Fin seedLength) :
    coordinate ∈ design.support output ↔
      ∃ input : Fin inputLength,
        design.coordinates output input = coordinate := by
  simp [support]

/--
@isnad1 id=eq.0h6v.s5.12e8889c860a from=translated src=- shape=e3970142 vocab=c8936eb4
-/
theorem overlap_comm_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (first second : Fin outputLength) :
    design.overlap first second = design.overlap second first := by
  simp [overlap, Finset.inter_comm]

/--
@isnad1 id=eq.0h5v.s4.29e66f3a63e1 from=translated src=- shape=60fe9985 vocab=c8936eb4
-/
theorem overlap_self_internal {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) :
    design.overlap output output = inputLength := by
  simp [overlap, card_support_internal]

/--
@isnad1 id=le.0h6v.s4.06babb0850e3 from=translated src=- shape=33a9083b vocab=5f11e340
-/
theorem overlap_le_inputLength_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (first second : Fin outputLength) :
    design.overlap first second ≤ inputLength := by
  calc
    design.overlap first second ≤ (design.support first).card := by
      exact Finset.card_le_card Finset.inter_subset_left
    _ = inputLength := card_support_internal design first

/--
@isnad1 id=hasoverl.2h6v.s5.22a8dd0a4d2d from=translated src=- shape=8d4dd692 vocab=9ff4f575
-/
theorem hasOverlapBudget_mono_internal
    {outputLength inputLength seedLength first second : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget first) (hle : first ≤ second) :
    design.HasOverlapBudget second := by
  intro output
  exact (hbudget output).trans hle

/--
@isnad1 id=eq.0h7v.s5.5c31483a0629 from=translated src=- shape=aae59801 vocab=57cecd8b
-/
theorem restrictSeed_apply_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (seed : Fin seedLength → Bool)
    (input : Fin inputLength) :
    design.restrictSeed output seed input =
      seed (design.coordinates output input) := by
  rfl

/--
@isnad1 id=eq.0h7v.s5.300f69ea550d from=translated src=- shape=d84191e2 vocab=6d62ce00
-/
theorem generator_apply_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (seed : Fin seedLength → Bool) (output : Fin outputLength) :
    design.generator hardFunction seed output =
      hardFunction (design.restrictSeed output seed) := by
  rfl

/--
@isnad1 id=ex.4h11v.s6.28ec315a22c5 from=translated src=- shape=5fa345cd vocab=3c614e80
-/
theorem exists_oriented_hybridGap_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        density / (outputLength : ℚ) ≤
          (design.generator hardFunction).hybridGap
            (BitGenerator.orientTest test complement) step := by
  have hdistinguishes :
      density ≤
        (design.generator hardFunction).distinguishingAdvantage test :=
    BitGenerator.density_le_distinguishingAdvantage_of_randomTest_internal
      hlow hrandom hdense
  exact BitGenerator.exists_oriented_hybridGap_ge_average_internal
    (design.generator hardFunction) test houtputLength hdistinguishes

/--
@isnad1 id=ex.5h11v.s7.99e91934a51f from=translated src=- shape=63296d7e vocab=1bcfe267
-/
theorem exists_oriented_hybridGap_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold : ℕ}
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
    (hdense : BitGenerator.IsDenseTest test density) :
    ∃ (complement : Bool) (step : ℕ),
      step < outputLength ∧
        density / (outputLength : ℚ) ≤
          (design.generator hardFunction).hybridGap
            (BitGenerator.orientTest test complement) step := by
  apply exists_oriented_hybridGap_of_randomTest_internal
    houtputLength (hrandom := hrandom) (hdense := hdense)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

/--
@isnad1 id=ex.4h11v.s7.3425f68ef4c5 from=translated src=- shape=d2b9dd6d vocab=39c67447
-/
theorem exists_predictionSuccess_ge_half_add_density_div_internal
    {outputLength inputLength seedLength tapes time threshold : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density) :
    ∃ (complement : Bool) (step : Fin outputLength),
      1 / 2 + density / (outputLength : ℚ) ≤
        NextBitPrediction.successProbability
          ((design.generator hardFunction).targetBit step)
          ((design.generator hardFunction).testAtCandidate
            (BitGenerator.orientTest test complement) step) := by
  obtain ⟨complement, step, hstep, hgap⟩ :=
    exists_oriented_hybridGap_of_randomTest_internal
      houtputLength hlow hrandom hdense
  let coordinate : Fin outputLength := ⟨step, hstep⟩
  refine ⟨complement, coordinate, ?_⟩
  rw [BitGenerator.predictionSuccessProbability_eq_half_add_hybridGap_internal]
  simpa [coordinate, add_comm] using add_le_add_left hgap (1 / 2)

/--
@isnad1 id=ex.5h11v.s7.b9ebf36000ba from=translated src=- shape=f240d024 vocab=d0e0e090
-/
theorem exists_predictionSuccess_ge_half_add_density_div_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold : ℕ}
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
    (hdense : BitGenerator.IsDenseTest test density) :
    ∃ (complement : Bool) (step : Fin outputLength),
      1 / 2 + density / (outputLength : ℚ) ≤
        NextBitPrediction.successProbability
          ((design.generator hardFunction).targetBit step)
          ((design.generator hardFunction).testAtCandidate
            (BitGenerator.orientTest test complement) step) := by
  apply exists_predictionSuccess_ge_half_add_density_div_internal
    houtputLength (hrandom := hrandom) (hdense := hdense)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

end NWDesign

end Complexity
