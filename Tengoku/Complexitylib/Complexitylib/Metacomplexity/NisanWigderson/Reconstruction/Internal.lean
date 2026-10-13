/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Internal

/-!
# Nisan--Wigderson fixed-advice reconstruction -- proof internals
-/

public section

namespace Complexity

namespace NWDesign

private theorem blockAppend_natAdd_internal
    {seedLength outputLength : ℕ}
    (seed : Fin seedLength → Bool) (tail : Fin outputLength → Bool)
    (coordinate : Fin outputLength) :
    blockAppend seedLength outputLength seed tail
        (Fin.natAdd seedLength coordinate) = tail coordinate := by
  have happ := congrFun
    (blockSnd_append seedLength outputLength seed tail) coordinate
  rw [blockSnd_apply] at happ
  exact happ

/--
@isnad1 id=eq.0h5v.s5.a7345e7eac8a from=translated src=- shape=b3906c49 vocab=38aeb6db
-/
theorem card_outsideCoordinates_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    (design.outsideCoordinates current).card = seedLength - inputLength := by
  rw [outsideCoordinates, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [card_support_internal]

/--
@isnad1 id=eq.0h2v.s5.3ff1691bacea from=translated src=- shape=4b9e5f29 vocab=c5b1c84e
-/
theorem card_laterCoordinates_internal {outputLength : ℕ}
    (current : Fin outputLength) :
    (laterCoordinates current).card = outputLength - (current.val + 1) := by
  simp [laterCoordinates]
  omega

/--
@isnad1 id=eq.0h5v.s8.e3672d41b395 from=translated src=- shape=5a24c21d vocab=c7bdbb25
-/
theorem card_outsideAssignments_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    Fintype.card (design.outsideCoordinates current → Bool) =
      2 ^ (seedLength - inputLength) := by
  simp [card_outsideCoordinates_internal]

/--
@isnad1 id=eq.0h2v.s7.b53001b3e3c6 from=translated src=- shape=b63073db vocab=5260e24b
-/
theorem card_laterAssignments_internal {outputLength : ℕ}
    (current : Fin outputLength) :
    Fintype.card (laterCoordinates current → Bool) =
      2 ^ (outputLength - (current.val + 1)) := by
  simp [card_laterCoordinates_internal]

/--
@isnad1 id=eq.0h8v.s6.7c9e14985955 from=translated src=- shape=e49ee479 vocab=8c7f926b
-/
theorem reconstructionSeed_apply_coordinates_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (input : Fin inputLength) :
    design.reconstructionSeed current outside challenge
        (design.coordinates current input) =
      challenge input := by
  exact seedWithChallenge_apply_coordinates_internal design current
    (design.outsideSeed current outside) challenge input

/--
@isnad1 id=eq.0h8v.s6.4a5b6b9ce932 from=translated src=- shape=3e55afdb vocab=e7106326
-/
theorem reconstructionSeed_apply_outside_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (challenge : Fin inputLength → Bool)
    (coordinate : design.outsideCoordinates current) :
    design.reconstructionSeed current outside challenge coordinate =
      outside coordinate := by
  have hcoordinate : coordinate.val ∉ design.support current := by
    exact (Finset.mem_sdiff.mp coordinate.property).2
  calc
    design.reconstructionSeed current outside challenge coordinate =
        design.outsideSeed current outside coordinate :=
      seedWithChallenge_apply_of_not_mem_support_internal design current
        (design.outsideSeed current outside) challenge coordinate hcoordinate
    _ = outside coordinate := by
      simp [outsideSeed, BooleanDependency.extendByFalse,
        coordinate.property]

/--
@isnad1 id=eq.0h6v.s5.d0a272be0907 from=translated src=- shape=56fe38d1 vocab=06d2aa09
-/
theorem reconstructionSeed_restrict_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (seed : Fin seedLength → Bool) :
    design.reconstructionSeed current
        (BooleanDependency.restrict
          (design.outsideCoordinates current) seed)
        (design.restrictSeed current seed) =
      seed := by
  funext coordinate
  by_cases hcoordinate : coordinate ∈ design.support current
  · obtain ⟨input, rfl⟩ :=
      (mem_support_iff_internal design current coordinate).mp hcoordinate
    simp [reconstructionSeed_apply_coordinates_internal, restrictSeed]
  · let outsideCoordinate : design.outsideCoordinates current :=
      ⟨coordinate, by simp [outsideCoordinates, hcoordinate]⟩
    simpa [outsideCoordinate, BooleanDependency.restrict] using
      reconstructionSeed_apply_outside_internal design current
        (BooleanDependency.restrict
          (design.outsideCoordinates current) seed)
        (design.restrictSeed current seed) outsideCoordinate

/--
@isnad1 id=eq.0h9v.s6.b0578d1bbe0f from=translated src=- shape=c078113d vocab=ff1af1d3
-/
theorem reconstructionBackground_targetBit_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) :
    (design.generator hardFunction).targetBit current
        (design.reconstructionBackground current outside later challenge) =
      hardFunction challenge := by
  simp only [BitGenerator.targetBit, generator, reconstructionBackground]
  apply congrArg hardFunction
  funext input
  exact reconstructionSeed_apply_coordinates_internal
    design current outside challenge input

/--
@isnad1 id=eq.0h10v.s7.a8a6fc30c8e3 from=translated src=- shape=729f494b vocab=372d93b1
-/
theorem reconstructionQuery_eq_hybridOutput_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (candidate : Bool) :
    design.reconstructionQuery hardFunction current outside later
        challenge candidate =
      (design.generator hardFunction).hybridOutput current.val
        (BitGenerator.assembleCandidate
          (design.reconstructionBackground current outside later challenge)
          candidate) := by
  funext output
  by_cases hbefore : output.val < current.val
  · simp [reconstructionQuery, hbefore, BitGenerator.hybridOutput,
      BitGenerator.assembleCandidate, reconstructionBackground,
      reconstructionSeed, generator, challengedBlock,
      predecessorTable_restrict_internal]
  · simp [reconstructionQuery, hbefore, BitGenerator.hybridOutput,
      BitGenerator.assembleCandidate, reconstructionBackground,
      blockAppend_natAdd_internal]

/--
@isnad1 id=eq.0h11v.s7.888937830ee5 from=translated src=- shape=10d245cf vocab=1bc77656
-/
theorem reconstructionTestAtCandidate_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool)
    (challenge : Fin inputLength → Bool) (candidate : Bool) :
    design.reconstructionTestAtCandidate hardFunction test current outside
        later challenge candidate =
      (design.generator hardFunction).testAtCandidate test current
        (design.reconstructionBackground current outside later challenge)
        candidate := by
  simp only [reconstructionTestAtCandidate, BitGenerator.testAtCandidate]
  rw [reconstructionQuery_eq_hybridOutput_internal]

/--
@isnad1 id=eq.0h11v.s7.ccbf8b6819ba from=translated src=- shape=063791a5 vocab=f0248ec3
-/
theorem reconstructionPredictor_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool) (candidate : Bool)
    (challenge : Fin inputLength → Bool) :
    design.reconstructionPredictor hardFunction test current outside later
        candidate challenge =
      NextBitPrediction.predictFromTest
        ((design.generator hardFunction).testAtCandidate test current
          (design.reconstructionBackground current outside later challenge)
          candidate)
        candidate := by
  rw [reconstructionPredictor,
    reconstructionTestAtCandidate_eq_internal]

/--
@isnad1 id=iff.0h11v.s7.8e6603cfa429 from=translated src=- shape=7bcd01d2 vocab=027d3dad
-/
theorem reconstructionPredictor_agrees_iff_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength)
    (outside : design.outsideCoordinates current → Bool)
    (later : laterCoordinates current → Bool) (candidate : Bool)
    (challenge : Fin inputLength → Bool) :
    design.reconstructionPredictor hardFunction test current outside later
        candidate challenge = hardFunction challenge ↔
      NextBitPrediction.predictFromTest
          ((design.generator hardFunction).testAtCandidate test current
            (design.reconstructionBackground current outside later challenge)
            candidate)
          candidate =
        (design.generator hardFunction).targetBit current
          (design.reconstructionBackground current outside later challenge) := by
  rw [reconstructionPredictor_eq_internal,
    reconstructionBackground_targetBit_internal]

/--
@isnad1 id=eq.0h5v.s5.4feb8be69026 from=translated src=- shape=8c10c7e1 vocab=7654787e
-/
theorem reconstructionDataBitsAt_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.reconstructionDataBitsAt current =
      design.overlapCostAt current + (seedLength - inputLength) + 1 := by
  rw [reconstructionDataBitsAt,
    overlapCostAt_eq_predecessorTableEntriesAt_add_internal,
    card_laterCoordinates_internal, card_outsideCoordinates_internal]

/--
@isnad1 id=le.1h6v.s5.cd7133c77b9f from=translated src=- shape=d52fe1e4 vocab=fd209d03
-/
theorem reconstructionDataBitsAt_le_of_hasOverlapBudget_internal
    {outputLength inputLength seedLength budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget budget)
    (current : Fin outputLength) :
    design.reconstructionDataBitsAt current ≤
      budget + (seedLength - inputLength) + 1 := by
  rw [reconstructionDataBitsAt_eq_internal]
  exact Nat.add_le_add_right (Nat.add_le_add_right (hbudget current) _) _

end NWDesign

end Complexity
