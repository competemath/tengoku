/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Internal

/-!
# Nisan--Wigderson overlap hardwiring -- proof internals
-/

public section

namespace Complexity

namespace NWDesign

/--
@isnad1 id=eq.0h6v.s5.8d98c98cde13 from=translated src=- shape=70036b0b vocab=031938d5
-/
theorem map_challengeOverlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).map
        (design.coordinates current) =
      design.support current ∩ design.support previous := by
  ext coordinate
  simp [challengeOverlap, support]
  aesop

/--
@isnad1 id=eq.0h6v.s5.1290d13947c5 from=translated src=- shape=3c72a350 vocab=654ae3e8
-/
theorem card_challengeOverlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).card =
      design.overlap current previous := by
  rw [overlap, ← map_challengeOverlap_internal design current previous]
  simp

/--
@isnad1 id=eq.0h8v.s6.751d4d759095 from=translated src=- shape=8ac11cd7 vocab=c2d8a8c7
-/
theorem seedWithChallenge_apply_coordinates_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (input : Fin inputLength) :
    design.seedWithChallenge current outside challenge
        (design.coordinates current input) =
      challenge input := by
  simp [seedWithChallenge]

/--
@isnad1 id=eq.1h8v.s6.9619d17314e8 from=translated src=- shape=908087f0 vocab=f16116d9
-/
theorem seedWithChallenge_apply_of_not_mem_support_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (coordinate : Fin seedLength)
    (hcoordinate : coordinate ∉ design.support current) :
    design.seedWithChallenge current outside challenge coordinate =
      outside coordinate := by
  have hnotrange : coordinate ∉ Set.range (design.coordinates current) := by
    simpa [support] using hcoordinate
  simp [seedWithChallenge, hnotrange]

/--
@isnad1 id=eq.0h7v.s5.3de7b81a59a8 from=translated src=- shape=f7612732 vocab=7687b2bd
-/
theorem challengedBlock_current_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) :
    design.challengedBlock current current outside challenge = challenge := by
  funext input
  exact seedWithChallenge_apply_coordinates_internal
    design current outside challenge input

/--
@isnad1 id=dependso.0h7v.s5.d02559633da7 from=translated src=- shape=da0c8974 vocab=3d0bcf57
-/
theorem challengedBlock_dependsOn_overlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool) :
    DependsOn (design.challengedBlock current previous outside)
      (design.challengeOverlap current previous : Set (Fin inputLength)) := by
  intro first second hagree
  funext input
  by_cases hcoordinate :
      design.coordinates previous input ∈
        Set.range (design.coordinates current)
  · simp only [challengedBlock, restrictSeed, seedWithChallenge,
      hcoordinate, dite_true]
    apply hagree
    have hsame :
        design.coordinates current
            ((design.coordinates current).toEquivRange.symm
              ⟨design.coordinates previous input, hcoordinate⟩) =
          design.coordinates previous input := by
      exact congrArg Subtype.val
        ((design.coordinates current).toEquivRange.apply_symm_apply
          ⟨design.coordinates previous input, hcoordinate⟩)
    have hmember :
        design.coordinates current
            ((design.coordinates current).toEquivRange.symm
              ⟨design.coordinates previous input, hcoordinate⟩) ∈
          design.support previous := by
      rw [hsame]
      simp [support]
    simpa [challengeOverlap] using hmember
  · simp [challengedBlock, restrictSeed, seedWithChallenge, hcoordinate]

/--
@isnad1 id=dependso.0h8v.s6.5f5688eec76c from=translated src=- shape=2badab1a vocab=3d0bcf57
-/
theorem challengedValue_dependsOn_overlap_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool) :
    DependsOn
      (fun challenge =>
        observe (design.challengedBlock current previous outside challenge))
      (design.challengeOverlap current previous : Set (Fin inputLength)) := by
  intro first second hagree
  apply congrArg observe
  exact challengedBlock_dependsOn_overlap_internal
    design current previous outside hagree

/--
@isnad1 id=eq.0h9v.s6.1a607a7b743a from=translated src=- shape=11f64240 vocab=25367abf
-/
theorem predecessorTable_restrict_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool)
    (challenge : Fin inputLength → Bool) :
    design.predecessorTable current previous outside observe
        (BooleanDependency.restrict
          (design.challengeOverlap current previous) challenge) =
      observe (design.challengedBlock current previous outside challenge) := by
  exact BooleanDependency.table_restrict_internal
    (design.challengeOverlap current previous)
    (fun candidate =>
      observe (design.challengedBlock current previous outside candidate))
    (challengedValue_dependsOn_overlap_internal
      design current previous outside observe)
    challenge

/--
@isnad1 id=eq.0h6v.s8.9cd909a2cba2 from=translated src=- shape=5ce1ea82 vocab=f64986c4
-/
theorem card_predecessorAssignments_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    Fintype.card (design.challengeOverlap current previous → Bool) =
      2 ^ design.overlap current previous := by
  rw [← Nat.card_eq_fintype_card,
    BooleanDependency.card_assignments_internal,
    card_challengeOverlap_internal]

/--
@isnad1 id=eq.0h5v.s6.9e32bd6301b6 from=translated src=- shape=291fcc4d vocab=873a3e40
-/
theorem predecessorTableEntriesAt_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current =
      ∑ previous ∈ Finset.Iio current,
        2 ^ design.overlap current previous := by
  simp [predecessorTableEntriesAt, card_challengeOverlap_internal]

/--
@isnad1 id=eq.0h5v.s5.2d91b0a35622 from=translated src=- shape=df5272fa vocab=8f4dd13e
-/
theorem overlapCostAt_eq_predecessorTableEntriesAt_add_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.overlapCostAt current =
      design.predecessorTableEntriesAt current +
        (outputLength - (current.val + 1)) := by
  rw [overlapCostAt, predecessorTableEntriesAt_eq_internal]

/--
@isnad1 id=le.0h5v.s4.68ab5b1bea9f from=translated src=- shape=9b23b8a2 vocab=b161f888
-/
theorem predecessorTableEntriesAt_le_overlapCostAt_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤
      design.overlapCostAt current := by
  rw [overlapCostAt_eq_predecessorTableEntriesAt_add_internal]
  exact Nat.le_add_right _ _

/--
@isnad1 id=le.1h6v.s5.105cc2a6548b from=translated src=- shape=b7690c1c vocab=3f17c611
-/
theorem predecessorTableEntriesAt_le_of_hasOverlapBudget_internal
    {outputLength inputLength seedLength budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget budget)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤ budget :=
  (predecessorTableEntriesAt_le_overlapCostAt_internal design current).trans
    (hbudget current)

end NWDesign

end Complexity
