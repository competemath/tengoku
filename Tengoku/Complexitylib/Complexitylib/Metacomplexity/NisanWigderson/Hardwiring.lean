/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.NisanWigderson.Hardwiring.Internal

/-!
# Nisan--Wigderson overlap hardwiring

When one NW block is replaced by a challenge, each predecessor block depends on
only the challenge coordinates in their intersection. Its observed Boolean
value is therefore recoverable from a canonical table with exactly
`2^|S_i ∩ S_j|` entries. Summing these entry counts gives precisely the
predecessor term in the design's overlap cost.
-/

public section

namespace Complexity

namespace NWDesign

/-- Mapping overlap coordinates through the current block embedding produces
exactly the intersection of the two block supports.
@isnad1 id=eq.0h6v.s5.8d98c98cde13 from=translated src=- shape=70036b0b vocab=031938d5
-/
theorem map_challengeOverlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).map
        (design.coordinates current) =
      design.support current ∩ design.support previous :=
  map_challengeOverlap_internal design current previous

/-- Challenge overlap has exactly the design's recorded intersection size.
@isnad1 id=eq.0h6v.s5.1290d13947c5 from=translated src=- shape=3c72a350 vocab=654ae3e8
-/
@[simp] theorem card_challengeOverlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    (design.challengeOverlap current previous).card =
      design.overlap current previous :=
  card_challengeOverlap_internal design current previous

/-- Inserting a challenge makes the current block read exactly that challenge.
@isnad1 id=eq.0h8v.s6.751d4d759095 from=translated src=- shape=8ac11cd7 vocab=c2d8a8c7
-/
@[simp] theorem seedWithChallenge_apply_coordinates
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (input : Fin inputLength) :
    design.seedWithChallenge current outside challenge
        (design.coordinates current input) =
      challenge input :=
  seedWithChallenge_apply_coordinates_internal
    design current outside challenge input

/-- Challenge insertion leaves every coordinate outside the current support
unchanged.
@isnad1 id=eq.1h8v.s6.9619d17314e8 from=translated src=- shape=908087f0 vocab=f16116d9
-/
theorem seedWithChallenge_apply_of_not_mem_support
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) (coordinate : Fin seedLength)
    (hcoordinate : coordinate ∉ design.support current) :
    design.seedWithChallenge current outside challenge coordinate =
      outside coordinate :=
  seedWithChallenge_apply_of_not_mem_support_internal
    design current outside challenge coordinate hcoordinate

/-- The challenged current block is definitionally faithful to the challenge.
@isnad1 id=eq.0h7v.s5.3de7b81a59a8 from=translated src=- shape=f7612732 vocab=7687b2bd
-/
@[simp] theorem challengedBlock_current
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) :
    design.challengedBlock current current outside challenge = challenge :=
  challengedBlock_current_internal design current outside challenge

/-- A predecessor block depends on the challenge only through the two blocks'
intersection coordinates.
@isnad1 id=dependso.0h7v.s5.d02559633da7 from=translated src=- shape=da0c8974 vocab=3d0bcf57
-/
theorem challengedBlock_dependsOn_overlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool) :
    DependsOn (design.challengedBlock current previous outside)
      (design.challengeOverlap current previous : Set (Fin inputLength)) :=
  challengedBlock_dependsOn_overlap_internal
    design current previous outside

/-- Any Boolean observation of a predecessor block has the same overlap-only
dependency.
@isnad1 id=dependso.0h8v.s6.5f5688eec76c from=translated src=- shape=2badab1a vocab=3d0bcf57
-/
theorem challengedValue_dependsOn_overlap
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool) :
    DependsOn
      (fun challenge =>
        observe (design.challengedBlock current previous outside challenge))
      (design.challengeOverlap current previous : Set (Fin inputLength)) :=
  challengedValue_dependsOn_overlap_internal
    design current previous outside observe

/-- Looking up the actual overlap restriction in the canonical predecessor
table recovers the observed predecessor value.
@isnad1 id=eq.0h9v.s6.1a607a7b743a from=translated src=- shape=11f64240 vocab=25367abf
-/
@[simp] theorem predecessorTable_restrict
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool)
    (challenge : Fin inputLength → Bool) :
    design.predecessorTable current previous outside observe
        (BooleanDependency.restrict
          (design.challengeOverlap current previous) challenge) =
      observe (design.challengedBlock current previous outside challenge) :=
  predecessorTable_restrict_internal
    design current previous outside observe challenge

/-- The assignment space indexing one predecessor table has exactly one entry
for every Boolean assignment to the intersection.
@isnad1 id=eq.0h6v.s8.9cd909a2cba2 from=translated src=- shape=5ce1ea82 vocab=f64986c4
-/
theorem card_predecessorAssignments
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) :
    Fintype.card (design.challengeOverlap current previous → Bool) =
      2 ^ design.overlap current previous :=
  card_predecessorAssignments_internal design current previous

/-- Total predecessor-table entries equal the sum of the standard exponential
intersection costs.
@isnad1 id=eq.0h5v.s6.9e32bd6301b6 from=translated src=- shape=291fcc4d vocab=873a3e40
-/
theorem predecessorTableEntriesAt_eq
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current =
      ∑ previous ∈ Finset.Iio current,
        2 ^ design.overlap current previous :=
  predecessorTableEntriesAt_eq_internal design current

/-- The exact design overlap cost is the predecessor-table cost plus one unit
for every later output coordinate.
@isnad1 id=eq.0h5v.s5.2d91b0a35622 from=translated src=- shape=df5272fa vocab=8f4dd13e
-/
theorem overlapCostAt_eq_predecessorTableEntriesAt_add
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.overlapCostAt current =
      design.predecessorTableEntriesAt current +
        (outputLength - (current.val + 1)) :=
  overlapCostAt_eq_predecessorTableEntriesAt_add_internal design current

/-- Predecessor tables fit within the exact overlap cost.
@isnad1 id=le.0h5v.s4.68ab5b1bea9f from=translated src=- shape=9b23b8a2 vocab=b161f888
-/
theorem predecessorTableEntriesAt_le_overlapCostAt
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤
      design.overlapCostAt current :=
  predecessorTableEntriesAt_le_overlapCostAt_internal design current

/-- A weak-design overlap budget bounds all predecessor hardwiring tables.
@isnad1 id=le.1h6v.s5.105cc2a6548b from=translated src=- shape=b7690c1c vocab=3f17c611
-/
theorem predecessorTableEntriesAt_le_of_hasOverlapBudget
    {outputLength inputLength seedLength budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (hbudget : design.HasOverlapBudget budget)
    (current : Fin outputLength) :
    design.predecessorTableEntriesAt current ≤ budget :=
  predecessorTableEntriesAt_le_of_hasOverlapBudget_internal hbudget current

end NWDesign

end Complexity
