/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Code
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.ConstructionRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Minimum construction rank of a Borel set

This file defines `borelRank s hs` as the least construction rank among all Borel codes whose
interpretation is `s`. The Borel measurability proof `hs` is an explicit argument so that a
non-Borel set is not silently assigned the infimum of an empty family.

This is a semantic minimum because it minimizes over every code representing the set. It is still
a minimum of `GeneratedCode.constructionRank`; it is not the least ordinal level at which `s`
belongs to `OrdinalSigma0` or `OrdinalPi0`. Keeping these notions separate prevents a complicated
presentation of a simple set from inflating the set's rank.

The minimum is attained. This follows from Borel-code completeness together with the well-ordering
of ordinals, exposed by mathlib's `isLeast_csInf`. Consequently every Borel rank is below `ω₁` and
the set appears in `generateMeasurableRec` by its minimum rank.
-/

open Cardinal MeasurableSpace Ordinal Set

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X]

/-- The construction ranks of all Borel codes whose interpretation is `s`.-/
def borelConstructionRanks (s : Set X) : Set Ordinal.{0} :=
  {i | ∃ c : BorelCode X, c.eval = s ∧ c.constructionRank = i}

private theorem borelConstructionRanks_nonempty {s : Set X}
    (hs : @MeasurableSet X (borel X) s) : (borelConstructionRanks s).Nonempty := by
  obtain ⟨c, hc⟩ := BorelCode.borelMeasurableSet_iff_exists_code.1 hs
  exact ⟨c.constructionRank, c, hc, rfl⟩

/-- The minimum construction rank of a Borel set.

The measurability proof is computationally irrelevant, but requiring it prevents this definition
from assigning the default ordinal infimum to a non-Borel set.-/
noncomputable def borelRank (s : Set X) (_ : @MeasurableSet X (borel X) s) : Ordinal.{0} :=
  sInf (borelConstructionRanks s)

/-- `borelRank` is the least construction rank of any code representing the set.-/
theorem isLeast_borelRank {s : Set X} (hs : @MeasurableSet X (borel X) s) :
    IsLeast (borelConstructionRanks s) (borelRank s hs) := by
  exact isLeast_csInf (borelConstructionRanks_nonempty hs)

/-- The value of `borelRank` is independent of the supplied measurability proof.-/
theorem borelRank_proof_irrel {s : Set X} (hs ht : @MeasurableSet X (borel X) s) :
    borelRank s hs = borelRank s ht := rfl

/-- The semantic Borel rank is bounded by the construction rank of every representing code.-/
theorem borelRank_le_constructionRank {s : Set X} (hs : @MeasurableSet X (borel X) s)
    (c : BorelCode X) (hc : c.eval = s) : borelRank s hs ≤ c.constructionRank :=
  (isLeast_borelRank hs).2 ⟨c, hc, rfl⟩

/-- Some Borel code representing the set attains its semantic Borel rank.-/
theorem exists_code_constructionRank_eq_borelRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    ∃ c : BorelCode X, c.eval = s ∧ c.constructionRank = borelRank s hs :=
  (isLeast_borelRank hs).1

/-- The semantic Borel rank of every Borel set is a countable ordinal.-/
theorem borelRank_lt_omega_one {s : Set X} (hs : @MeasurableSet X (borel X) s) :
    borelRank s hs < ω₁ := by
  obtain ⟨c, _, hc⟩ := exists_code_constructionRank_eq_borelRank hs
  rw [← hc]
  exact c.constructionRank_lt_omega_one

/-- A Borel set appears in mathlib's transfinite measurable-space generator by its minimum
construction rank.-/
theorem mem_generateMeasurableRec_borelRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    s ∈ generateMeasurableRec {t : Set X | IsOpen t} (borelRank s hs) := by
  obtain ⟨c, hc, hr⟩ := exists_code_constructionRank_eq_borelRank hs
  rw [← range_openGenerator X, ← hr, ← hc]
  exact c.eval_mem_generateMeasurableRec

/-- Every open set has semantic Borel rank zero.-/
theorem borelRank_eq_zero_of_isOpen {s : Set X} (hs : IsOpen s) :
    borelRank s (GenerateMeasurable.basic s hs) = 0 := by
  apply le_antisymm
  · exact borelRank_le_constructionRank _ (BorelCode.basic s hs) rfl
  · exact bot_le

end DescriptiveSetTheory
