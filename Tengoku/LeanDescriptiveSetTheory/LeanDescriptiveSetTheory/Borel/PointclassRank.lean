/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.CodeHierarchy
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.SemanticRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Least Borel pointclass levels

This file defines the least additive, multiplicative, and ambiguous ordinal Borel levels of a
Borel set in a perfectly normal space.  Each definition takes an explicit Borel-measurability proof
instead of assigning a default value outside its mathematical domain.

These invariants are not `borelRank`: that older definition minimizes the construction rank of a
code.  The pointclass ranks below minimize indices of `OrdinalSigma0`, `OrdinalPi0`, and
`OrdinalDelta0`.  In the project's one-based hierarchy, every pointclass rank is positive, while an
open set has minimum code-construction rank zero.
-/

open Cardinal Ordinal Set

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X]

private def borelSigmaLevels (s : Set X) : Set Ordinal.{0} :=
  {i | OrdinalSigma0 i s}

private def borelPiLevels (s : Set X) : Set Ordinal.{0} :=
  {i | OrdinalPi0 i s}

private def borelDeltaLevels (s : Set X) : Set Ordinal.{0} :=
  {i | OrdinalDelta0 i s}

private noncomputable def leastOrdinalOfNonempty
    (levels : Set Ordinal.{0}) (_ : levels.Nonempty) : Ordinal.{0} :=
  sInf levels

section PerfectlyNormal

variable [PerfectlyNormalSpace X]

private theorem borelSigmaLevels_nonempty {s : Set X}
    (hs : @MeasurableSet X (borel X) s) : (borelSigmaLevels s).Nonempty := by
  obtain ⟨i, _, hi⟩ := borelMeasurableSet_exists_countable_ordinalDelta0 hs
  exact ⟨i, hi.1⟩

private theorem borelPiLevels_nonempty {s : Set X}
    (hs : @MeasurableSet X (borel X) s) : (borelPiLevels s).Nonempty := by
  obtain ⟨i, _, hi⟩ := borelMeasurableSet_exists_countable_ordinalDelta0 hs
  exact ⟨i, hi.2⟩

private theorem borelDeltaLevels_nonempty {s : Set X}
    (hs : @MeasurableSet X (borel X) s) : (borelDeltaLevels s).Nonempty := by
  obtain ⟨i, _, hi⟩ := borelMeasurableSet_exists_countable_ordinalDelta0 hs
  exact ⟨i, hi⟩

/-- The least additive Borel pointclass level of a Borel set.-/
noncomputable def borelSigmaRank (s : Set X)
    (hs : @MeasurableSet X (borel X) s) : Ordinal.{0} :=
  leastOrdinalOfNonempty (borelSigmaLevels s) (borelSigmaLevels_nonempty hs)

/-- The least multiplicative Borel pointclass level of a Borel set.-/
noncomputable def borelPiRank (s : Set X)
    (hs : @MeasurableSet X (borel X) s) : Ordinal.{0} :=
  leastOrdinalOfNonempty (borelPiLevels s) (borelPiLevels_nonempty hs)

/-- The least ambiguous Borel pointclass level of a Borel set.-/
noncomputable def borelDeltaRank (s : Set X)
    (hs : @MeasurableSet X (borel X) s) : Ordinal.{0} :=
  leastOrdinalOfNonempty (borelDeltaLevels s) (borelDeltaLevels_nonempty hs)

private theorem isLeast_borelSigmaRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    IsLeast (borelSigmaLevels s) (borelSigmaRank s hs) := by
  exact isLeast_csInf (borelSigmaLevels_nonempty hs)

private theorem isLeast_borelPiRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    IsLeast (borelPiLevels s) (borelPiRank s hs) := by
  exact isLeast_csInf (borelPiLevels_nonempty hs)

private theorem isLeast_borelDeltaRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    IsLeast (borelDeltaLevels s) (borelDeltaRank s hs) := by
  exact isLeast_csInf (borelDeltaLevels_nonempty hs)

/-- The least additive pointclass level is attained.-/
theorem ordinalSigma0_borelSigmaRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    OrdinalSigma0 (borelSigmaRank s hs) s :=
  (isLeast_borelSigmaRank hs).1

/-- The least multiplicative pointclass level is attained.-/
theorem ordinalPi0_borelPiRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    OrdinalPi0 (borelPiRank s hs) s :=
  (isLeast_borelPiRank hs).1

/-- The least ambiguous pointclass level is attained.-/
theorem ordinalDelta0_borelDeltaRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    OrdinalDelta0 (borelDeltaRank s hs) s :=
  (isLeast_borelDeltaRank hs).1

/-- Additive pointclass membership is exactly comparison with the least additive level.-/
theorem ordinalSigma0_iff_borelSigmaRank_le {s : Set X}
    (hs : @MeasurableSet X (borel X) s) (i : Ordinal.{0}) :
    OrdinalSigma0 i s ↔ borelSigmaRank s hs ≤ i := by
  constructor
  · intro hi
    exact (isLeast_borelSigmaRank hs).2 hi
  · intro hi
    exact (ordinalSigma0_borelSigmaRank hs).mono hi

/-- Multiplicative pointclass membership is exactly comparison with the least multiplicative
level.-/
theorem ordinalPi0_iff_borelPiRank_le {s : Set X}
    (hs : @MeasurableSet X (borel X) s) (i : Ordinal.{0}) :
    OrdinalPi0 i s ↔ borelPiRank s hs ≤ i := by
  constructor
  · intro hi
    exact (isLeast_borelPiRank hs).2 hi
  · intro hi
    exact (ordinalPi0_borelPiRank hs).mono hi

/-- Ambiguous pointclass membership is exactly comparison with the least ambiguous level.-/
theorem ordinalDelta0_iff_borelDeltaRank_le {s : Set X}
    (hs : @MeasurableSet X (borel X) s) (i : Ordinal.{0}) :
    OrdinalDelta0 i s ↔ borelDeltaRank s hs ≤ i := by
  constructor
  · intro hi
    exact (isLeast_borelDeltaRank hs).2 hi
  · intro hi
    exact (ordinalDelta0_borelDeltaRank hs).mono hi

/-- The least additive pointclass level of a Borel set is countable.-/
theorem borelSigmaRank_lt_omega_one {s : Set X}
    (hs : @MeasurableSet X (borel X) s) : borelSigmaRank s hs < ω₁ := by
  obtain ⟨i, hi, his⟩ := borelMeasurableSet_exists_countable_ordinalDelta0 hs
  exact ((ordinalSigma0_iff_borelSigmaRank_le hs i).1 his.1).trans_lt hi

/-- The least multiplicative pointclass level of a Borel set is countable.-/
theorem borelPiRank_lt_omega_one {s : Set X}
    (hs : @MeasurableSet X (borel X) s) : borelPiRank s hs < ω₁ := by
  obtain ⟨i, hi, his⟩ := borelMeasurableSet_exists_countable_ordinalDelta0 hs
  exact ((ordinalPi0_iff_borelPiRank_le hs i).1 his.2).trans_lt hi

/-- The multiplicative pointclass rank is independent of the supplied Borel proof.-/
theorem borelPiRank_proof_irrel {s : Set X}
    (hs ht : @MeasurableSet X (borel X) s) :
    borelPiRank s hs = borelPiRank s ht :=
  rfl

/-- The ambiguous pointclass rank is independent of the supplied Borel proof.-/
theorem borelDeltaRank_proof_irrel {s : Set X}
    (hs ht : @MeasurableSet X (borel X) s) :
    borelDeltaRank s hs = borelDeltaRank s ht :=
  rfl

/-- Ambiguous pointclass rank is extensional in the underlying set.-/
theorem borelDeltaRank_congr {s t : Set X} (hst : s = t)
    (hs : @MeasurableSet X (borel X) s) (ht : @MeasurableSet X (borel X) t) :
    borelDeltaRank s hs = borelDeltaRank t ht := by
  subst t
  exact borelDeltaRank_proof_irrel hs ht

/-- Complementation exchanges the least additive and multiplicative pointclass levels.-/
theorem borelSigmaRank_compl {s : Set X} (hs : @MeasurableSet X (borel X) s) :
    borelSigmaRank sᶜ hs.compl = borelPiRank s hs := by
  apply le_antisymm
  · exact (ordinalSigma0_iff_borelSigmaRank_le hs.compl _).1
      (ordinalPi0_borelPiRank hs).compl
  · have hpi : OrdinalPi0 (borelSigmaRank sᶜ hs.compl) s := by
      simpa using (ordinalSigma0_borelSigmaRank hs.compl).compl
    exact (ordinalPi0_iff_borelPiRank_le hs _).1 hpi

/-- The additive rank is no larger than the ambiguous rank.-/
theorem borelSigmaRank_le_borelDeltaRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    borelSigmaRank s hs ≤ borelDeltaRank s hs :=
  (ordinalSigma0_iff_borelSigmaRank_le hs _).1 (ordinalDelta0_borelDeltaRank hs).1

/-- The multiplicative rank is no larger than the ambiguous rank.-/
theorem borelPiRank_le_borelDeltaRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) :
    borelPiRank s hs ≤ borelDeltaRank s hs :=
  (ordinalPi0_iff_borelPiRank_le hs _).1 (ordinalDelta0_borelDeltaRank hs).2

private theorem one_le_borelDeltaRank {s : Set X}
    (hs : @MeasurableSet X (borel X) s) : 1 ≤ borelDeltaRank s hs := by
  exact Order.one_le_iff_ne_zero.mpr fun hzero =>
    ordinalSigma0_zero s (hzero ▸ (ordinalDelta0_borelDeltaRank hs).1)

/-- Every clopen set has least ambiguous pointclass level one.-/
theorem borelDeltaRank_eq_one_of_isClopen {s : Set X}
    (hm : @MeasurableSet X (borel X) s) (hsOpen : IsOpen s) (hsClosed : IsClosed s) :
    borelDeltaRank s hm = 1 :=
  le_antisymm ((ordinalDelta0_iff_borelDeltaRank_le hm 1).1
    ⟨ordinalSigma0_one_iff.2 hsOpen, ordinalPi0_one_iff.2 hsClosed⟩)
    (one_le_borelDeltaRank hm)

/-- An additive level witnessed not to be multiplicative is the exact least additive level.-/
theorem borelSigmaRank_eq_of_ordinalSigma0_not_ordinalPi0 {s : Set X}
    (hm : @MeasurableSet X (borel X) s) {i : Ordinal.{0}}
    (hs : OrdinalSigma0 i s) (hpi : ¬ OrdinalPi0 i s) :
    borelSigmaRank s hm = i := by
  apply le_antisymm
  · exact (ordinalSigma0_iff_borelSigmaRank_le hm i).1 hs
  · by_contra hle
    have hlt : borelSigmaRank s hm < i := lt_of_not_ge hle
    apply hpi
    exact (ordinalSigma0_borelSigmaRank hm).toPi0_succ.mono
      (Order.add_one_le_iff.mpr hlt)

end PerfectlyNormal

end DescriptiveSetTheory
