/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.OrdinalOperations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal sets for the countable ordinal Borel hierarchy

For every countable positive ordinal `i`, recursively construct a Baire-parameter relation whose
vertical sections are exactly the `OrdinalSigma0 i` subsets of the object space. Level one is the
universal open relation. Above level one, a parameter selects positive lower levels and parameters,
then `baireIndexedIUnion` takes the corresponding countable section union.

Level zero remains excluded: both ordinal polarities contain no sets there, while any relation over
the nonempty Baire parameter space has vertical sections.
-/

open Cardinal Ordinal Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

variable {X : Type u}

private noncomputable def ordinalUniversalSigmaAux (b : ℕ → Set X) (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set ((ℕ → ℕ) × X) :=
  if hi0 : i = 0 then
    ∅
  else if hi1 : i = 1 then
    baireParameterUniversalOpen b
  else
    have hi : (1 : Ordinal) < i :=
      lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr hi0) (Ne.symm hi1)
    baireIndexedIUnion fun k =>
      (ordinalUniversalSigmaAux b (positiveBorelLevelSequence i hi hic k).1
        ((positiveBorelLevelSequence i hi hic k).2.2.trans hic))ᶜ
termination_by i
decreasing_by
  exact (positiveBorelLevelSequence i hi hic k).2.2

/-- The universal additive relation at a countable ordinal level, using Baire parameters.-/
noncomputable def ordinalUniversalSigma (b : ℕ → Set X) (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set ((ℕ → ℕ) × X) :=
  ordinalUniversalSigmaAux b i hic

/-- The universal multiplicative relation at the same countable ordinal level.-/
noncomputable def ordinalUniversalPi (b : ℕ → Set X) (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set ((ℕ → ℕ) × X) :=
  (ordinalUniversalSigma b i hic)ᶜ

/-- At level one the recursive relation is the Baire-parameter universal open relation.-/
theorem ordinalUniversalSigma_one (b : ℕ → Set X) :
    ordinalUniversalSigma b (1 : Ordinal.{0}) (by simpa using isCountableBorelLevel_nat 1) =
      baireParameterUniversalOpen b := by
  rw [ordinalUniversalSigma, ordinalUniversalSigmaAux.eq_1]
  simp

/-- Above level one, the universal relation is the indexed union of complements of recursively
constructed lower-level relations.-/
theorem ordinalUniversalSigma_of_one_lt (b : ℕ → Set X) {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi : (1 : Ordinal) < i) :
    ordinalUniversalSigma b i hic = baireIndexedIUnion fun k =>
      (ordinalUniversalSigma b (positiveBorelLevelSequence i hi hic k).1
        ((positiveBorelLevelSequence i hi hic k).2.2.trans hic))ᶜ := by
  rw [ordinalUniversalSigma, ordinalUniversalSigmaAux.eq_1]
  simp only [dite_eq_right (ne_of_gt (zero_lt_one.trans hi)), dite_eq_right (ne_of_gt hi)]
  rfl

/-- At every positive countable level, the recursive additive relation has the advertised ordinal
Borel complexity.-/
theorem ordinalSigma0_ordinalUniversalSigma [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalSigma0 i (ordinalUniversalSigma b i hic) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
      by_cases hi1 : i = 1
      · subst i
        rw [ordinalUniversalSigma_one]
        have hbo : ∀ n, IsOpen (b n) := fun n => hb.isOpen (Set.mem_range_self n)
        exact ordinalSigma0_one_iff.2 (isOpen_baireParameterUniversalOpen hbo)
      · have hi : (1 : Ordinal) < i :=
          lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr (ne_of_gt hi0)) (Ne.symm hi1)
        rw [ordinalUniversalSigma_of_one_lt b hic hi]
        apply ordinalSigma0_baireIndexedIUnion hi (positiveBorelLevelSequence i hi hic)
        intro k
        let j := positiveBorelLevelSequence i hi hic k
        exact (ih j.1 j.2.2 (j.2.2.trans hic) j.2.1).compl

/-- At every positive countable level, the recursively generated sections are exactly the
additive-class subsets of the object space.-/
theorem isUniversalFor_ordinalUniversalSigma [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalSigma0 i) (ordinalUniversalSigma b i hic) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
      by_cases hi1 : i = 1
      · subst i
        rw [ordinalUniversalSigma_one]
        intro s
        simpa only [ordinalSigma0_one_iff] using
          (isUniversalFor_baireParameterUniversalOpen hb s)
      · have hi : (1 : Ordinal) < i :=
          lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr (ne_of_gt hi0)) (Ne.symm hi1)
        rw [ordinalUniversalSigma_of_one_lt b hic hi]
        apply isUniversalFor_baireIndexedIUnion_ordinal hi
          (positiveBorelLevelSequence i hi hic)
          (surjective_positiveBorelLevelSequence i hi hic)
        intro k
        let j := positiveBorelLevelSequence i hi hic k
        exact (ih j.1 j.2.2 (j.2.2.trans hic) j.2.1).compl_ordinalSigma0

/-- The multiplicative universal relation has the same positive countable ordinal complexity.-/
theorem ordinalPi0_ordinalUniversalPi [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalPi0 i (ordinalUniversalPi b i hic) :=
  (ordinalSigma0_ordinalUniversalSigma hb hic hi0).compl

/-- The multiplicative relation is universal for the corresponding ordinal class.-/
theorem isUniversalFor_ordinalUniversalPi [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalPi0 i) (ordinalUniversalPi b i hic) :=
  (isUniversalFor_ordinalUniversalSigma hb hic hi0).compl_ordinalSigma0

/-- The additive universal relation for Baire-space subsets at a countable ordinal level.-/
noncomputable def baireOrdinalUniversalSigma (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  ordinalUniversalSigma baireCylinderBasisSequence i hic

/-- The multiplicative universal relation for Baire-space subsets at a countable ordinal level.-/
noncomputable def baireOrdinalUniversalPi (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  ordinalUniversalPi baireCylinderBasisSequence i hic

/-- The additive universal relation for Cantor-space subsets at a countable ordinal level.-/
noncomputable def cantorOrdinalUniversalSigma (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set ((ℕ → ℕ) × (ℕ → Bool)) :=
  ordinalUniversalSigma cantorCylinderBasisSequence i hic

/-- The multiplicative universal relation for Cantor-space subsets at a countable ordinal level.-/
noncomputable def cantorOrdinalUniversalPi (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set ((ℕ → ℕ) × (ℕ → Bool)) :=
  ordinalUniversalPi cantorCylinderBasisSequence i hic

/-- The Baire additive relation belongs to its positive countable ordinal level.-/
theorem ordinalSigma0_baireOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalSigma0 i (baireOrdinalUniversalSigma i hic) :=
  ordinalSigma0_ordinalUniversalSigma
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Baire multiplicative relation belongs to its positive countable ordinal level.-/
theorem ordinalPi0_baireOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalPi0 i (baireOrdinalUniversalPi i hic) :=
  ordinalPi0_ordinalUniversalPi
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Cantor additive relation belongs to its positive countable ordinal level.-/
theorem ordinalSigma0_cantorOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalSigma0 i (cantorOrdinalUniversalSigma i hic) :=
  ordinalSigma0_ordinalUniversalSigma
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

/-- The Cantor multiplicative relation belongs to its positive countable ordinal level.-/
theorem ordinalPi0_cantorOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalPi0 i (cantorOrdinalUniversalPi i hic) :=
  ordinalPi0_ordinalUniversalPi
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

/-- The Baire additive relation is universal for all subsets in its ordinal class.-/
theorem isUniversalFor_baireOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalSigma0 i) (baireOrdinalUniversalSigma i hic) :=
  isUniversalFor_ordinalUniversalSigma
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Baire multiplicative relation is universal for all subsets in its ordinal class.-/
theorem isUniversalFor_baireOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalPi0 i) (baireOrdinalUniversalPi i hic) :=
  isUniversalFor_ordinalUniversalPi
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Cantor additive relation is universal for all subsets in its ordinal class.-/
theorem isUniversalFor_cantorOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalSigma0 i) (cantorOrdinalUniversalSigma i hic) :=
  isUniversalFor_ordinalUniversalSigma
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

/-- The Cantor multiplicative relation is universal for all subsets in its ordinal class.-/
theorem isUniversalFor_cantorOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalPi0 i) (cantorOrdinalUniversalPi i hic) :=
  isUniversalFor_ordinalUniversalPi
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

end DescriptiveSetTheory
