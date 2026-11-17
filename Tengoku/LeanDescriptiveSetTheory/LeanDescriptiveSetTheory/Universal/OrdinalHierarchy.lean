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

/-- At level one the recursive relation is the Baire-parameter universal open relation.
@isnad1 id=eq.0h2v.s4.2f6c8cfcd2d9 from=translated src=- shape=15526353 vocab=642bc46d
-/
theorem ordinalUniversalSigma_one (b : ℕ → Set X) :
    ordinalUniversalSigma b (1 : Ordinal.{0}) (by simpa using isCountableBorelLevel_nat 1) =
      baireParameterUniversalOpen b := by
  rw [ordinalUniversalSigma, ordinalUniversalSigmaAux.eq_1]
  simp

/-- Above level one, the universal relation is the indexed union of complements of recursively
constructed lower-level relations.
@isnad1 id=eq.2h3v.s6.4e65251b441c from=translated src=- shape=6259b9ef vocab=d767c58f
-/
theorem ordinalUniversalSigma_of_one_lt (b : ℕ → Set X) {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi : (1 : Ordinal) < i) :
    ordinalUniversalSigma b i hic = baireIndexedIUnion fun k =>
      (ordinalUniversalSigma b (positiveBorelLevelSequence i hi hic k).1
        ((positiveBorelLevelSequence i hi hic k).2.2.trans hic))ᶜ := by
  rw [ordinalUniversalSigma, ordinalUniversalSigmaAux.eq_1]
  simp only [dite_eq_right (ne_of_gt (zero_lt_one.trans hi)), dite_eq_right (ne_of_gt hi)]
  rfl

/-- At every positive countable level, the recursive additive relation has the advertised ordinal
Borel complexity.
@isnad1 id=ordinals.3h3v.s6.fcd26c28083f from=translated src=- shape=dfbfe792 vocab=9bee673c
-/
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
additive-class subsets of the object space.
@isnad1 id=isuniver.3h3v.s5.07e1a35aed6e from=translated src=- shape=417d694c vocab=eb1db942
-/
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

/-- The multiplicative universal relation has the same positive countable ordinal complexity.
@isnad1 id=ordinalp.3h3v.s6.c613299c0634 from=translated src=- shape=dfbfe792 vocab=8ba804b6
-/
theorem ordinalPi0_ordinalUniversalPi [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalPi0 i (ordinalUniversalPi b i hic) :=
  (ordinalSigma0_ordinalUniversalSigma hb hic hi0).compl

/-- The multiplicative relation is universal for the corresponding ordinal class.
@isnad1 id=isuniver.3h3v.s5.fc0563da78f1 from=translated src=- shape=417d694c vocab=2f124f11
-/
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

/-- The Baire additive relation belongs to its positive countable ordinal level.
@isnad1 id=ordinals.2h1v.s5.1b18e9c10f8b from=translated src=- shape=f85169c1 vocab=60356af8
-/
theorem ordinalSigma0_baireOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalSigma0 i (baireOrdinalUniversalSigma i hic) :=
  ordinalSigma0_ordinalUniversalSigma
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Baire multiplicative relation belongs to its positive countable ordinal level.
@isnad1 id=ordinalp.2h1v.s5.3880d93263be from=translated src=- shape=f85169c1 vocab=98b3fc03
-/
theorem ordinalPi0_baireOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalPi0 i (baireOrdinalUniversalPi i hic) :=
  ordinalPi0_ordinalUniversalPi
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Cantor additive relation belongs to its positive countable ordinal level.
@isnad1 id=ordinals.2h1v.s5.b1c0420e6b6b from=translated src=- shape=2aab4a43 vocab=c72c7899
-/
theorem ordinalSigma0_cantorOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalSigma0 i (cantorOrdinalUniversalSigma i hic) :=
  ordinalSigma0_ordinalUniversalSigma
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

/-- The Cantor multiplicative relation belongs to its positive countable ordinal level.
@isnad1 id=ordinalp.2h1v.s5.5c706d4d1eb6 from=translated src=- shape=2aab4a43 vocab=786adf6f
-/
theorem ordinalPi0_cantorOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalPi0 i (cantorOrdinalUniversalPi i hic) :=
  ordinalPi0_ordinalUniversalPi
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

/-- The Baire additive relation is universal for all subsets in its ordinal class.
@isnad1 id=isuniver.2h1v.s5.09093c6cc138 from=translated src=- shape=44fe34d2 vocab=9ae556b7
-/
theorem isUniversalFor_baireOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalSigma0 i) (baireOrdinalUniversalSigma i hic) :=
  isUniversalFor_ordinalUniversalSigma
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Baire multiplicative relation is universal for all subsets in its ordinal class.
@isnad1 id=isuniver.2h1v.s5.38e3d0cdb851 from=translated src=- shape=44fe34d2 vocab=8969de3e
-/
theorem isUniversalFor_baireOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalPi0 i) (baireOrdinalUniversalPi i hic) :=
  isUniversalFor_ordinalUniversalPi
    isTopologicalBasis_range_baireCylinderBasisSequence hic hi0

/-- The Cantor additive relation is universal for all subsets in its ordinal class.
@isnad1 id=isuniver.2h1v.s5.d493cf5754c4 from=translated src=- shape=7db5a71d vocab=fd338e9e
-/
theorem isUniversalFor_cantorOrdinalUniversalSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalSigma0 i) (cantorOrdinalUniversalSigma i hic) :=
  isUniversalFor_ordinalUniversalSigma
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

/-- The Cantor multiplicative relation is universal for all subsets in its ordinal class.
@isnad1 id=isuniver.2h1v.s5.da590c980af7 from=translated src=- shape=7db5a71d vocab=247ee78f
-/
theorem isUniversalFor_cantorOrdinalUniversalPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    IsUniversalFor (OrdinalPi0 i) (cantorOrdinalUniversalPi i hic) :=
  isUniversalFor_ordinalUniversalPi
    isTopologicalBasis_range_cantorCylinderBasisSequence hic hi0

end DescriptiveSetTheory
