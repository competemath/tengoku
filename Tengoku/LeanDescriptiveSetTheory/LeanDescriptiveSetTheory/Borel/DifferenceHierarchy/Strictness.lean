/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.DifferenceHierarchy.Universal
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.OrdinalStrictness
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Strictness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strictness of the Hausdorff difference hierarchy

At every positive countable ordinal `i`, universal exact-level relations and diagonalization give
explicit Baire- and Cantor-space sets in `HausdorffDifference (i + 1)` which do not belong to
`HausdorffDifference i`.
-/

open Cardinal Ordinal Set TopologicalSpace

namespace DescriptiveSetTheory

/-- A universal exact difference relation cannot code its Baire diagonal complement.
@isnad1 id=not.1h2v.s5.3049f022ada3 from=translated src=- shape=0d1149df vocab=d4c265c9
-/
theorem IsUniversalFor.not_hausdorffDifference_baireDiagonalComplement
    {i : Ordinal.{0}} {U : Set ((ℕ → ℕ) × (ℕ → ℕ))}
    (hU : IsUniversalFor (HausdorffDifference i) U) :
    ¬ HausdorffDifference i (baireDiagonalComplement U) := by
  intro hdiagonal
  obtain ⟨p, hp⟩ := (hU (baireDiagonalComplement U)).1 hdiagonal
  have hself := Set.ext_iff.mp hp p
  simp only [verticalSection, mem_baireDiagonalComplement, mem_ofPred_eq] at hself
  tauto

/-- The canonical Baire witness separating exact levels `i` and `i + 1`.-/
noncomputable def baireHausdorffDifferenceStrictWitness (i : Ordinal.{0})
    (hi : 0 < i) (hic : IsCountableBorelLevel i) : Set (ℕ → ℕ) :=
  baireDiagonalComplement
    (baireUniversalDifference baireCylinderBasisSequence i hi hic)

/--
@isnad1 id=hausdorf.2h1v.s5.8f9fc314247f from=translated src=- shape=f2d65741 vocab=4529c1ff
-/
theorem hausdorffDifference_add_one_baireStrictWitness {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    HausdorffDifference (i + 1)
      (baireHausdorffDifferenceStrictWitness i hi hic) := by
  have hCompl := (hausdorffDifference_baireUniversalDifference
    (fun n => isTopologicalBasis_range_baireCylinderBasisSequence.isOpen
      (Set.mem_range_self n)) hi hic).compl_add_one
  exact hCompl.preimage continuous_baireDiagonal

/--
@isnad1 id=not.2h1v.s5.99cd2abb4bd8 from=translated src=- shape=474eb5b8 vocab=fa39ccfe
-/
theorem not_hausdorffDifference_baireStrictWitness {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    ¬ HausdorffDifference i (baireHausdorffDifferenceStrictWitness i hi hic) :=
  IsUniversalFor.not_hausdorffDifference_baireDiagonalComplement
    (isUniversalFor_baireUniversalDifference
      isTopologicalBasis_range_baireCylinderBasisSequence hi hic)

/-- Every positive countable Baire-space difference level is properly contained in its
successor.
@isnad1 id=ex.2h1v.s6.0642ee5874d1 from=translated src=- shape=6eaf43f9 vocab=8f01f389
-/
theorem exists_hausdorffDifference_add_one_not_baire {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    ∃ s : Set (ℕ → ℕ), HausdorffDifference (i + 1) s ∧
      ¬ HausdorffDifference i s :=
  ⟨baireHausdorffDifferenceStrictWitness i hi hic,
    hausdorffDifference_add_one_baireStrictWitness hi hic,
    not_hausdorffDifference_baireStrictWitness hi hic⟩

/-- A universal Cantor-parameter exact difference relation cannot code its diagonal complement.
@isnad1 id=not.1h2v.s5.98536dc848fb from=translated src=- shape=1789a01b vocab=e453fdc5
-/
theorem IsUniversalFor.not_hausdorffDifference_diagonalComplement
    {i : Ordinal.{0}} {U : Set ((ℕ → Bool) × (ℕ → Bool))}
    (hU : IsUniversalFor (HausdorffDifference i) U) :
    ¬ HausdorffDifference i (diagonalComplement U) := by
  intro hdiagonal
  obtain ⟨p, hp⟩ := (hU (diagonalComplement U)).1 hdiagonal
  have hself := Set.ext_iff.mp hp p
  simp only [verticalSection, mem_diagonalComplement, mem_ofPred_eq] at hself
  tauto

/-- The canonical Cantor witness separating exact levels `i` and `i + 1`.-/
noncomputable def cantorHausdorffDifferenceStrictWitness (i : Ordinal.{0})
    (hi : 0 < i) (hic : IsCountableBorelLevel i) : Set (ℕ → Bool) :=
  diagonalComplement
    (cantorUniversalDifference cantorCylinderBasisSequence i hi hic)

/--
@isnad1 id=hausdorf.2h1v.s5.856e463817bd from=translated src=- shape=54a0e99e vocab=be60110e
-/
theorem hausdorffDifference_add_one_cantorStrictWitness {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    HausdorffDifference (i + 1)
      (cantorHausdorffDifferenceStrictWitness i hi hic) := by
  have hCompl := (hausdorffDifference_cantorUniversalDifference
    (fun n => isTopologicalBasis_range_cantorCylinderBasisSequence.isOpen
      (Set.mem_range_self n)) hi hic).compl_add_one
  exact hCompl.preimage continuous_cantorDiagonal

/--
@isnad1 id=not.2h1v.s5.26f9324f4eca from=translated src=- shape=dd8030f2 vocab=05c76f5d
-/
theorem not_hausdorffDifference_cantorStrictWitness {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    ¬ HausdorffDifference i (cantorHausdorffDifferenceStrictWitness i hi hic) :=
  IsUniversalFor.not_hausdorffDifference_diagonalComplement
    (isUniversalFor_cantorUniversalDifference
      isTopologicalBasis_range_cantorCylinderBasisSequence hi hic)

/-- Every positive countable Cantor-space difference level is properly contained in its
successor.
@isnad1 id=ex.2h1v.s6.c031c0704ec5 from=translated src=- shape=2c1daa2f vocab=7ff76426
-/
theorem exists_hausdorffDifference_add_one_not_cantor {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    ∃ s : Set (ℕ → Bool), HausdorffDifference (i + 1) s ∧
      ¬ HausdorffDifference i s :=
  ⟨cantorHausdorffDifferenceStrictWitness i hi hic,
    hausdorffDifference_add_one_cantorStrictWitness hi hic,
    not_hausdorffDifference_cantorStrictWitness hi hic⟩

end DescriptiveSetTheory
