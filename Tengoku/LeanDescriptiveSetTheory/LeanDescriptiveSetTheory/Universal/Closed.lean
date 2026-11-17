/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Open

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal closed sets

Complementing the universal open relation induced by a countable basis gives a universal closed
relation with the same Cantor parameter space. Its vertical sections are exactly the closed
subsets of the object space. The construction deliberately reuses the open-set parameter code;
there is no second basis encoding.
-/

open Set TopologicalSpace

universe u v

namespace DescriptiveSetTheory

variable {X : Type u}

/-- A closed relation whose vertical sections are exactly all closed subsets of the object space.-/
def IsUniversalClosed {P : Type v} [TopologicalSpace P] [TopologicalSpace X]
    (F : Set (P × X)) : Prop :=
  IsClosed F ∧ IsUniversalFor IsClosed F

/-- Every vertical section of a universal closed relation is closed.-/
theorem IsUniversalClosed.isClosed_verticalSection {P : Type v} [TopologicalSpace P]
    [TopologicalSpace X] {F : Set (P × X)} (hF : IsUniversalClosed F) (p : P) :
    IsClosed (verticalSection F p) :=
  DescriptiveSetTheory.IsClosed.verticalSection hF.1 p

/-- Every closed set occurs as a vertical section of a universal closed relation.-/
theorem IsUniversalClosed.exists_section {P : Type v} [TopologicalSpace P]
    [TopologicalSpace X] {F : Set (P × X)} (hF : IsUniversalClosed F)
    {s : Set X} (hs : IsClosed s) : ∃ p, verticalSection F p = s :=
  (hF.2 s).1 hs

/-- The closed relation obtained by complementing the open relation induced by `b`.-/
def universalClosed (b : ℕ → Set X) : Set ((ℕ → Bool) × X) :=
  (universalOpen b)ᶜ

/-- The universal closed relation is transparently the complement of the universal open relation.-/
theorem universalClosed_eq_compl (b : ℕ → Set X) :
    universalClosed b = (universalOpen b)ᶜ :=
  rfl

/-- Sections of `universalClosed` are complements of the corresponding open sections.-/
@[simp]
theorem verticalSection_universalClosed (b : ℕ → Set X) (p : ℕ → Bool) :
    verticalSection (universalClosed b) p = (verticalSection (universalOpen b) p)ᶜ :=
  rfl

/-- An open basis sequence produces a closed relation after complementation.-/
theorem isClosed_universalClosed [TopologicalSpace X] {b : ℕ → Set X}
    (hb : ∀ n, IsOpen (b n)) : IsClosed (universalClosed b) :=
  (isOpen_universalOpen hb).isClosed_compl

/-- Every section of the complemented basis relation is closed.-/
theorem isClosed_verticalSection_universalClosed [TopologicalSpace X] {b : ℕ → Set X}
    (hb : ∀ n, IsOpen (b n)) (p : ℕ → Bool) :
    IsClosed (verticalSection (universalClosed b) p) :=
  DescriptiveSetTheory.IsClosed.verticalSection (isClosed_universalClosed hb) p

/-- Reuse the open-set code for the complement of a target closed set.-/
noncomputable def universalClosedCode (b : ℕ → Set X) (s : Set X) : ℕ → Bool :=
  universalOpenCode b sᶜ

/-- The canonical code of a closed set has that set as its vertical section.-/
theorem verticalSection_universalClosedCode_eq [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {s : Set X} (hs : IsClosed s) :
    verticalSection (universalClosed b) (universalClosedCode b s) = s := by
  rw [verticalSection_universalClosed, universalClosedCode,
    verticalSection_universalOpenCode_eq hb hs.isOpen_compl, compl_compl]

/-- Every natural-number-indexed topological basis produces a universal closed relation.-/
theorem isUniversalClosed_universalClosed [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) : IsUniversalClosed (universalClosed b) := by
  have hbo : ∀ n, IsOpen (b n) := fun n => hb.isOpen (Set.mem_range_self n)
  refine ⟨isClosed_universalClosed hbo, fun s => ?_⟩
  constructor
  · intro hs
    exact ⟨universalClosedCode b s, verticalSection_universalClosedCode_eq hb hs⟩
  · rintro ⟨p, rfl⟩
    exact isClosed_verticalSection_universalClosed hbo p

/-- A universal closed subset of Cantor parameter space times Baire space.-/
def baireUniversalClosed : Set ((ℕ → Bool) × (ℕ → ℕ)) :=
  universalClosed baireCylinderBasisSequence

/-- A universal closed subset of Cantor parameter space times Cantor space.-/
def cantorUniversalClosed : Set ((ℕ → Bool) × (ℕ → Bool)) :=
  universalClosed cantorCylinderBasisSequence

/-- `baireUniversalClosed` is universal for the closed subsets of Baire space.-/
theorem isUniversalClosed_baireUniversalClosed : IsUniversalClosed baireUniversalClosed :=
  isUniversalClosed_universalClosed isTopologicalBasis_range_baireCylinderBasisSequence

/-- `cantorUniversalClosed` is universal for the closed subsets of Cantor space.-/
theorem isUniversalClosed_cantorUniversalClosed : IsUniversalClosed cantorUniversalClosed :=
  isUniversalClosed_universalClosed isTopologicalBasis_range_cantorCylinderBasisSequence

/-- The Baire-space universal closed relation belongs to the first multiplicative Borel level.-/
theorem pi0_one_baireUniversalClosed : Pi0 1 baireUniversalClosed :=
  pi0_one_of_isClosed isUniversalClosed_baireUniversalClosed.1

/-- The Cantor-space universal closed relation belongs to the first multiplicative Borel level.-/
theorem pi0_one_cantorUniversalClosed : Pi0 1 cantorUniversalClosed :=
  pi0_one_of_isClosed isUniversalClosed_cantorUniversalClosed.1

end DescriptiveSetTheory
