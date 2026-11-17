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

/-- Every vertical section of a universal closed relation is closed.
@isnad1 id=isclosed.1h4v.s5.66c7f800390f from=translated src=- shape=3a691ed0 vocab=e7287e45
-/
theorem IsUniversalClosed.isClosed_verticalSection {P : Type v} [TopologicalSpace P]
    [TopologicalSpace X] {F : Set (P × X)} (hF : IsUniversalClosed F) (p : P) :
    IsClosed (verticalSection F p) :=
  DescriptiveSetTheory.IsClosed.verticalSection hF.1 p

/-- Every closed set occurs as a vertical section of a universal closed relation.
@isnad1 id=ex.2h4v.s5.4072af5c71de from=translated src=- shape=86d10b4b vocab=e7287e45
-/
theorem IsUniversalClosed.exists_section {P : Type v} [TopologicalSpace P]
    [TopologicalSpace X] {F : Set (P × X)} (hF : IsUniversalClosed F)
    {s : Set X} (hs : IsClosed s) : ∃ p, verticalSection F p = s :=
  (hF.2 s).1 hs

/-- The closed relation obtained by complementing the open relation induced by `b`.-/
def universalClosed (b : ℕ → Set X) : Set ((ℕ → Bool) × X) :=
  (universalOpen b)ᶜ

/-- The universal closed relation is transparently the complement of the universal open relation.
@isnad1 id=eq.0h2v.s5.ef2021cb0164 from=translated src=- shape=9e6b34e3 vocab=76f4b1e1
-/
theorem universalClosed_eq_compl (b : ℕ → Set X) :
    universalClosed b = (universalOpen b)ᶜ :=
  rfl

/-- Sections of `universalClosed` are complements of the corresponding open sections.
@isnad1 id=eq.0h3v.s5.b233647cf3c4 from=translated src=- shape=8e3fa025 vocab=c9dc8888
-/
@[simp]
theorem verticalSection_universalClosed (b : ℕ → Set X) (p : ℕ → Bool) :
    verticalSection (universalClosed b) p = (verticalSection (universalOpen b) p)ᶜ :=
  rfl

/-- An open basis sequence produces a closed relation after complementation.
@isnad1 id=isclosed.1h2v.s5.55c5abd0ddeb from=translated src=- shape=069bc691 vocab=c9cd8e3d
-/
theorem isClosed_universalClosed [TopologicalSpace X] {b : ℕ → Set X}
    (hb : ∀ n, IsOpen (b n)) : IsClosed (universalClosed b) :=
  (isOpen_universalOpen hb).isClosed_compl

/-- Every section of the complemented basis relation is closed.
@isnad1 id=isclosed.1h3v.s5.0865e8050ca8 from=translated src=- shape=4594f8db vocab=7ce21c6f
-/
theorem isClosed_verticalSection_universalClosed [TopologicalSpace X] {b : ℕ → Set X}
    (hb : ∀ n, IsOpen (b n)) (p : ℕ → Bool) :
    IsClosed (verticalSection (universalClosed b) p) :=
  DescriptiveSetTheory.IsClosed.verticalSection (isClosed_universalClosed hb) p

/-- Reuse the open-set code for the complement of a target closed set.-/
noncomputable def universalClosedCode (b : ℕ → Set X) (s : Set X) : ℕ → Bool :=
  universalOpenCode b sᶜ

/-- The canonical code of a closed set has that set as its vertical section.
@isnad1 id=eq.2h3v.s5.31df0dac65ce from=translated src=- shape=789cfa70 vocab=a1e7dd2d
-/
theorem verticalSection_universalClosedCode_eq [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {s : Set X} (hs : IsClosed s) :
    verticalSection (universalClosed b) (universalClosedCode b s) = s := by
  rw [verticalSection_universalClosed, universalClosedCode,
    verticalSection_universalOpenCode_eq hb hs.isOpen_compl, compl_compl]

/-- Every natural-number-indexed topological basis produces a universal closed relation.
@isnad1 id=isuniver.1h2v.s5.45b35da045c9 from=translated src=- shape=73b42b6e vocab=1969fa7e
-/
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

/-- `baireUniversalClosed` is universal for the closed subsets of Baire space.
@isnad1 id=isuniver.0h0v.s4.225e7bb74f17 from=translated src=- shape=9b4c26d4 vocab=91c7220c
-/
theorem isUniversalClosed_baireUniversalClosed : IsUniversalClosed baireUniversalClosed :=
  isUniversalClosed_universalClosed isTopologicalBasis_range_baireCylinderBasisSequence

/-- `cantorUniversalClosed` is universal for the closed subsets of Cantor space.
@isnad1 id=isuniver.0h0v.s4.5077b2529cca from=translated src=- shape=eb6111ea vocab=4134ef1a
-/
theorem isUniversalClosed_cantorUniversalClosed : IsUniversalClosed cantorUniversalClosed :=
  isUniversalClosed_universalClosed isTopologicalBasis_range_cantorCylinderBasisSequence

/-- The Baire-space universal closed relation belongs to the first multiplicative Borel level.
@isnad1 id=pi0.0h0v.s5.9f413d64c044 from=translated src=- shape=7e7e3679 vocab=7bf39d22
-/
theorem pi0_one_baireUniversalClosed : Pi0 1 baireUniversalClosed :=
  pi0_one_of_isClosed isUniversalClosed_baireUniversalClosed.1

/-- The Cantor-space universal closed relation belongs to the first multiplicative Borel level.
@isnad1 id=pi0.0h0v.s5.a5bad34162eb from=translated src=- shape=28f5f212 vocab=5af3b498
-/
theorem pi0_one_cantorUniversalClosed : Pi0 1 cantorUniversalClosed :=
  pi0_one_of_isClosed isUniversalClosed_cantorUniversalClosed.1

end DescriptiveSetTheory
