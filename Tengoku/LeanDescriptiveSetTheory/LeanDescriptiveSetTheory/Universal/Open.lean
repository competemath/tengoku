/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.FiniteHierarchy
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Relations.Sections
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Spaces.Cylinders

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal open sets

Given a natural-number-indexed topological basis b for X, a point p : ℕ → Bool selects the basis
sets for which p n = true. The set universalOpen b contains (p, x) exactly when x belongs to one of
the selected basis sets.

The resulting subset of Cantor space times X is open, all of its vertical sections are open, and
every open subset of X is a section. A canonical noncomputable parameter selects precisely the basis
elements contained in the target open set.

The Baire- and Cantor-space specializations use the explicit cylinder sequences from
Spaces.Cylinders. They provide the first finite-hierarchy universal sets: both universal relations
belong to Sigma0 1.
-/

open Set TopologicalSpace

universe u v

namespace DescriptiveSetTheory

variable {X : Type u}

/-- A relation is universal for a class of subsets when its sections are exactly that class.-/
def IsUniversalFor {P : Type v} (C : Set X → Prop) (U : Set (P × X)) : Prop :=
  ∀ s, C s ↔ ∃ p, verticalSection U p = s

/-- An open relation whose vertical sections are exactly all open subsets of the object space.-/
def IsUniversalOpen {P : Type v} [TopologicalSpace P] [TopologicalSpace X]
    (U : Set (P × X)) : Prop :=
  IsOpen U ∧ IsUniversalFor IsOpen U

/-- Every vertical section of a universal open relation is open.
@isnad1 id=isopen.1h4v.s5.644aefa4179d from=translated src=- shape=3a691ed0 vocab=a82c5a41
-/
theorem IsUniversalOpen.isOpen_verticalSection {P : Type v} [TopologicalSpace P]
    [TopologicalSpace X] {U : Set (P × X)} (hU : IsUniversalOpen U) (p : P) :
    IsOpen (verticalSection U p) :=
  DescriptiveSetTheory.IsOpen.verticalSection hU.1 p

/-- Every open set occurs as a vertical section of a universal open relation.
@isnad1 id=ex.2h4v.s5.5fbe9c646263 from=translated src=- shape=86d10b4b vocab=a82c5a41
-/
theorem IsUniversalOpen.exists_section {P : Type v} [TopologicalSpace P]
    [TopologicalSpace X] {U : Set (P × X)} (hU : IsUniversalOpen U)
    {s : Set X} (hs : IsOpen s) : ∃ p, verticalSection U p = s :=
  (hU.2 s).1 hs

/-- The open relation induced by a natural-number-indexed family of subsets of X.-/
def universalOpen (b : ℕ → Set X) : Set ((ℕ → Bool) × X) :=
  {q | ∃ n, q.1 n = true ∧ q.2 ∈ b n}

/-- Membership in a vertical section of universalOpen unfolds to basis membership.
@isnad1 id=iff.0h4v.s5.8f5b93f99207 from=translated src=- shape=6e4ec235 vocab=c07b5e2a
-/
theorem mem_verticalSection_universalOpen {b : ℕ → Set X} {p : ℕ → Bool} {x : X} :
    x ∈ verticalSection (universalOpen b) p ↔ ∃ n, p n = true ∧ x ∈ b n :=
  Iff.rfl

/-- The universal relation is a countable union of products of parameter cylinders and basis
sets.
@isnad1 id=eq.0h2v.s5.605e5fe22d0e from=translated src=- shape=bb998b20 vocab=59203c00
-/
theorem universalOpen_eq_iUnion (b : ℕ → Set X) :
    universalOpen b = ⋃ n, {p : ℕ → Bool | p n = true} ×ˢ b n := by
  ext q
  simp [universalOpen]

/-- The relation induced by a sequence of open sets is open.
@isnad1 id=isopen.1h2v.s5.718fe6488dfe from=translated src=- shape=0a466a89 vocab=58febb03
-/
theorem isOpen_universalOpen [TopologicalSpace X] {b : ℕ → Set X} (hb : ∀ n, IsOpen (b n)) :
    IsOpen (universalOpen b) := by
  rw [universalOpen_eq_iUnion]
  apply isOpen_iUnion
  intro n
  have hp : IsOpen {p : ℕ → Bool | p n = true} := by
    change IsOpen ((fun p : ℕ → Bool => p n) ⁻¹' {true})
    exact (isOpen_discrete {true}).preimage (continuous_apply n)
  exact hp.prod (hb n)

/-- Every section of the relation induced by open basis sets is open.
@isnad1 id=isopen.1h3v.s5.457bf3732a44 from=translated src=- shape=0a3f7c03 vocab=9e795ce0
-/
theorem isOpen_verticalSection_universalOpen [TopologicalSpace X] {b : ℕ → Set X}
    (hb : ∀ n, IsOpen (b n)) (p : ℕ → Bool) :
    IsOpen (verticalSection (universalOpen b) p) := by
  exact DescriptiveSetTheory.IsOpen.verticalSection (isOpen_universalOpen hb) p

/-- The canonical Cantor-space parameter selecting all basis sets contained in s.-/
noncomputable def universalOpenCode (b : ℕ → Set X) (s : Set X) : ℕ → Bool :=
  by
    classical
    exact fun n => if b n ⊆ s then true else false

/-- A basis index is selected by universalOpenCode exactly when its set is contained in s.
@isnad1 id=iff.0h4v.s4.8ed8298d6925 from=translated src=- shape=82530eda vocab=072d7291
-/
theorem universalOpenCode_apply_iff (b : ℕ → Set X) (s : Set X) (n : ℕ) :
    universalOpenCode b s n = true ↔ b n ⊆ s := by
  classical
  simp [universalOpenCode]

/-- The canonical code of an open set has that set as its vertical section.
@isnad1 id=eq.2h3v.s5.8c899f0831b2 from=translated src=- shape=789cfa70 vocab=ee39af77
-/
theorem verticalSection_universalOpenCode_eq [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {s : Set X} (hs : IsOpen s) :
    verticalSection (universalOpen b) (universalOpenCode b s) = s := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_verticalSection_universalOpen.1 hx
    exact (universalOpenCode_apply_iff b s n).1 hn hxn
  · intro x hx
    obtain ⟨u, hu, hxu, hus⟩ := hb.exists_subset_of_mem_open hx hs
    obtain ⟨n, rfl⟩ := hu
    exact mem_verticalSection_universalOpen.2
      ⟨n, (universalOpenCode_apply_iff b s n).2 hus, hxu⟩

/-- Every natural-number-indexed topological basis produces a universal open relation.
@isnad1 id=isuniver.1h2v.s5.9a88df7b0c6c from=translated src=- shape=73b42b6e vocab=1e4881e9
-/
theorem isUniversalOpen_universalOpen [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) : IsUniversalOpen (universalOpen b) := by
  have hbo : ∀ n, IsOpen (b n) := fun n => hb.isOpen (Set.mem_range_self n)
  refine ⟨isOpen_universalOpen hbo, fun s => ?_⟩
  constructor
  · intro hs
    exact ⟨universalOpenCode b s, verticalSection_universalOpenCode_eq hb hs⟩
  · rintro ⟨p, rfl⟩
    exact isOpen_verticalSection_universalOpen hbo p

/-- A universal open subset of Cantor parameter space times Baire space.-/
def baireUniversalOpen : Set ((ℕ → Bool) × (ℕ → ℕ)) :=
  universalOpen baireCylinderBasisSequence

/-- A universal open subset of Cantor parameter space times Cantor space.-/
def cantorUniversalOpen : Set ((ℕ → Bool) × (ℕ → Bool)) :=
  universalOpen cantorCylinderBasisSequence

/-- baireUniversalOpen is universal for the open subsets of Baire space.
@isnad1 id=isuniver.0h0v.s4.377265d8af2c from=translated src=- shape=9b4c26d4 vocab=3057bc3e
-/
theorem isUniversalOpen_baireUniversalOpen : IsUniversalOpen baireUniversalOpen :=
  isUniversalOpen_universalOpen isTopologicalBasis_range_baireCylinderBasisSequence

/-- cantorUniversalOpen is universal for the open subsets of Cantor space.
@isnad1 id=isuniver.0h0v.s4.a421924cf8ae from=translated src=- shape=eb6111ea vocab=6dd78072
-/
theorem isUniversalOpen_cantorUniversalOpen : IsUniversalOpen cantorUniversalOpen :=
  isUniversalOpen_universalOpen isTopologicalBasis_range_cantorCylinderBasisSequence

/-- The Baire-space universal open relation belongs to the first additive Borel level.
@isnad1 id=sigma0.0h0v.s5.54588a246ef1 from=translated src=- shape=7e7e3679 vocab=c3e2d0f0
-/
theorem sigma0_one_baireUniversalOpen : Sigma0 1 baireUniversalOpen :=
  sigma0_one_of_isOpen isUniversalOpen_baireUniversalOpen.1

/-- The Cantor-space universal open relation belongs to the first additive Borel level.
@isnad1 id=sigma0.0h0v.s5.3421b01b75a3 from=translated src=- shape=28f5f212 vocab=5122fbf5
-/
theorem sigma0_one_cantorUniversalOpen : Sigma0 1 cantorUniversalOpen :=
  sigma0_one_of_isOpen isUniversalOpen_cantorUniversalOpen.1

end DescriptiveSetTheory
