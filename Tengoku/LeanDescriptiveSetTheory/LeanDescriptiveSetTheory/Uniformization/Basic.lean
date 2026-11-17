/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Relations.Sections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Set-theoretic uniformization

This module records the minimal relation-theoretic interface for uniformization.  A uniformizing
relation is a subrelation with the same domain and at most one value over each point.  Thus every
nonempty vertical section is reduced to exactly one point.

The choice construction at the end is deliberately set-theoretic: it proves no measurability,
continuity, Baire measurability, or other definability property of the selected function.
-/

open Set

universe u v w

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- A relation has at most one value above each point of its domain.-/
def RelationSingleValued (G : Set (X × Y)) : Prop :=
  ∀ ⦃x y z⦄, (x, y) ∈ G → (x, z) ∈ G → y = z

/-- `G` uniformizes `R` when it is a single-valued subrelation with exactly the same domain.-/
def Uniformizes (R G : Set (X × Y)) : Prop :=
  G ⊆ R ∧ relationDomain G = relationDomain R ∧ RelationSingleValued G

/-- Restrict a relation to first coordinates in `s`.-/
def relationRestrict (R : Set (X × Y)) (s : Set X) : Set (X × Y) :=
  {p | p ∈ R ∧ p.1 ∈ s}

/-- The graph of a function whose native domain is the subtype `s`.-/
def partialGraph (s : Set X) (f : s → Y) : Set (X × Y) :=
  {p | ∃ hp : p.1 ∈ s, f ⟨p.1, hp⟩ = p.2}

@[simp] theorem mem_relationRestrict {R : Set (X × Y)} {s : Set X} {p : X × Y} :
    p ∈ relationRestrict R s ↔ p ∈ R ∧ p.1 ∈ s :=
  Iff.rfl

@[simp] theorem mem_partialGraph {s : Set X} {f : s → Y} {x : X} {y : Y} :
    (x, y) ∈ partialGraph s f ↔ ∃ hx : x ∈ s, f ⟨x, hx⟩ = y :=
  Iff.rfl

@[simp] theorem relationDomain_relationRestrict (R : Set (X × Y)) (s : Set X) :
    relationDomain (relationRestrict R s) = relationDomain R ∩ s := by
  ext x
  simp only [mem_relationDomain, mem_relationRestrict, mem_inter_iff]
  constructor
  · rintro ⟨y, hxy, hx⟩
    exact ⟨⟨y, hxy⟩, hx⟩
  · rintro ⟨⟨y, hxy⟩, hx⟩
    exact ⟨y, hxy, hx⟩

@[simp] theorem relationDomain_partialGraph (s : Set X) (f : s → Y) :
    relationDomain (partialGraph s f) = s := by
  ext x
  constructor
  · rintro ⟨y, hx, _⟩
    exact hx
  · intro hx
    exact ⟨f ⟨x, hx⟩, hx, rfl⟩

theorem relationSingleValued_partialGraph (s : Set X) (f : s → Y) :
    RelationSingleValued (partialGraph s f) := by
  rintro x y z ⟨hy, hfy⟩ ⟨hz, hfz⟩
  calc
    y = f ⟨x, hy⟩ := hfy.symm
    _ = f ⟨x, hz⟩ := by congr
    _ = z := hfz

/-- A partial graph uniformizes `R` exactly when its native domain is the relation domain and all
selected pairs lie in `R`.-/
theorem uniformizes_partialGraph_iff {R : Set (X × Y)} {s : Set X} {f : s → Y} :
    Uniformizes R (partialGraph s f) ↔
      s = relationDomain R ∧ ∀ x : s, (x.1, f x) ∈ R := by
  constructor
  · intro h
    refine ⟨(relationDomain_partialGraph s f).symm.trans h.2.1, ?_⟩
    intro x
    exact h.1 ⟨x.property, rfl⟩
  · rintro ⟨hs, hf⟩
    refine ⟨?_, ?_, relationSingleValued_partialGraph s f⟩
    · rintro ⟨x, y⟩ ⟨hx, hxy⟩
      simpa [hxy] using hf ⟨x, hx⟩
    · calc
        relationDomain (partialGraph s f) = s := relationDomain_partialGraph s f
        _ = relationDomain R := hs

/-- Uniformization is equivalently exact singleton semantics on every section in the domain and
an empty section outside it.-/
theorem uniformizes_iff_verticalSection {R G : Set (X × Y)} :
    Uniformizes R G ↔
      G ⊆ R ∧ ∀ x, x ∈ relationDomain R ↔ ∃! y, y ∈ verticalSection G x := by
  constructor
  · rintro ⟨hsub, hdom, hfun⟩
    refine ⟨hsub, fun x => ?_⟩
    constructor
    · intro hx
      rw [← hdom] at hx
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, hy, ?_⟩
      intro z hz
      exact hfun hz hy
    · rintro ⟨y, hy, _⟩
      rw [← hdom]
      exact ⟨y, hy⟩
  · rintro ⟨hsub, hsections⟩
    refine ⟨hsub, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, hsub hy⟩
      · intro hx
        obtain ⟨y, hy, _⟩ := (hsections x).mp hx
        exact ⟨y, hy⟩
    · intro x y z hy hz
      obtain ⟨w, hw, huw⟩ := (hsections x).mp ⟨y, hsub hy⟩
      exact (huw y hy).trans (huw z hz).symm

/-- Restricting both relations to the same first-coordinate set preserves uniformization.-/
theorem Uniformizes.restrict {R G : Set (X × Y)} (h : Uniformizes R G) (s : Set X) :
    Uniformizes (relationRestrict R s) (relationRestrict G s) := by
  refine ⟨fun p hp => ⟨h.1 hp.1, hp.2⟩, ?_, ?_⟩
  · simp [h.2.1]
  · intro x y z hy hz
    exact h.2.2 hy.1 hz.1

/-- A composable pair of uniformizers remains a uniformizer.  The range hypothesis is the exact
condition ensuring that the first selected value lies in the second relation's domain.-/
theorem Uniformizes.comp {R G : Set (X × Y)} {S H : Set (Y × Z)}
    (hG : Uniformizes R G) (hH : Uniformizes S H)
    (hrange : relationRange R ⊆ relationDomain S) :
    Uniformizes (relationComp R S) (relationComp G H) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact ⟨y, hG.1 hxy, hH.1 hyz⟩
  · ext x
    constructor
    · rintro ⟨z, y, hxy, hyz⟩
      exact ⟨z, y, hG.1 hxy, hH.1 hyz⟩
    · rintro ⟨z, y, hxy, hyz⟩
      have hxR : x ∈ relationDomain R := ⟨y, hxy⟩
      rw [← hG.2.1] at hxR
      obtain ⟨y', hxy'⟩ := hxR
      have hy'S : y' ∈ relationDomain S := hrange ⟨x, hG.1 hxy'⟩
      rw [← hH.2.1] at hy'S
      obtain ⟨z', hy'z'⟩ := hy'S
      exact ⟨z', y', hxy', hy'z'⟩
  · rintro x z z' ⟨y, hxy, hyz⟩ ⟨y', hxy', hy'z'⟩
    have hyy' := hG.2.2 hxy hxy'
    subst y'
    exact hH.2.2 hyz hy'z'

/-- The selector obtained by classical choice on each nonempty section.-/
noncomputable def choiceSelector (R : Set (X × Y)) : relationDomain R → Y :=
  fun x => Classical.choose x.property

theorem choiceSelector_mem (R : Set (X × Y)) (x : relationDomain R) :
    (x.1, choiceSelector R x) ∈ R :=
  Classical.choose_spec x.property

/-- Every relation has a set-theoretic uniformization.  This theorem intentionally carries no
regularity conclusion about `choiceSelector`.-/
theorem uniformizes_partialGraph_choiceSelector (R : Set (X × Y)) :
    Uniformizes R (partialGraph (relationDomain R) (choiceSelector R)) :=
  uniformizes_partialGraph_iff.mpr ⟨rfl, choiceSelector_mem R⟩

end DescriptiveSetTheory
