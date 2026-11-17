/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.ExplicitDecomposition
import Tengoku.Seed.Data.Set.Countable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pointwise coding of countable sections

This file separates three notions that must not be conflated:

* every vertical section of a relation is countable;
* an arbitrary pointwise `Option`-valued enumeration has been chosen;
* the graphs cut out by that enumeration are measurable.

Countable sections are equivalent to the existence of a pointwise enumeration by classical choice.
Such an enumeration supplies single-valued candidate graphs and a pairwise-disjoint first-occurrence
decomposition covering the relation exactly.  No measurability follows from that construction.

`HasMeasurableSectionCandidateGraphs` records the extra graph-measurability obligation needed by a
future Lusin--Novikov theorem.  The conditional measurable/code results at the end consume that
obligation; this module deliberately does not manufacture it from pointwise countability.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- Every vertical section of `R` is countable.-/
def HasCountableVerticalSections (R : Set (X × Y)) : Prop :=
  ∀ x, (verticalSection R x).Countable

/-- `e x` enumerates exactly the vertical section of `R` at `x`.  `none` permits empty and finite
sections without choosing a default point of the codomain.  No regularity of `x ↦ e x n` is part of
this predicate.-/
def IsPointwiseSectionEnumeration (R : Set (X × Y))
    (e : X → ℕ → Option Y) : Prop :=
  ∀ x y, (x, y) ∈ R ↔ ∃ n, e x n = some y

/-- A relation admits some pointwise section enumeration.  This is a set-theoretic property, not a
measurable-enumeration predicate.-/
def HasPointwiseSectionEnumeration (R : Set (X × Y)) : Prop :=
  ∃ e : X → ℕ → Option Y, IsPointwiseSectionEnumeration R e

/-- A noncomputable pointwise enumeration obtained by decoding the countable subtype of each
section.  The chosen `Encodable` structures carry no dependence regularity in `x`.-/
noncomputable def pointwiseSectionEnumeration (R : Set (X × Y))
    (hR : HasCountableVerticalSections R) (x : X) (n : ℕ) : Option Y :=
  Option.map Subtype.val
    (@Encodable.decode (verticalSection R x) (hR x).toEncodable n)

theorem pointwiseSectionEnumeration_spec (R : Set (X × Y))
    (hR : HasCountableVerticalSections R) :
    IsPointwiseSectionEnumeration R (pointwiseSectionEnumeration R hR) := by
  intro x y
  constructor
  · intro hxy
    let y' : verticalSection R x := ⟨y, hxy⟩
    refine ⟨@Encodable.encode _ (hR x).toEncodable y', ?_⟩
    simp [pointwiseSectionEnumeration, y']
  · rintro ⟨n, hn⟩
    unfold pointwiseSectionEnumeration at hn
    generalize hdecode : @Encodable.decode (verticalSection R x) (hR x).toEncodable n = o at hn
    cases o with
    | none => simp at hn
    | some y' =>
        simp only [Option.map_some, Option.some.injEq] at hn
        exact hn ▸ y'.property

theorem IsPointwiseSectionEnumeration.hasCountableVerticalSections
    {R : Set (X × Y)} {e : X → ℕ → Option Y}
    (he : IsPointwiseSectionEnumeration R e) : HasCountableVerticalSections R := by
  intro x
  have hEq : verticalSection R x = ⋃ n, {y | e x n = some y} := by
    ext y
    simpa using he x y
  rw [hEq]
  exact Set.countable_iUnion fun n => Set.Subsingleton.countable fun y hy z hz =>
    Option.some.inj (hy.symm.trans hz)

/-- Pointwise enumerability is exactly section countability.  The forward construction is
noncomputable and has no measurable consequence.-/
theorem hasCountableVerticalSections_iff_hasPointwiseSectionEnumeration
    (R : Set (X × Y)) :
    HasCountableVerticalSections R ↔ HasPointwiseSectionEnumeration R := by
  constructor
  · intro hR
    exact ⟨pointwiseSectionEnumeration R hR, pointwiseSectionEnumeration_spec R hR⟩
  · rintro ⟨e, he⟩
    exact he.hasCountableVerticalSections

/-- The candidate graph selected by enumeration index `n`.-/
def sectionCandidateGraph (e : X → ℕ → Option Y) (n : ℕ) : Set (X × Y) :=
  {p | e p.1 n = some p.2}

@[simp] theorem mem_sectionCandidateGraph {e : X → ℕ → Option Y} {n : ℕ}
    {x : X} {y : Y} :
    (x, y) ∈ sectionCandidateGraph e n ↔ e x n = some y :=
  Iff.rfl

/-- Every candidate graph is single-valued, independently of any regularity of the enumeration.-/
theorem relationSingleValued_sectionCandidateGraph (e : X → ℕ → Option Y) (n : ℕ) :
    RelationSingleValued (sectionCandidateGraph e n) := by
  intro x y z hy hz
  exact Option.some.inj (hy.symm.trans hz)

/-- The relation covered by all candidate graphs of an enumeration.-/
def sectionEnumerationRelation (e : X → ℕ → Option Y) : Set (X × Y) :=
  ⋃ n, sectionCandidateGraph e n

@[simp] theorem mem_sectionEnumerationRelation {e : X → ℕ → Option Y}
    {x : X} {y : Y} :
    (x, y) ∈ sectionEnumerationRelation e ↔ ∃ n, e x n = some y := by
  simp [sectionEnumerationRelation]

theorem IsPointwiseSectionEnumeration.sectionEnumerationRelation_eq
    {R : Set (X × Y)} {e : X → ℕ → Option Y}
    (he : IsPointwiseSectionEnumeration R e) :
    sectionEnumerationRelation e = R := by
  ext p
  rcases p with ⟨x, y⟩
  rw [mem_sectionEnumerationRelation]
  exact (he x y).symm

private theorem partialGraph_choiceSelector_eq_of_relationSingleValued
    {G : Set (X × Y)} (hG : RelationSingleValued G) :
    partialGraph (relationDomain G) (choiceSelector G) = G := by
  apply Set.Subset.antisymm (uniformizes_partialGraph_choiceSelector G).1
  rintro ⟨x, y⟩ hxy
  let hx : x ∈ relationDomain G := ⟨y, hxy⟩
  have hchosen : (x, choiceSelector G ⟨x, hx⟩) ∈ G :=
    choiceSelector_mem G ⟨x, hx⟩
  exact ⟨hx, hG hchosen hxy⟩

/-- Each candidate graph is exactly a partial graph on its native relation domain.  The displayed
selector is still a choice selector and has no asserted regularity.-/
theorem sectionCandidateGraph_eq_partialGraph_choiceSelector
    (e : X → ℕ → Option Y) (n : ℕ) :
    sectionCandidateGraph e n =
      partialGraph (relationDomain (sectionCandidateGraph e n))
        (choiceSelector (sectionCandidateGraph e n)) := by
  symm
  exact partialGraph_choiceSelector_eq_of_relationSingleValued
    (relationSingleValued_sectionCandidateGraph e n)

/-- The first-occurrence version of a candidate graph, removing pairs already enumerated at a
smaller index.  Different values over the same source point are retained.-/
def firstSectionCandidateGraph (e : X → ℕ → Option Y) (n : ℕ) : Set (X × Y) :=
  firstGraphDomain (sectionCandidateGraph e) n

@[simp] theorem mem_firstSectionCandidateGraph {e : X → ℕ → Option Y} {n : ℕ}
    {x : X} {y : Y} :
    (x, y) ∈ firstSectionCandidateGraph e n ↔
      e x n = some y ∧ ∀ m < n, e x m ≠ some y :=
  Iff.rfl

/-- Distinct first-occurrence graphs are disjoint as sets of ordered pairs.-/
theorem disjoint_firstSectionCandidateGraph (e : X → ℕ → Option Y)
    {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (firstSectionCandidateGraph e m) (firstSectionCandidateGraph e n) :=
  disjoint_firstGraphDomain (sectionCandidateGraph e) hmn

theorem relationSingleValued_firstSectionCandidateGraph
    (e : X → ℕ → Option Y) (n : ℕ) :
    RelationSingleValued (firstSectionCandidateGraph e n) := by
  intro x y z hy hz
  exact relationSingleValued_sectionCandidateGraph e n hy.1 hz.1

/-- Each first-occurrence graph is also exactly a partial graph.  Again, this set-theoretic choice
representation has no measurable conclusion.-/
theorem firstSectionCandidateGraph_eq_partialGraph_choiceSelector
    (e : X → ℕ → Option Y) (n : ℕ) :
    firstSectionCandidateGraph e n =
      partialGraph (relationDomain (firstSectionCandidateGraph e n))
        (choiceSelector (firstSectionCandidateGraph e n)) := by
  symm
  exact partialGraph_choiceSelector_eq_of_relationSingleValued
    (relationSingleValued_firstSectionCandidateGraph e n)

/-- The additional definability obligation that v1.45 does not derive from pointwise
countability.-/
def HasMeasurableSectionCandidateGraphs
    [MeasurableSpace X] [MeasurableSpace Y]
    (e : X → ℕ → Option Y) : Prop :=
  ∀ n, MeasurableSet (sectionCandidateGraph e n)

/-- A measurable section enumeration consists of exact pointwise coverage plus measurable candidate
graphs.  No existence theorem for this predicate is asserted here.-/
def IsMeasurableSectionEnumeration
    [MeasurableSpace X] [MeasurableSpace Y]
    (R : Set (X × Y)) (e : X → ℕ → Option Y) : Prop :=
  IsPointwiseSectionEnumeration R e ∧ HasMeasurableSectionCandidateGraphs e

theorem measurableSet_firstSectionCandidateGraph
    [MeasurableSpace X] [MeasurableSpace Y]
    {e : X → ℕ → Option Y} (he : HasMeasurableSectionCandidateGraphs e) (n : ℕ) :
    MeasurableSet (firstSectionCandidateGraph e n) :=
  measurableSet_firstGraphDomain he n

/-- Under standard-Borel hypotheses, the explicitly assumed measurable first-occurrence graphs
have exact codes.  This is conditional infrastructure, not Lusin--Novikov existence.-/
theorem exists_standardBorelCode_firstSectionCandidateGraph
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {e : X → ℕ → Option Y} (he : HasMeasurableSectionCandidateGraphs e) (n : ℕ) :
    ∃ c : StandardBorelCode (X × Y), c.eval = firstSectionCandidateGraph e n :=
  StandardBorelCode.exists_code (measurableSet_firstSectionCandidateGraph he n)

end DescriptiveSetTheory
