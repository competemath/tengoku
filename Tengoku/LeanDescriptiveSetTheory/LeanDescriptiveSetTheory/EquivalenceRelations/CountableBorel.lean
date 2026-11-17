/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.StandardBorel.FiniteFiberLabel
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.CountableSections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Countable Borel equivalence relations

This module keeps equivalence relations as ordinary binary predicates and exposes their graphs and
classes as sets.  Borelness, countable classes, and the equivalence laws remain separate predicates;
`IsCountableBorelEquivalenceRelation` is their conjunction.  The API proves exact section/class
semantics, pointwise class enumeration, restrictions, and pullback along measurable injections.

The equality relation and every equivalence relation on a finite measurable-singleton type are
instances of the predicate.  `eventualEq` is introduced only as an equivalence-relation prototype;
its Borel graph, countable classes, and nonsmoothness are deliberately not asserted here.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- The subset of `X × X` representing a binary relation.-/
def equivalenceRelationGraph (r : X → X → Prop) : Set (X × X) :=
  {p | r p.1 p.2}

/-- The class of `x` for a binary relation.-/
def equivalenceClass (r : X → X → Prop) (x : X) : Set X :=
  {y | r x y}

/-- A relation has a Borel graph in the supplied measurable structure.-/
def IsBorelRelation [MeasurableSpace X] (r : X → X → Prop) : Prop :=
  MeasurableSet (equivalenceRelationGraph r)

/-- Every class of the relation is countable.-/
def HasCountableClasses (r : X → X → Prop) : Prop :=
  ∀ x, (equivalenceClass r x).Countable

/-- Conservative unbundled predicate for a countable Borel equivalence relation.-/
def IsCountableBorelEquivalenceRelation [MeasurableSpace X]
    (r : X → X → Prop) : Prop :=
  Equivalence r ∧ IsBorelRelation r ∧ HasCountableClasses r

@[simp] theorem verticalSection_equivalenceRelationGraph
    (r : X → X → Prop) (x : X) :
    verticalSection (equivalenceRelationGraph r) x = equivalenceClass r x := by
  rfl

theorem HasCountableClasses.hasCountableVerticalSections
    {r : X → X → Prop} (h : HasCountableClasses r) :
    HasCountableVerticalSections (equivalenceRelationGraph r) := by
  intro x
  simpa only [verticalSection_equivalenceRelationGraph] using h x

theorem IsCountableBorelEquivalenceRelation.hasCountableVerticalSections
    [MeasurableSpace X] {r : X → X → Prop}
    (h : IsCountableBorelEquivalenceRelation r) :
    HasCountableVerticalSections (equivalenceRelationGraph r) :=
  h.2.2.hasCountableVerticalSections

theorem IsCountableBorelEquivalenceRelation.hasPointwiseClassEnumeration
    [MeasurableSpace X] {r : X → X → Prop}
    (h : IsCountableBorelEquivalenceRelation r) :
    HasPointwiseSectionEnumeration (equivalenceRelationGraph r) :=
  (hasCountableVerticalSections_iff_hasPointwiseSectionEnumeration _).mp
    h.hasCountableVerticalSections

/-- Restriction of a relation to a subtype.-/
def restrictEquivalenceRelation (r : X → X → Prop) (s : Set X) : s → s → Prop :=
  fun x y => r x.1 y.1

@[simp] theorem equivalenceClass_restrictEquivalenceRelation
    (r : X → X → Prop) (s : Set X) (x : s) :
    equivalenceClass (restrictEquivalenceRelation r s) x =
      ((↑) : s → X) ⁻¹' equivalenceClass r x.1 := by
  rfl

theorem equivalence_restrictEquivalenceRelation
    {r : X → X → Prop} (hr : Equivalence r) (s : Set X) :
    Equivalence (restrictEquivalenceRelation r s) := by
  exact ⟨fun x => hr.refl x, fun h => hr.symm h,
    fun hxy hyz => hr.trans hxy hyz⟩

theorem IsBorelRelation.restrictEquivalenceRelation
    [MeasurableSpace X] {r : X → X → Prop} (hr : IsBorelRelation r) (s : Set X) :
    IsBorelRelation (restrictEquivalenceRelation r s) := by
  exact hr.preimage
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd))

theorem HasCountableClasses.restrictEquivalenceRelation
    {r : X → X → Prop} (hr : HasCountableClasses r) (s : Set X) :
    HasCountableClasses (restrictEquivalenceRelation r s) := by
  intro x
  rw [equivalenceClass_restrictEquivalenceRelation]
  exact (hr x.1).preimage Subtype.coe_injective

theorem IsCountableBorelEquivalenceRelation.restrict
    [MeasurableSpace X] {r : X → X → Prop}
    (hr : IsCountableBorelEquivalenceRelation r) (s : Set X) :
    IsCountableBorelEquivalenceRelation (restrictEquivalenceRelation r s) :=
  ⟨equivalence_restrictEquivalenceRelation hr.1 s,
    hr.2.1.restrictEquivalenceRelation s,
    hr.2.2.restrictEquivalenceRelation s⟩

/-- Pullback of a relation along a map.-/
def pullbackEquivalenceRelation (f : X → Y) (r : Y → Y → Prop) : X → X → Prop :=
  fun x x' => r (f x) (f x')

@[simp] theorem equivalenceClass_pullbackEquivalenceRelation
    (f : X → Y) (r : Y → Y → Prop) (x : X) :
    equivalenceClass (pullbackEquivalenceRelation f r) x =
      f ⁻¹' equivalenceClass r (f x) := by
  rfl

theorem equivalence_pullbackEquivalenceRelation
    (f : X → Y) {r : Y → Y → Prop} (hr : Equivalence r) :
    Equivalence (pullbackEquivalenceRelation f r) := by
  exact ⟨fun x => hr.refl (f x), fun h => hr.symm h,
    fun hxy hyz => hr.trans hxy hyz⟩

theorem IsBorelRelation.pullbackEquivalenceRelation
    [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) {r : Y → Y → Prop} (hr : IsBorelRelation r) :
    IsBorelRelation (pullbackEquivalenceRelation f r) := by
  exact hr.preimage
    ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd))

theorem HasCountableClasses.pullbackEquivalenceRelation
    {f : X → Y} (hf : Function.Injective f)
    {r : Y → Y → Prop} (hr : HasCountableClasses r) :
    HasCountableClasses (pullbackEquivalenceRelation f r) := by
  intro x
  rw [equivalenceClass_pullbackEquivalenceRelation]
  exact (hr (f x)).preimage hf

theorem IsCountableBorelEquivalenceRelation.pullback
    [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) (hinj : Function.Injective f)
    {r : Y → Y → Prop} (hr : IsCountableBorelEquivalenceRelation r) :
    IsCountableBorelEquivalenceRelation (pullbackEquivalenceRelation f r) :=
  ⟨equivalence_pullbackEquivalenceRelation f hr.1,
    hr.2.1.pullbackEquivalenceRelation hf,
    hr.2.2.pullbackEquivalenceRelation hinj⟩

@[simp] theorem equivalenceRelationGraph_eq_diagonal :
    equivalenceRelationGraph (@Eq X) = Set.diagonal X := by
  ext p
  simp [equivalenceRelationGraph]

@[simp] theorem equivalenceClass_eq (x : X) :
    equivalenceClass (@Eq X) x = {x} := by
  ext y
  simp [equivalenceClass]

theorem isCountableBorelEquivalenceRelation_eq
    [MeasurableSpace X] [StandardBorelSpace X] :
    IsCountableBorelEquivalenceRelation (@Eq X) := by
  refine ⟨eq_equivalence, ?_, ?_⟩
  · simpa only [IsBorelRelation, equivalenceRelationGraph_eq_diagonal] using
      (measurableSet_diagonal : MeasurableSet (Set.diagonal X))
  · intro x
    simpa only [equivalenceClass_eq] using Set.countable_singleton x

theorem isCountableBorelEquivalenceRelation_of_finite
    [MeasurableSpace X] [MeasurableSingletonClass X] [Finite X]
    {r : X → X → Prop} (hr : Equivalence r) :
    IsCountableBorelEquivalenceRelation r := by
  refine ⟨hr, Set.toFinite (equivalenceRelationGraph r) |>.measurableSet, ?_⟩
  intro x
  exact (Set.toFinite (equivalenceClass r x)).countable

/-- Eventual equality on Cantor space, introduced here only as an equivalence-relation prototype.-/
def eventualEq (x y : ℕ → Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n → x n = y n

theorem eventualEq_equivalence : Equivalence eventualEq := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨0, fun _ _ => rfl⟩
  · rintro x y ⟨N, hN⟩
    exact ⟨N, fun n hn => (hN n hn).symm⟩
  · rintro x y z ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun n hn => ?_⟩
    exact (hN n ((Nat.le_max_left N M).trans hn)).trans
      (hM n ((Nat.le_max_right N M).trans hn))

end DescriptiveSetTheory
