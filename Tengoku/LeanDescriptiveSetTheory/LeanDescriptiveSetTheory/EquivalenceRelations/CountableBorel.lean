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

/--
@isnad1 id=eq.0h3v.s4.1d007481807b from=translated src=- shape=5b7d92f2 vocab=fb40374d
-/
@[simp] theorem verticalSection_equivalenceRelationGraph
    (r : X → X → Prop) (x : X) :
    verticalSection (equivalenceRelationGraph r) x = equivalenceClass r x := by
  rfl

/--
@isnad1 id=hascount.1h2v.s4.92203f908583 from=translated src=- shape=99d1b266 vocab=a35424b5
-/
theorem HasCountableClasses.hasCountableVerticalSections
    {r : X → X → Prop} (h : HasCountableClasses r) :
    HasCountableVerticalSections (equivalenceRelationGraph r) := by
  intro x
  simpa only [verticalSection_equivalenceRelationGraph] using h x

/--
@isnad1 id=hascount.1h2v.s4.eab3a06e35cc from=translated src=- shape=e7c1227d vocab=07fd98f8
-/
theorem IsCountableBorelEquivalenceRelation.hasCountableVerticalSections
    [MeasurableSpace X] {r : X → X → Prop}
    (h : IsCountableBorelEquivalenceRelation r) :
    HasCountableVerticalSections (equivalenceRelationGraph r) :=
  h.2.2.hasCountableVerticalSections

/--
@isnad1 id=haspoint.1h2v.s4.8e45937b5db1 from=translated src=- shape=e7c1227d vocab=9de40822
-/
theorem IsCountableBorelEquivalenceRelation.hasPointwiseClassEnumeration
    [MeasurableSpace X] {r : X → X → Prop}
    (h : IsCountableBorelEquivalenceRelation r) :
    HasPointwiseSectionEnumeration (equivalenceRelationGraph r) :=
  (hasCountableVerticalSections_iff_hasPointwiseSectionEnumeration _).mp
    h.hasCountableVerticalSections

/-- Restriction of a relation to a subtype.-/
def restrictEquivalenceRelation (r : X → X → Prop) (s : Set X) : s → s → Prop :=
  fun x y => r x.1 y.1

/--
@isnad1 id=eq.0h4v.s6.eb936f1d00df from=translated src=- shape=7baa1d25 vocab=c5cf05e4
-/
@[simp] theorem equivalenceClass_restrictEquivalenceRelation
    (r : X → X → Prop) (s : Set X) (x : s) :
    equivalenceClass (restrictEquivalenceRelation r s) x =
      ((↑) : s → X) ⁻¹' equivalenceClass r x.1 := by
  rfl

/--
@isnad1 id=equivale.1h3v.s4.b18d9bf10e54 from=translated src=- shape=a2747fa5 vocab=e04857ed
-/
theorem equivalence_restrictEquivalenceRelation
    {r : X → X → Prop} (hr : Equivalence r) (s : Set X) :
    Equivalence (restrictEquivalenceRelation r s) := by
  exact ⟨fun x => hr.refl x, fun h => hr.symm h,
    fun hxy hyz => hr.trans hxy hyz⟩

/--
@isnad1 id=isborelr.1h3v.s5.78728e477174 from=translated src=- shape=27acce0b vocab=ae9946fe
-/
theorem IsBorelRelation.restrictEquivalenceRelation
    [MeasurableSpace X] {r : X → X → Prop} (hr : IsBorelRelation r) (s : Set X) :
    IsBorelRelation (restrictEquivalenceRelation r s) := by
  exact hr.preimage
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd))

/--
@isnad1 id=hascount.1h3v.s4.b57bebb71cd2 from=translated src=- shape=a2747fa5 vocab=9bff7dff
-/
theorem HasCountableClasses.restrictEquivalenceRelation
    {r : X → X → Prop} (hr : HasCountableClasses r) (s : Set X) :
    HasCountableClasses (restrictEquivalenceRelation r s) := by
  intro x
  rw [equivalenceClass_restrictEquivalenceRelation]
  exact (hr x.1).preimage Subtype.coe_injective

/--
@isnad1 id=iscounta.1h3v.s5.2555e46fdb4d from=translated src=- shape=27acce0b vocab=c9d08b0f
-/
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

/--
@isnad1 id=eq.0h5v.s5.528fae58d0bb from=translated src=- shape=6590cb14 vocab=793f928b
-/
@[simp] theorem equivalenceClass_pullbackEquivalenceRelation
    (f : X → Y) (r : Y → Y → Prop) (x : X) :
    equivalenceClass (pullbackEquivalenceRelation f r) x =
      f ⁻¹' equivalenceClass r (f x) := by
  rfl

/--
@isnad1 id=equivale.1h4v.s4.e5ebcd985fd5 from=translated src=- shape=cb79e560 vocab=0d1fc0e1
-/
theorem equivalence_pullbackEquivalenceRelation
    (f : X → Y) {r : Y → Y → Prop} (hr : Equivalence r) :
    Equivalence (pullbackEquivalenceRelation f r) := by
  exact ⟨fun x => hr.refl (f x), fun h => hr.symm h,
    fun hxy hyz => hr.trans hxy hyz⟩

/--
@isnad1 id=isborelr.2h4v.s5.b984b446201a from=translated src=- shape=26d1180d vocab=556b04aa
-/
theorem IsBorelRelation.pullbackEquivalenceRelation
    [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) {r : Y → Y → Prop} (hr : IsBorelRelation r) :
    IsBorelRelation (pullbackEquivalenceRelation f r) := by
  exact hr.preimage
    ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd))

/--
@isnad1 id=hascount.2h4v.s4.5de70840b6a7 from=translated src=- shape=32669c73 vocab=a6f472d0
-/
theorem HasCountableClasses.pullbackEquivalenceRelation
    {f : X → Y} (hf : Function.Injective f)
    {r : Y → Y → Prop} (hr : HasCountableClasses r) :
    HasCountableClasses (pullbackEquivalenceRelation f r) := by
  intro x
  rw [equivalenceClass_pullbackEquivalenceRelation]
  exact (hr (f x)).preimage hf

/--
@isnad1 id=iscounta.3h4v.s5.cc4002e7da6e from=translated src=- shape=890e15da vocab=7e4ea6d9
-/
theorem IsCountableBorelEquivalenceRelation.pullback
    [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) (hinj : Function.Injective f)
    {r : Y → Y → Prop} (hr : IsCountableBorelEquivalenceRelation r) :
    IsCountableBorelEquivalenceRelation (pullbackEquivalenceRelation f r) :=
  ⟨equivalence_pullbackEquivalenceRelation f hr.1,
    hr.2.1.pullbackEquivalenceRelation hf,
    hr.2.2.pullbackEquivalenceRelation hinj⟩

/--
@isnad1 id=eq.0h1v.s3.c49579d416bc from=translated src=- shape=b5a80988 vocab=5e489b83
-/
@[simp] theorem equivalenceRelationGraph_eq_diagonal :
    equivalenceRelationGraph (@Eq X) = Set.diagonal X := by
  ext p
  simp [equivalenceRelationGraph]

/--
@isnad1 id=eq.0h2v.s4.ee87c32a2973 from=translated src=- shape=851ccb80 vocab=016e1670
-/
@[simp] theorem equivalenceClass_eq (x : X) :
    equivalenceClass (@Eq X) x = {x} := by
  ext y
  simp [equivalenceClass]

/--
@isnad1 id=iscounta.0h1v.s3.6dac2d1e35bc from=translated src=- shape=4c9b52a8 vocab=da9e651b
-/
theorem isCountableBorelEquivalenceRelation_eq
    [MeasurableSpace X] [StandardBorelSpace X] :
    IsCountableBorelEquivalenceRelation (@Eq X) := by
  refine ⟨eq_equivalence, ?_, ?_⟩
  · simpa only [IsBorelRelation, equivalenceRelationGraph_eq_diagonal] using
      (measurableSet_diagonal : MeasurableSet (Set.diagonal X))
  · intro x
    simpa only [equivalenceClass_eq] using Set.countable_singleton x

/--
@isnad1 id=iscounta.1h2v.s4.3bd9285a1bed from=translated src=- shape=b3981c83 vocab=1a23d92d
-/
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

/--
@isnad1 id=equivale.0h0v.s2.c88efab9dbc6 from=translated src=- shape=67086572 vocab=b3f1c5f5
-/
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
