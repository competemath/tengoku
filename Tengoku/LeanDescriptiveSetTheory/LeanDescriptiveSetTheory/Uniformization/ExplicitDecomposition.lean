/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.PartialBorel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable selection from explicit countable graph covers

Suppose a relation is supplied as a countable union of graphs of measurable total functions,
restricted to measurable domains.  Choosing the function with the least applicable index gives a
measurable selector on the exact union domain.  This file proves the first-piece decomposition,
selector measurability, exact uniformization, and graph coding.

The explicit graph-cover data is an essential hypothesis.  No decomposition is extracted from an
abstract pointwise sigma-compact-section assumption, so this is not the full Arsenin--Kunugui
theorem.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- The union of a countable family of native domains.-/
def graphFamilyDomain (s : ℕ → Set X) : Set X :=
  {x | ∃ n, x ∈ s n}

@[simp] theorem mem_graphFamilyDomain {s : ℕ → Set X} {x : X} :
    x ∈ graphFamilyDomain s ↔ ∃ n, x ∈ s n :=
  Iff.rfl

theorem graphFamilyDomain_eq_iUnion (s : ℕ → Set X) :
    graphFamilyDomain s = ⋃ n, s n := by
  ext x
  simp

theorem measurableSet_graphFamilyDomain [MeasurableSpace X]
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) :
    MeasurableSet (graphFamilyDomain s) := by
  rw [graphFamilyDomain_eq_iUnion]
  exact MeasurableSet.iUnion hs

/-- Points first covered at index `n`.-/
def firstGraphDomain (s : ℕ → Set X) (n : ℕ) : Set X :=
  {x | x ∈ s n ∧ ∀ m < n, x ∉ s m}

@[simp] theorem mem_firstGraphDomain {s : ℕ → Set X} {n : ℕ} {x : X} :
    x ∈ firstGraphDomain s n ↔ x ∈ s n ∧ ∀ m < n, x ∉ s m :=
  Iff.rfl

theorem measurableSet_firstGraphDomain [MeasurableSpace X]
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (n : ℕ) :
    MeasurableSet (firstGraphDomain s n) := by
  have hEq : firstGraphDomain s n = s n \ ⋃ m : Fin n, s m := by
    ext x
    constructor
    · rintro ⟨hxn, hmin⟩
      refine ⟨hxn, ?_⟩
      intro hxUnion
      obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hxUnion
      exact hmin m m.isLt hxm
    · rintro ⟨hxn, hmin⟩
      refine ⟨hxn, fun m hm hxm => ?_⟩
      exact hmin (Set.mem_iUnion.mpr ⟨⟨m, hm⟩, hxm⟩)
  rw [hEq]
  exact (hs n).diff (MeasurableSet.iUnion fun m => hs m)

/-- The least index whose domain contains a point of the union domain.-/
noncomputable def firstGraphIndex (s : ℕ → Set X) (x : graphFamilyDomain s) : ℕ := by
  classical
  exact Nat.find x.property

@[simp] theorem firstGraphIndex_mem (s : ℕ → Set X) (x : graphFamilyDomain s) :
    x.1 ∈ s (firstGraphIndex s x) := by
  classical
  exact Nat.find_spec x.property

/-- Distinct least-index pieces are disjoint.-/
theorem disjoint_firstGraphDomain (s : ℕ → Set X) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (firstGraphDomain s m) (firstGraphDomain s n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  by_cases hlt : m < n
  · exact hxn.2 m hlt hxm.1
  · have hlt' : n < m := by omega
    exact hxm.2 n hlt' hxn.1

/-- The relation presented by a countable family of restricted total graphs.-/
def graphFamilyRelation (s : ℕ → Set X) (f : ℕ → X → Y) : Set (X × Y) :=
  ⋃ n, (s n).graphOn (f n)

@[simp] theorem mem_graphFamilyRelation {s : ℕ → Set X} {f : ℕ → X → Y}
    {x : X} {y : Y} :
    (x, y) ∈ graphFamilyRelation s f ↔ ∃ n, x ∈ s n ∧ f n x = y := by
  simp [graphFamilyRelation]

@[simp] theorem relationDomain_graphFamilyRelation (s : ℕ → Set X) (f : ℕ → X → Y) :
    relationDomain (graphFamilyRelation s f) = graphFamilyDomain s := by
  ext x
  simp [relationDomain]

/-- Select from the least applicable graph in an explicit graph family.-/
noncomputable def graphFamilySelector (s : ℕ → Set X) (f : ℕ → X → Y) :
    graphFamilyDomain s → Y := fun x => f (firstGraphIndex s x) x.1

theorem graphFamilySelector_mem (s : ℕ → Set X) (f : ℕ → X → Y)
    (x : graphFamilyDomain s) :
    (x.1, graphFamilySelector s f x) ∈ graphFamilyRelation s f := by
  rw [mem_graphFamilyRelation]
  exact ⟨firstGraphIndex s x, firstGraphIndex_mem s x, rfl⟩

/-- Least-index selection exactly uniformizes the relation supplied by the graph family.-/
theorem uniformizes_partialGraph_graphFamilySelector
    (s : ℕ → Set X) (f : ℕ → X → Y) :
    Uniformizes (graphFamilyRelation s f)
      (partialGraph (graphFamilyDomain s) (graphFamilySelector s f)) := by
  rw [uniformizes_partialGraph_iff]
  exact ⟨(relationDomain_graphFamilyRelation s f).symm, graphFamilySelector_mem s f⟩

theorem measurableSet_graphFamilyRelation
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {s : ℕ → Set X} {f : ℕ → X → Y}
    (hs : ∀ n, MeasurableSet (s n)) (hf : ∀ n, Measurable (f n)) :
    MeasurableSet (graphFamilyRelation s f) := by
  exact MeasurableSet.iUnion fun n => measurableSet_graphOn (hs n) (hf n)

end DescriptiveSetTheory
