/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Regularity.PerfectSet.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The analytic perfect-set dichotomy

This file packages the v1.29 perfect-set theorem as an exact dichotomy.  An analytic set in a
Hausdorff space is countable or contains a closed embedded copy of Cantor space, and the two
alternatives are mutually exclusive.

The exclusivity proof is independent of analyticity: Cantor space is uncountable by a direct
diagonal argument, so the range of any injective Cantor map is uncountable.  Consequently no
countable set can contain that range.  The resulting corollaries use explicit injections and
countability predicates instead of ambiguous cardinal notation.
-/

open Set Topology

universe u

namespace DescriptiveSetTheory

variable {X : Type u}

/-- Cantor space is not countable, proved directly by diagonalizing against an alleged
enumeration.  This statement avoids relying on a global `Uncountable` instance for the product
topology.-/
theorem not_countable_univ_cantor : ¬(univ : Set (ℕ → Bool)).Countable := by
  intro hcount
  rcases hcount.exists_eq_range univ_nonempty with ⟨g, hg⟩
  let diagonal : ℕ → Bool := fun n => !(g n n)
  have hd : diagonal ∈ range g := by rw [← hg]; exact mem_univ _
  rcases hd with ⟨n, hn⟩
  have hcoordinate := congrFun hn n
  cases h : g n n <;> simp [diagonal, h] at hcoordinate

/-- The range of an injective map from Cantor space is uncountable.-/
theorem not_countable_range_of_injective_cantor (e : (ℕ → Bool) → X)
    (he : Function.Injective e) : ¬(range e).Countable := by
  intro hrange
  apply not_countable_univ_cantor
  apply countable_of_injective_of_countable_image he.injOn
  simpa only [image_univ] using hrange

/-- A countable set cannot contain the range of an injective Cantor map.  No analyticity or
topology is needed for this exclusion.-/
theorem _root_.Set.Countable.not_exists_injective_cantor_subset {s : Set X} (hs : s.Countable) :
    ¬∃ e : (ℕ → Bool) → X, Function.Injective e ∧ range e ⊆ s := by
  rintro ⟨e, he, hes⟩
  exact not_countable_range_of_injective_cantor e he (hs.mono hes)

/-- A countable set cannot contain a closed embedded Cantor copy.-/
theorem _root_.Set.Countable.not_exists_isClosedEmbedding_cantor_subset [TopologicalSpace X]
    {s : Set X} (hs : s.Countable) :
    ¬∃ e : (ℕ → Bool) → X, IsClosedEmbedding e ∧ range e ⊆ s := by
  rintro ⟨e, he, hes⟩
  exact hs.not_exists_injective_cantor_subset ⟨e, he.isEmbedding.injective, hes⟩

/-- Analytic perfect-set dichotomy: an analytic subset of a Hausdorff space is countable or
contains a closed embedded Cantor copy.-/
theorem _root_.MeasureTheory.AnalyticSet.countable_or_exists_isClosedEmbedding_cantor
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s) :
    s.Countable ∨
      ∃ e : (ℕ → Bool) → X, IsClosedEmbedding e ∧ range e ⊆ s := by
  classical
  exact if hcount : s.Countable then Or.inl hcount else Or.inr
    (hs.exists_isClosedEmbedding_cantor hcount)

/-- Countability and containing a closed embedded Cantor copy are mutually exclusive.  This
statement is independent of analyticity and separation assumptions.-/
theorem not_countable_and_exists_isClosedEmbedding_cantor
    [TopologicalSpace X] {s : Set X} :
    ¬(s.Countable ∧
      ∃ e : (ℕ → Bool) → X, IsClosedEmbedding e ∧ range e ⊆ s) := by
  rintro ⟨hcount, he⟩
  exact hcount.not_exists_isClosedEmbedding_cantor_subset he

/-- Exact uncountable-side formulation of the dichotomy.-/
theorem _root_.MeasureTheory.AnalyticSet.not_countable_iff_exists_isClosedEmbedding_cantor
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s) :
    ¬s.Countable ↔
      ∃ e : (ℕ → Bool) → X, IsClosedEmbedding e ∧ range e ⊆ s := by
  constructor
  · exact hs.exists_isClosedEmbedding_cantor
  · rintro ⟨e, he, hes⟩ hcount
    exact hcount.not_exists_injective_cantor_subset
      ⟨e, he.isEmbedding.injective, hes⟩

/-- Exact countable-side formulation: an analytic set is countable precisely when it contains no
injective Cantor image.-/
theorem _root_.MeasureTheory.AnalyticSet.countable_iff_not_exists_injective_cantor
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s) :
    s.Countable ↔
      ¬∃ e : (ℕ → Bool) → X, Function.Injective e ∧ range e ⊆ s := by
  constructor
  · exact Set.Countable.not_exists_injective_cantor_subset
  · intro hnone
    by_contra hunc
    rcases hs.exists_continuous_injective_cantor hunc with ⟨e, _, he, hes⟩
    exact hnone ⟨e, he, hes⟩

/-- Every uncountable analytic set contains an uncountable closed subset, namely the range of its
closed embedded Cantor copy.-/
theorem _root_.MeasureTheory.AnalyticSet.exists_uncountable_closed_subset
    [TopologicalSpace X] [T2Space X] {s : Set X} (hs : MeasureTheory.AnalyticSet s)
    (hunc : ¬s.Countable) :
    ∃ C : Set X, C ⊆ s ∧ IsClosed C ∧ ¬C.Countable := by
  rcases hs.exists_isClosedEmbedding_cantor hunc with ⟨e, he, hes⟩
  exact ⟨range e, hes, he.isClosed_range,
    not_countable_range_of_injective_cantor e he.isEmbedding.injective⟩

/-- Baire-space specialization of the analytic dichotomy.-/
theorem analyticSet_countable_or_closedCantor_baire {s : Set (ℕ → ℕ)}
    (hs : MeasureTheory.AnalyticSet s) :
    s.Countable ∨
      ∃ e : (ℕ → Bool) → (ℕ → ℕ), IsClosedEmbedding e ∧ range e ⊆ s :=
  hs.countable_or_exists_isClosedEmbedding_cantor

/-- Cantor-space specialization of the analytic dichotomy.-/
theorem analyticSet_countable_or_closedCantor_cantor {s : Set (ℕ → Bool)}
    (hs : MeasureTheory.AnalyticSet s) :
    s.Countable ∨
      ∃ e : (ℕ → Bool) → (ℕ → Bool), IsClosedEmbedding e ∧ range e ⊆ s :=
  hs.countable_or_exists_isClosedEmbedding_cantor

end DescriptiveSetTheory
