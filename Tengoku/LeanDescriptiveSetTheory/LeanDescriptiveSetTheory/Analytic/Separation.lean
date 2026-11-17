/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.TreeNormalForm
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Code

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel-code separators for analytic sets

This file turns mathlib's Lusin separation theorem into an explicit `BorelCode` witness. The
returned code is an extensional existence witness selected through Borel-code completeness; no
normalization, uniqueness, or executable separator is asserted.

The tree adapter deliberately passes through the stable `v1.1.0` projected-body normal form. It
does not reproduce either the separation proof or the construction of analytic tree witnesses.
-/

open Set

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X]

/-- Disjoint analytic sets have a `BorelCode` whose interpretation contains the first set and is
disjoint from the second.

This is the semantic code-witness bridge from mathlib's `AnalyticSet.measurablySeparable` to
`BorelCode.borelMeasurableSet_iff_exists_code`. The selected code is not canonical.-/
theorem exists_borelCode_separator_of_disjoint_analytic
    [T2Space X] {s t : Set X} (hs : MeasureTheory.AnalyticSet s)
    (ht : MeasureTheory.AnalyticSet t) (hst : Disjoint s t) :
    ∃ c : BorelCode X, s ⊆ c.eval ∧ Disjoint t c.eval := by
  letI : MeasurableSpace X := borel X
  letI : OpensMeasurableSpace X := ⟨le_rfl⟩
  obtain ⟨u, hsu, htu, hu⟩ := hs.measurablySeparable ht hst
  obtain ⟨c, rfl⟩ := BorelCode.borelMeasurableSet_iff_exists_code.1 hu
  exact ⟨c, hsu, htu⟩

namespace Tree

variable {A : Type u}

/-- Disjoint projected bodies have a semantic `BorelCode` separator.

The analytic-set premises are discharged through the `v1.1.0` projected-body normal-form
equivalence, so this theorem is the tree-facing adapter for the generic separator.-/
theorem exists_borelCode_separator_projectedBody
    [TopologicalSpace A] [DiscreteTopology A]
    [PolishSpace (ℕ → A)]
    (S T : Descriptive.tree (A × ℕ))
    (h : Disjoint (projectedBody S) (projectedBody T)) :
    ∃ c : BorelCode (ℕ → A), projectedBody S ⊆ c.eval ∧
      Disjoint (projectedBody T) c.eval := by
  have hS : MeasureTheory.AnalyticSet (projectedBody S) :=
    (analyticSet_iff_exists_projectedBody (projectedBody S)).2 ⟨S, rfl⟩
  have hT : MeasureTheory.AnalyticSet (projectedBody T) :=
    (analyticSet_iff_exists_projectedBody (projectedBody T)).2 ⟨T, rfl⟩
  exact exists_borelCode_separator_of_disjoint_analytic hS hT h

/-- Baire-space projected bodies have a semantic `BorelCode` separator.-/
theorem exists_borelCode_separator_projectedBody_baire
    (S T : Descriptive.tree (ℕ × ℕ))
    (h : Disjoint (projectedBody S) (projectedBody T)) :
    ∃ c : BorelCode (ℕ → ℕ), projectedBody S ⊆ c.eval ∧
      Disjoint (projectedBody T) c.eval :=
  exists_borelCode_separator_projectedBody S T h

end Tree
end DescriptiveSetTheory
