/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.Coanalytic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Code

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel characterization by analytic and coanalytic sets

This file exposes Suslin's characterization using the project's `IsCoanalytic` vocabulary, then
composes it with Borel-code completeness. The difficult directions are reused directly from
mathlib; the project contributes only the stable vocabulary and code-witness bridge.

Code existence is extensional and classical. It does not provide a normalized, unique, or
executable code.
-/

open Set

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X] [PolishSpace X]
variable [MeasurableSpace X] [BorelSpace X]

/-- In a Polish Borel space, a set is measurable exactly when it is analytic and coanalytic.
@isnad1 id=iff.0h2v.s5.35cb1708b515 from=translated src=- shape=9fb6fa7d vocab=7142e21a
-/
theorem measurableSet_iff_analyticSet_and_isCoanalytic {s : Set X} :
    MeasurableSet s ↔ MeasureTheory.AnalyticSet s ∧ IsCoanalytic s := by
  constructor
  · intro hs
    exact ⟨hs.analyticSet, hs.isCoanalytic⟩
  · rintro ⟨hs, hsc⟩
    exact hs.measurableSet_of_compl (isCoanalytic_iff_analyticSet_compl.1 hsc)

/-- A set has a `BorelCode` exactly when it is both analytic and coanalytic.

The code is selected through Borel-code completeness and has no claimed canonical form.
@isnad1 id=iff.0h2v.s5.f8bc7c4d779f from=translated src=- shape=e03d1021 vocab=fcc6e9a3
-/
theorem exists_borelCode_iff_analyticSet_and_isCoanalytic {s : Set X} :
    (∃ c : BorelCode X, c.eval = s) ↔
      MeasureTheory.AnalyticSet s ∧ IsCoanalytic s := by
  rw [← BorelCode.measurableSet_iff_exists_code]
  exact measurableSet_iff_analyticSet_and_isCoanalytic

end DescriptiveSetTheory
