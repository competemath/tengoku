/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coanalytic sets

This file provides a small project-namespaced coanalytic interface. A set is coanalytic exactly
when its complement is a mathlib analytic set. The interface includes complement duality,
continuous-preimage closure, and the inclusion of Borel sets; it deliberately introduces no
separate analytic-set definition or general pointclass framework.
-/

open Set

namespace DescriptiveSetTheory

variable {X Y : Type*} [TopologicalSpace X]

/-- A set is coanalytic when its complement is analytic.-/
def IsCoanalytic (s : Set X) : Prop :=
  MeasureTheory.AnalyticSet sᶜ

@[simp]
theorem isCoanalytic_iff_analyticSet_compl {s : Set X} :
    IsCoanalytic s ↔ MeasureTheory.AnalyticSet sᶜ :=
  Iff.rfl

theorem isCoanalytic_compl_iff {s : Set X} :
    IsCoanalytic sᶜ ↔ MeasureTheory.AnalyticSet s := by
  simp [IsCoanalytic]

/-- The complement of an analytic set is coanalytic.-/
theorem MeasureTheory.AnalyticSet.isCoanalytic_compl {s : Set X}
    (hs : MeasureTheory.AnalyticSet s) : IsCoanalytic sᶜ := by
  simpa [IsCoanalytic]

/-- The continuous preimage of a coanalytic set is coanalytic.-/
protected theorem IsCoanalytic.preimage [TopologicalSpace Y] [PolishSpace X] [T2Space Y]
    {s : Set Y} (hs : IsCoanalytic s) {f : X → Y} (hf : Continuous f) :
    IsCoanalytic (f ⁻¹' s) := by
  rw [IsCoanalytic, ← Set.preimage_compl]
  exact MeasureTheory.AnalyticSet.preimage hs hf

/-- Every Borel-measurable subset of a Polish Borel space is coanalytic.-/
theorem _root_.MeasurableSet.isCoanalytic [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Set X} (hs : MeasurableSet s) : IsCoanalytic s := by
  exact hs.compl.analyticSet

end DescriptiveSetTheory
