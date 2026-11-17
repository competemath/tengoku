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

/--
@isnad1 id=iff.0h2v.s4.ab22dc0bd8a4 from=translated src=- shape=8072668f vocab=1220ed3f
-/
@[simp]
theorem isCoanalytic_iff_analyticSet_compl {s : Set X} :
    IsCoanalytic s ↔ MeasureTheory.AnalyticSet sᶜ :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s4.39c96420c1a5 from=translated src=- shape=1052c33f vocab=1220ed3f
-/
theorem isCoanalytic_compl_iff {s : Set X} :
    IsCoanalytic sᶜ ↔ MeasureTheory.AnalyticSet s := by
  simp [IsCoanalytic]

/-- The complement of an analytic set is coanalytic.
@isnad1 id=iscoanal.1h2v.s4.31bf36206aa7 from=translated src=- shape=a00f5de4 vocab=1220ed3f
-/
theorem MeasureTheory.AnalyticSet.isCoanalytic_compl {s : Set X}
    (hs : MeasureTheory.AnalyticSet s) : IsCoanalytic sᶜ := by
  simpa [IsCoanalytic]

/-- The continuous preimage of a coanalytic set is coanalytic.
@isnad1 id=iscoanal.2h4v.s5.1415c5dab75e from=translated src=- shape=742138c2 vocab=eb5e0ef3
-/
protected theorem IsCoanalytic.preimage [TopologicalSpace Y] [PolishSpace X] [T2Space Y]
    {s : Set Y} (hs : IsCoanalytic s) {f : X → Y} (hf : Continuous f) :
    IsCoanalytic (f ⁻¹' s) := by
  rw [IsCoanalytic, ← Set.preimage_compl]
  exact MeasureTheory.AnalyticSet.preimage hs hf

/-- Every Borel-measurable subset of a Polish Borel space is coanalytic.
@isnad1 id=iscoanal.1h2v.s4.97f998565564 from=translated src=- shape=fc688b40 vocab=721f2370
-/
theorem _root_.MeasurableSet.isCoanalytic [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Set X} (hs : MeasurableSet s) : IsCoanalytic s := by
  exact hs.compl.analyticSet

end DescriptiveSetTheory
