/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.BorelCharacterization
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Projective.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projective level-one coherence

On a Polish Borel space, the one-based projective core recovers the existing descriptive-set
notions exactly: `ProjectiveSigma 1` is analytic, `ProjectivePi 1` is coanalytic, and
`ProjectiveDelta 1` is Borel measurable.

The nontrivial direction represents a continuous Baire image as the projection of its closed graph.
This proves the bridge from the definitions rather than making either the projective or existing
analytic interfaces aliases of one another.
-/

open Set

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- The first positive projective Sigma level is exactly the analytic sets.-/
theorem projectiveSigma_one_iff_analyticSet {s : Set X} :
    ProjectiveSigma 1 s ↔ MeasureTheory.AnalyticSet s := by
  constructor
  · rw [projectiveSigma_succ]
    rintro ⟨R, hR, rfl⟩
    rw [projectiveProjection_eq_image_snd]
    exact (projectivePi_zero.mp hR).analyticSet.image_of_continuous continuous_snd
  · intro hs
    rw [MeasureTheory.AnalyticSet] at hs
    rcases hs with rfl | ⟨f, hf, rfl⟩
    · rw [projectiveSigma_succ]
      exact ⟨∅, projectivePi_zero.mpr MeasurableSet.empty, by ext; simp⟩
    · let R : Set (ProjectiveWitness × X) := {q | f q.1 = q.2}
      have hR : IsClosed R := isClosed_eq (hf.comp continuous_fst) continuous_snd
      rw [projectiveSigma_succ]
      refine ⟨R, projectivePi_zero.mpr hR.measurableSet, ?_⟩
      ext x
      simp [R, projectiveProjection, eq_comm]

/-- The first positive projective Pi level is exactly the coanalytic sets.-/
theorem projectivePi_one_iff_isCoanalytic {s : Set X} :
    ProjectivePi 1 s ↔ IsCoanalytic s := by
  rw [ProjectivePi, IsCoanalytic, projectiveSigma_one_iff_analyticSet]

/-- The first positive projective Delta level is exactly the Borel measurable sets.-/
theorem projectiveDelta_one_iff_measurableSet {s : Set X} :
    ProjectiveDelta 1 s ↔ MeasurableSet s := by
  rw [ProjectiveDelta, projectiveSigma_one_iff_analyticSet,
    projectivePi_one_iff_isCoanalytic]
  exact measurableSet_iff_analyticSet_and_isCoanalytic.symm

/-- An analytic set belongs to `ProjectiveSigma 1`.-/
theorem _root_.MeasureTheory.AnalyticSet.projectiveSigma_one {s : Set X}
    (hs : MeasureTheory.AnalyticSet s) : ProjectiveSigma 1 s :=
  projectiveSigma_one_iff_analyticSet.mpr hs

/-- A coanalytic set belongs to `ProjectivePi 1`.-/
theorem IsCoanalytic.projectivePi_one {s : Set X} (hs : IsCoanalytic s) :
    ProjectivePi 1 s :=
  projectivePi_one_iff_isCoanalytic.mpr hs

/-- A Borel set belongs to `ProjectiveDelta 1`.-/
theorem _root_.MeasurableSet.projectiveDelta_one {s : Set X} (hs : MeasurableSet s) :
    ProjectiveDelta 1 s :=
  projectiveDelta_one_iff_measurableSet.mpr hs

end DescriptiveSetTheory
