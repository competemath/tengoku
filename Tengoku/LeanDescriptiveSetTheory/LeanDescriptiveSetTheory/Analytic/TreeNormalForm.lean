/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.TreeRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tree normal forms for analytic subsets of sequence spaces

This file completes the tree representation from `TreeRepresentation`. A subset of a sequence
space over a discrete alphabet is analytic exactly when it is the projection of the body of a tree
on the product of the object alphabet with `ℕ`.

The Baire and Cantor statements are exposed separately. In the Cantor statement, only the object
coordinate is Boolean: the witness coordinate remains Baire space, so the tree alphabet is
`Bool × ℕ`.
-/

open Set

universe u

namespace DescriptiveSetTheory.Tree

variable {A : Type u}

/-- Analytic subsets of a discrete-alphabet sequence space are exactly projected tree bodies.-/
theorem analyticSet_iff_exists_projectedBody
    [TopologicalSpace A] [DiscreteTopology A] [PolishSpace (ℕ → A)]
    (s : Set (ℕ → A)) :
    MeasureTheory.AnalyticSet s ↔
      ∃ T : Descriptive.tree (A × ℕ), projectedBody T = s := by
  constructor
  · intro hs
    rw [MeasureTheory.AnalyticSet] at hs
    rcases hs with rfl | ⟨f, hf, rfl⟩
    · exact ⟨⊥, by simp [projectedBody, pairedBody]⟩
    · let graph : Set ((ℕ → A) × (ℕ → ℕ)) := {p | f p.2 = p.1}
      have hgraph : IsClosed graph := isClosed_eq (hf.comp continuous_snd) continuous_fst
      let codedGraph : Set (ℕ → A × ℕ) :=
        (pairSequencesHomeomorph (A := A) (B := ℕ)).symm ⁻¹' graph
      have hcodedGraph : IsClosed codedGraph :=
        hgraph.preimage (pairSequencesHomeomorph (A := A) (B := ℕ)).symm.continuous
      refine ⟨treeOfSet codedGraph, ?_⟩
      ext x
      rw [mem_projectedBody, body_treeOfSet_of_isClosed hcodedGraph]
      simp only [codedGraph, mem_preimage, pairSequencesHomeomorph_symm_apply,
        unpairSequences, graph, mem_ofPred_eq, mem_range]
      constructor
      · rintro ⟨y, hxy⟩
        exact ⟨y, hxy⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, rfl⟩
  · rintro ⟨T, rfl⟩
    exact analyticSet_projectedBody T

/-- Baire-space analytic sets are exactly projections of bodies of trees on `ℕ × ℕ`.-/
theorem analyticSet_iff_exists_projectedBody_baire (s : Set (ℕ → ℕ)) :
    MeasureTheory.AnalyticSet s ↔
      ∃ T : Descriptive.tree (ℕ × ℕ), projectedBody T = s :=
  analyticSet_iff_exists_projectedBody s

/-- Cantor-space analytic sets are exactly projections with a Baire witness coordinate.-/
theorem analyticSet_iff_exists_projectedBody_cantor (s : Set (ℕ → Bool)) :
    MeasureTheory.AnalyticSet s ↔
      ∃ T : Descriptive.tree (Bool × ℕ), projectedBody T = s := by
  letI : MetricSpace (ℕ → Bool) :=
    PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl
  exact analyticSet_iff_exists_projectedBody s

end DescriptiveSetTheory.Tree
