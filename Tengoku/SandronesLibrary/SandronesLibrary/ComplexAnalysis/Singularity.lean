/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.Seed.Analysis.Meromorphic.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Foundations for isolated-singularity classification

The textbook definitions require holomorphy on a deleted disk. `MeromorphicAt` is used only for
the removable-or-finite-pole bridge and never as a synonym for all isolated singularities. -/

open Filter Metric Set Topology
open scoped Topology

namespace SandronesLibrary.ComplexAnalysis

/-- Holomorphy on a deleted disk.

> **Entry**: complex-analysis.singularity.classification-foundation-/
def IsolatedSingularityAtTextbook (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ r > 0, HolomorphicOnTextbook f (ball a r \ {a})

/-- An isolated singularity with a finite punctured limit.

> **Entry**: complex-analysis.singularity.classification-foundation-/
def RemovableSingularityAtTextbook (f : ℂ → ℂ) (a : ℂ) : Prop :=
  IsolatedSingularityAtTextbook f a ∧
    ∃ L : ℂ, Tendsto f (nhdsWithin a {a}ᶜ) (nhds L)

/-- An isolated singularity tending to the cobounded filter.

> **Entry**: complex-analysis.singularity.classification-foundation-/
def PoleAtTextbook (f : ℂ → ℂ) (a : ℂ) : Prop :=
  IsolatedSingularityAtTextbook f a ∧
    Tendsto f (nhdsWithin a {a}ᶜ) (Bornology.cobounded ℂ)

/-- An isolated singularity that is neither removable nor a pole.

> **Entry**: complex-analysis.singularity.classification-foundation-/
def EssentialSingularityAtTextbook (f : ℂ → ℂ) (a : ℂ) : Prop :=
  IsolatedSingularityAtTextbook f a ∧
    ¬ RemovableSingularityAtTextbook f a ∧ ¬ PoleAtTextbook f a

/-- The logical trichotomy of the three textbook singularity predicates.

> **Entry**: complex-analysis.singularity.classification-foundation-/
theorem isolatedSingularity_classification
    {f : ℂ → ℂ} {a : ℂ} (h : IsolatedSingularityAtTextbook f a) :
    RemovableSingularityAtTextbook f a ∨ PoleAtTextbook f a ∨
      EssentialSingularityAtTextbook f a := by
  classical
  by_cases hr : RemovableSingularityAtTextbook f a
  · exact Or.inl hr
  by_cases hp : PoleAtTextbook f a
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ⟨h, hr, hp⟩)

/-- For a meromorphic isolated singularity, removability is equivalent to nonnegative order.

> **Entry**: complex-analysis.singularity.classification-foundation-/
theorem removableSingularityAtTextbook_iff_order_nonneg
    {f : ℂ → ℂ} {a : ℂ} (hiso : IsolatedSingularityAtTextbook f a)
    (hf : MeromorphicAt f a) :
    RemovableSingularityAtTextbook f a ↔ 0 ≤ meromorphicOrderAt f a := by
  rw [RemovableSingularityAtTextbook, and_iff_right hiso]
  exact tendsto_nhds_iff_meromorphicOrderAt_nonneg hf

/-- For a meromorphic isolated singularity, being a pole is equivalent to negative order.

> **Entry**: complex-analysis.singularity.classification-foundation-/
theorem poleAtTextbook_iff_order_neg
    {f : ℂ → ℂ} {a : ℂ} (hiso : IsolatedSingularityAtTextbook f a)
    (hf : MeromorphicAt f a) :
    PoleAtTextbook f a ↔ meromorphicOrderAt f a < 0 := by
  rw [PoleAtTextbook, and_iff_right hiso]
  exact tendsto_cobounded_iff_meromorphicOrderAt_neg hf

/-- A meromorphic germ cannot be an essential singularity.

> **Entry**: complex-analysis.singularity.classification-foundation-/
theorem meromorphicAt_not_essential
    {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) :
    ¬ EssentialSingularityAtTextbook f a := by
  rintro ⟨hiso, hr, hp⟩
  rcases lt_or_ge (meromorphicOrderAt f a) 0 with ho | ho
  · exact hp ((poleAtTextbook_iff_order_neg hiso hf).2 ho)
  · exact hr ((removableSingularityAtTextbook_iff_order_nonneg hiso hf).2 ho)

end SandronesLibrary.ComplexAnalysis
