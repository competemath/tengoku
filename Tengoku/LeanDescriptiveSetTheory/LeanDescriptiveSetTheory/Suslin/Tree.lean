/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.TreeNormalForm
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.ClosedScheme

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tree projections as Suslin operations

This file associates a closed Suslin scheme with a tree on a product alphabet. At a finite witness
prefix `s`, the scheme contains exactly the object sequences whose equally long object prefix,
zipped with `s`, is a node of the tree.

Because both sides use `Tree.initialSegment` at length `n`, membership in the Suslin operation is
definitionally aligned with the branch constraints after one pairing lemma. This yields an exact
equality with `Tree.projectedBody` and a closed-scheme representation of Baire analytic sets.
-/

open Set

namespace DescriptiveSetTheory.Tree

variable {A : Type*}

/-- The Suslin scheme associated with a tree on an object alphabet paired with natural witnesses.-/
def suslinScheme (T : Descriptive.tree (A × ℕ)) (s : List ℕ) : Set (ℕ → A) :=
  {x | (initialSegment x s.length).zip s ∈ T}

/-- A projected tree body is exactly the Suslin operation of its associated scheme.-/
theorem projectedBody_eq_suslinOperation (T : Descriptive.tree (A × ℕ)) :
    projectedBody T = suslinOperation (suslinScheme T) := by
  ext x
  simp only [mem_projectedBody, mem_suslinOperation]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n => ?_⟩
    have hn := hy n
    rw [initialSegment_pairSequences] at hn
    simpa [suslinScheme] using hn
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n => ?_⟩
    rw [initialSegment_pairSequences]
    simpa [suslinScheme] using hy n

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

/-- Every set in the scheme associated with a product-alphabet tree is closed.-/
theorem isClosed_suslinScheme (T : Descriptive.tree (A × ℕ)) (s : List ℕ) :
    IsClosed (suslinScheme T s) := by
  rw [show suslinScheme T s =
      (fun x : ℕ → A => fun i : Fin s.length => x i) ⁻¹'
        {f : Fin s.length → A | (List.ofFn f).zip s ∈ T} by
    rfl]
  have hcontinuous : Continuous (fun x : ℕ → A =>
      fun i : Fin s.length => x (i : ℕ)) :=
    continuous_pi fun i => continuous_apply (i : ℕ)
  exact (isClopen_discrete
    {f : Fin s.length → A | (List.ofFn f).zip s ∈ T}).isClosed.preimage
    hcontinuous

end Topology

/-- A Baire-space set is analytic exactly when it is the Suslin operation of a closed scheme.-/
theorem analyticSet_iff_exists_closed_suslinScheme_baire (s : Set (ℕ → ℕ)) :
    MeasureTheory.AnalyticSet s ↔
      ∃ A : List ℕ → Set (ℕ → ℕ),
        (∀ t, IsClosed (A t)) ∧ suslinOperation A = s := by
  constructor
  · intro hs
    rcases (analyticSet_iff_exists_projectedBody_baire s).1 hs with ⟨T, hT⟩
    refine ⟨suslinScheme T, isClosed_suslinScheme T, ?_⟩
    exact (projectedBody_eq_suslinOperation T).symm.trans hT
  · rintro ⟨A, hA, rfl⟩
    exact analyticSet_suslinOperation_of_isClosed A hA

end DescriptiveSetTheory.Tree
