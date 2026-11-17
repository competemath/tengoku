/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.TreeRepresentation
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.CodeSpace
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.WellFounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parameterized section trees

Fix a tree on an object alphabet paired with a natural-number witness alphabet. At an object point
`x`, the section tree contains a finite witness string `s` exactly when the equally long prefix of
`x`, zipped with `s`, is a node of the product tree.

The output is a `TreeCode`, so the section construction has a genuine topology. Its branches are
exactly the witnesses through the original product tree, projected-body membership is exactly
ill-foundedness of the decoded section, and the code-valued map is continuous for every discrete
object alphabet. Concrete Baire- and Cantor-object specializations are supplied below.
-/

open Set

universe u

namespace DescriptiveSetTheory.Tree

variable {A : Type u}

/-- Appending one witness symbol appends the paired next coordinate to the zipped object prefix.
@isnad1 id=eq.0h4v.s6.761c8839e052 from=translated src=- shape=6cc79160 vocab=b012b0d9
-/
theorem zip_initialSegment_append_singleton (x : ℕ → A) (s : List ℕ) (a : ℕ) :
    (initialSegment x (s ++ [a]).length).zip (s ++ [a]) =
      (initialSegment x s.length).zip s ++ [(x s.length, a)] := by
  rw [List.length_append, List.length_singleton, initialSegment_succ]
  rw [List.zip_append (length_initialSegment x s.length)]
  simp

/-- The witness-coordinate section of a product tree at a fixed object point, as a valid code.-/
noncomputable def sectionTree (T : Descriptive.tree (A × ℕ)) (x : ℕ → A) :
    TreeCode := by
  classical
  refine ⟨fun s => decide ((initialSegment x s.length).zip s ∈ T), ?_⟩
  intro s a hs
  simp only [decide_eq_true_eq] at hs ⊢
  rw [zip_initialSegment_append_singleton] at hs
  exact Descriptive.Tree.mem_of_append hs

/--
@isnad1 id=iff.0h4v.s8.35af20d37c3e from=translated src=- shape=43b58124 vocab=5595b87c
-/
@[simp]
theorem sectionTree_apply_eq_true (T : Descriptive.tree (A × ℕ)) (x : ℕ → A)
    (s : List ℕ) :
    (sectionTree T x).1 s = true ↔ (initialSegment x s.length).zip s ∈ T := by
  classical
  simp [sectionTree]

/-- Branches through the decoded section are exactly paired branches through the product tree.
@isnad1 id=iff.0h4v.s7.4decd252f4de from=translated src=- shape=03a4005e vocab=bcbf1b0a
-/
theorem isBranch_decodeTree_sectionTree_iff (T : Descriptive.tree (A × ℕ))
    (x : ℕ → A) (y : ℕ → ℕ) :
    IsBranch (decodeTree (sectionTree T x)) y ↔
      IsBranch T (pairSequences (x, y)) := by
  simp only [IsBranch, mem_decodeTree, sectionTree_apply_eq_true,
    length_initialSegment, initialSegment_pairSequences]

/-- The body of the decoded section consists exactly of witnesses paired with the object point.
@isnad1 id=iff.0h4v.s7.2e08fc02e562 from=translated src=- shape=27c269d0 vocab=51ea3ccc
-/
theorem mem_body_decodeTree_sectionTree_iff (T : Descriptive.tree (A × ℕ))
    (x : ℕ → A) (y : ℕ → ℕ) :
    y ∈ body (decodeTree (sectionTree T x)) ↔
      pairSequences (x, y) ∈ body T :=
  isBranch_decodeTree_sectionTree_iff T x y

/-- Projected-body membership is the existence of a branch through the decoded section tree.
@isnad1 id=iff.0h3v.s7.547ba206f751 from=translated src=- shape=ee6a7681 vocab=f9336a8e
-/
theorem mem_projectedBody_iff_exists_branch_sectionTree
    (T : Descriptive.tree (A × ℕ)) (x : ℕ → A) :
    x ∈ projectedBody T ↔
      ∃ y : ℕ → ℕ, y ∈ body (decodeTree (sectionTree T x)) := by
  rw [mem_projectedBody]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (mem_body_decodeTree_sectionTree_iff T x y).2 hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (mem_body_decodeTree_sectionTree_iff T x y).1 hy⟩

/-- An object belongs to the projected body exactly when its decoded section is ill-founded.
@isnad1 id=iff.0h3v.s7.45e60cc7a77f from=translated src=- shape=cfeefd7a vocab=39cf4380
-/
theorem mem_projectedBody_iff_sectionTree_illFounded
    (T : Descriptive.tree (A × ℕ)) (x : ℕ → A) :
    x ∈ projectedBody T ↔
      ¬ IsWellFounded (decodeTree (sectionTree T x)) := by
  rw [mem_projectedBody_iff_exists_branch_sectionTree,
    isWellFounded_iff_body_eq_empty]
  exact Set.nonempty_iff_ne_empty

/-- The coded section tree depends continuously on the object point over a discrete alphabet.
@isnad1 id=continuo.0h2v.s7.5e0c33f33087 from=translated src=- shape=89627935 vocab=594ff5ad
-/
theorem continuous_sectionTree [TopologicalSpace A] [DiscreteTopology A]
    (T : Descriptive.tree (A × ℕ)) : Continuous (sectionTree T) := by
  classical
  apply Continuous.subtype_mk
  exact continuous_pi fun s => by
    have hprefix : Continuous (fun x : ℕ → A =>
        fun i : Fin s.length => x (i : ℕ)) :=
      continuous_pi fun i => continuous_apply (i : ℕ)
    have htest : Continuous (fun f : Fin s.length → A =>
        decide ((List.ofFn f).zip s ∈ T)) :=
      continuous_of_discreteTopology
    convert htest.comp hprefix using 1
    funext x
    rfl

/-- Baire-object specialization of the section-tree continuity theorem.
@isnad1 id=continuo.0h1v.s7.c069e86f9b8f from=translated src=- shape=fef7b39d vocab=dbb8d3ac
-/
theorem continuous_sectionTree_baire (T : Descriptive.tree (ℕ × ℕ)) :
    Continuous (sectionTree T) :=
  continuous_sectionTree T

/-- Baire-object specialization of projected-body/ill-foundedness equivalence.
@isnad1 id=iff.0h2v.s7.7f72f2c76ff5 from=translated src=- shape=fd87dd6e vocab=39cf4380
-/
theorem mem_projectedBody_iff_sectionTree_illFounded_baire
    (T : Descriptive.tree (ℕ × ℕ)) (x : ℕ → ℕ) :
    x ∈ projectedBody T ↔
      ¬ IsWellFounded (decodeTree (sectionTree T x)) :=
  mem_projectedBody_iff_sectionTree_illFounded T x

end DescriptiveSetTheory.Tree
