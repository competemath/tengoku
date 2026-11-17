/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.TreeNormalForm
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Reductions.Continuous
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Complexity
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Sections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Completeness of ill-founded and well-founded tree codes

Every analytic subset of Baire space is the projected body of a tree on `ℕ × ℕ`. Sending an object
point to its coded witness-section tree is continuous, and the point belongs to the projection
exactly when that section is ill-founded. This gives a continuous reduction to `illFoundedTrees`.
Complementing the same reduction gives the coanalytic dual for `wellFoundedTrees`.

Completeness here quantifies over Baire-space source sets. It introduces no claim about ranks,
boundedness, arbitrary Polish source spaces, or canonical reduction witnesses.
-/

open Set

universe u

namespace DescriptiveSetTheory

/-- A target set is analytic-complete for Baire sources when it is analytic and every analytic
subset of Baire space continuously reduces to it.-/
def IsAnalyticCompleteForBaire {Y : Type u} [TopologicalSpace Y] (t : Set Y) : Prop :=
  MeasureTheory.AnalyticSet t ∧
    ∀ s : Set (ℕ → ℕ), MeasureTheory.AnalyticSet s → ContinuouslyReduces s t

/-- A target set is coanalytic-complete for Baire sources when it is coanalytic and every
coanalytic subset of Baire space continuously reduces to it.-/
def IsCoanalyticCompleteForBaire {Y : Type u} [TopologicalSpace Y] (t : Set Y) : Prop :=
  IsCoanalytic t ∧
    ∀ s : Set (ℕ → ℕ), IsCoanalytic s → ContinuouslyReduces s t

/-- Apply coanalytic completeness for Baire sources without unfolding its conjunction.-/
theorem IsCoanalyticCompleteForBaire.continuouslyReduces
    {Y : Type u} [TopologicalSpace Y] {t : Set Y} {s : Set (ℕ → ℕ)}
    (ht : IsCoanalyticCompleteForBaire t) (hs : IsCoanalytic s) :
    ContinuouslyReduces s t :=
  ht.2 s hs

namespace Tree

/-- A projected Baire tree body reduces to ill-founded codes via its continuous section-tree map.-/
theorem continuouslyReduces_projectedBody_illFoundedTrees
    (T : Descriptive.tree (ℕ × ℕ)) :
    ContinuouslyReduces (projectedBody T) illFoundedTrees := by
  refine continuouslyReduces_of_continuous (sectionTree T)
    (continuous_sectionTree_baire T) fun x => ?_
  rw [mem_illFoundedTrees]
  exact mem_projectedBody_iff_sectionTree_illFounded_baire T x

/-- Every analytic Baire set continuously reduces to the ill-founded tree codes.-/
theorem continuouslyReduces_illFoundedTrees_of_analytic
    {s : Set (ℕ → ℕ)} (hs : MeasureTheory.AnalyticSet s) :
    ContinuouslyReduces s illFoundedTrees := by
  obtain ⟨T, hT⟩ := analyticSet_iff_exists_projectedBody_baire s |>.1 hs
  rw [← hT]
  exact continuouslyReduces_projectedBody_illFoundedTrees T

/-- Every coanalytic Baire set continuously reduces to the well-founded tree codes.-/
theorem continuouslyReduces_wellFoundedTrees_of_isCoanalytic
    {s : Set (ℕ → ℕ)} (hs : IsCoanalytic s) :
    ContinuouslyReduces s wellFoundedTrees := by
  have hcompl : ContinuouslyReduces sᶜ illFoundedTrees :=
    continuouslyReduces_illFoundedTrees_of_analytic hs
  simpa [wellFoundedTrees_eq_compl] using hcompl.compl

/-- Ill-founded tree codes are analytic-complete for Baire-space source sets.-/
theorem illFoundedTrees_complete :
    IsAnalyticCompleteForBaire illFoundedTrees :=
  ⟨analyticSet_illFoundedTrees, fun _ hs =>
    continuouslyReduces_illFoundedTrees_of_analytic hs⟩

end Tree

end DescriptiveSetTheory
