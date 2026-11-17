/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Ranks.Coanalytic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Ranks.CoanalyticNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete consumers of the abstract coanalytic-rank interface

The well-founded-tree rank and every explicit Baire-space presentation released in v1.20 satisfy
`CoanalyticRank`. The tree instance reuses the concrete comparison and boundedness theorems; the
presentation instance reuses their continuous pullback. A bridge identifies the generic realized
stage with the recursive tree stage from v1.17.
-/

open Cardinal Ordinal Set

namespace DescriptiveSetTheory

open Tree

/-- The well-founded-tree rank as an abstract enriched coanalytic rank.-/
noncomputable def wellFoundedTreeRank : CoanalyticRank TreeCode wellFoundedTrees where
  rank T hT := Tree.rank (decodeTree T) hT
  leAnalytic := treeRankLeAnalytic
  leCoanalytic := treeRankLeCoanalytic
  ltAnalytic := treeRankLtAnalytic
  ltCoanalytic := treeRankLtCoanalytic
  isCoanalytic_domain := isCoanalytic_wellFoundedTrees
  analyticSet_leAnalytic := analyticSet_treeRankLeAnalytic
  isCoanalytic_leCoanalytic := isCoanalytic_treeRankLeCoanalytic
  analyticSet_ltAnalytic := analyticSet_treeRankLtAnalytic
  isCoanalytic_ltCoanalytic := isCoanalytic_treeRankLtCoanalytic
  mem_leAnalytic_iff := fun hy => mem_treeRankLeAnalytic_iff_of_isWellFounded hy
  mem_leCoanalytic_iff := fun hy => mem_treeRankLeCoanalytic_iff_of_isWellFounded hy
  mem_ltAnalytic_iff := fun hy => mem_treeRankLtAnalytic_iff_of_isWellFounded hy
  mem_ltCoanalytic_iff := fun hy => mem_treeRankLtCoanalytic_iff_of_isWellFounded hy
  rank_lt_omega_one := fun T hT => treeRank_lt_omega_one (decodeTree T) hT
  boundedOn_analytic := by
    intro B hB hBWF
    obtain ⟨ξ, hξ, hbound⟩ :=
      rank_bounded_of_analytic_subset_wellFounded hB hBWF
    exact ⟨ξ, hξ, fun T hT => hbound T hT (hBWF hT)⟩

/-- The generic realized stage for the tree rank is exactly the recursive strict rank stage.-/
theorem wellFoundedTreeRank_stageAt (T : TreeCode) (hT : T ∈ wellFoundedTrees) :
    wellFoundedTreeRank.stageAt T hT = treeRankLT (Tree.rank (decodeTree T) hT) := by
  rw [wellFoundedTreeRank.stageAt_eq_ltAnalytic_section]
  exact (treeRankLT_eq_treeRankLtAnalytic_section T hT).symm

namespace CoanalyticRankPresentation

variable {A : Set (ℕ → ℕ)} (P : CoanalyticRankPresentation A)

/-- An explicit Baire-space rank presentation as an abstract enriched coanalytic rank.-/
noncomputable def toCoanalyticRank : CoanalyticRank (ℕ → ℕ) A where
  rank := P.rank
  leAnalytic := P.leAnalytic
  leCoanalytic := P.leCoanalytic
  ltAnalytic := P.ltAnalytic
  ltCoanalytic := P.ltCoanalytic
  isCoanalytic_domain := by
    rw [← P.domain_eq]
    exact isCoanalytic_wellFoundedTrees.preimage P.continuous_treeCode
  analyticSet_leAnalytic := P.analyticSet_leAnalytic
  isCoanalytic_leCoanalytic := P.isCoanalytic_leCoanalytic
  analyticSet_ltAnalytic := P.analyticSet_ltAnalytic
  isCoanalytic_ltCoanalytic := P.isCoanalytic_ltCoanalytic
  mem_leAnalytic_iff := fun hy => P.mem_leAnalytic_iff hy
  mem_leCoanalytic_iff := fun hy => P.mem_leCoanalytic_iff hy
  mem_ltAnalytic_iff := fun hy => P.mem_ltAnalytic_iff hy
  mem_ltCoanalytic_iff := fun hy => P.mem_ltCoanalytic_iff hy
  rank_lt_omega_one := P.rank_lt_omega_one
  boundedOn_analytic := fun hB hBA => P.bounded_of_analytic hB hBA

/-- The abstract rank value agrees exactly with the v1.20 presentation value.-/
@[simp] theorem toCoanalyticRank_rank (x : ℕ → ℕ) (hx : x ∈ A) :
    P.toCoanalyticRank.rank x hx = P.rank x hx := rfl

end CoanalyticRankPresentation

end DescriptiveSetTheory
