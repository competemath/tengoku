/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Completeness
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.RankComparison
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.AnalyticStrictness
import Tengoku.Seed.SetTheory.Cardinal.Aleph
import Tengoku.Seed.SetTheory.Cardinal.Regular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundedness for analytic families of well-founded trees

The analytic downward closure of a family `A` consists of every tree whose rank is at most the
rank of some member of `A`. If `A` is analytic and contained in `wellFoundedTrees`, this downward
closure is analytic and still contained in `wellFoundedTrees`. It cannot equal all well-founded
trees, because that set is not analytic. A well-founded code outside the closure therefore supplies
a strict uniform bound.

The resulting ordinal is genuinely below `ω₁`. This file proves that accessibility ranks of
natural-number trees are countable and does not replace that conclusion by a cardinal-sized or
universe-level supremum. Baire-coded and countable-family forms are provided as direct consumers.
-/

open Cardinal Ordinal Set

namespace DescriptiveSetTheory.Tree

/-- The rank-downward closure of a family, using the analytic comparison polarity.-/
def treeRankDownwardClosure (A : Set TreeCode) : Set TreeCode :=
  {S | ∃ T ∈ A, (S, T) ∈ treeRankLeAnalytic}

private theorem analyticSet_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {s t : Set X} (hs : MeasureTheory.AnalyticSet s) (ht : MeasureTheory.AnalyticSet t) :
    MeasureTheory.AnalyticSet (s ∩ t) := by
  rw [show s ∩ t = ⋂ b : Bool, if b then s else t by
    ext x
    simp [and_comm]]
  exact MeasureTheory.AnalyticSet.iInter fun b => by
    cases b <;> simp_all

/-- The rank-downward closure of an analytic family is analytic.-/
theorem analyticSet_treeRankDownwardClosure {A : Set TreeCode}
    (hA : MeasureTheory.AnalyticSet A) :
    MeasureTheory.AnalyticSet (treeRankDownwardClosure A) := by
  rw [show treeRankDownwardClosure A =
      Prod.fst ''
        ({p : TreeCode × TreeCode | p.2 ∈ A} ∩ treeRankLeAnalytic) by
    ext S
    constructor
    · rintro ⟨T, hT, hST⟩
      exact ⟨(S, T), ⟨hT, hST⟩, rfl⟩
    · rintro ⟨⟨S', T⟩, ⟨hT, hST⟩, hS⟩
      change S' = S at hS
      subst S'
      exact ⟨T, hT, hST⟩]
  exact (analyticSet_inter (hA.preimage continuous_snd)
    analyticSet_treeRankLeAnalytic).image_of_continuous continuous_fst

/-- If a family consists of well-founded trees, then so does its rank-downward closure.-/
theorem treeRankDownwardClosure_subset_wellFoundedTrees {A : Set TreeCode}
    (hA : A ⊆ wellFoundedTrees) :
    treeRankDownwardClosure A ⊆ wellFoundedTrees := by
  rintro S ⟨T, hT, hST⟩
  have hTwf : IsWellFounded (decodeTree T) := hA hT
  exact (mem_treeRankLeAnalytic_iff_of_isWellFounded hTwf).1 hST |>.choose

/-- The coanalytic-complete set of well-founded tree codes is not analytic.-/
theorem not_analyticSet_wellFoundedTrees :
    ¬MeasureTheory.AnalyticSet wellFoundedTrees := by
  intro hWF
  obtain ⟨f, hf, hpre⟩ :=
    continuouslyReduces_wellFoundedTrees_of_isCoanalytic
      isCoanalytic_baireCoanalyticNotAnalytic
  apply not_analyticSet_baireCoanalyticNotAnalytic
  rw [← hpre]
  exact hWF.preimage hf

private theorem accRank_lt_omega_one {T : Descriptive.tree ℕ} {s : T}
    (h : Acc (Child T) s) : h.rank < (ω₁ : Ordinal.{0}) := by
  induction h with
  | intro s hbelow ih =>
      rw [Acc.rank_eq]
      apply Ordinal.iSup_lt_omega_one
      intro child
      exact (isSuccLimit_omega 1).succ_lt (ih child.1 child.2)

/-- Every node rank of a well-founded natural-number tree is a countable ordinal.-/
theorem nodeRank_lt_omega_one {T : Descriptive.tree ℕ} (hT : IsWellFounded T) (s : T) :
    nodeRank hT s < (ω₁ : Ordinal.{0}) := by
  letI : _root_.IsWellFounded T (Child T) := ⟨hT⟩
  unfold nodeRank _root_.IsWellFounded.rank
  exact accRank_lt_omega_one (_root_.IsWellFounded.apply (Child T) s)

/-- The rank of every well-founded natural-number tree is below the first uncountable ordinal.-/
theorem treeRank_lt_omega_one (T : Descriptive.tree ℕ) (hT : IsWellFounded T) :
    rank T hT < (ω₁ : Ordinal.{0}) := by
  by_cases hroot : [] ∈ T
  · rw [rank_eq_nodeRank hT hroot]
    exact nodeRank_lt_omega_one hT ⟨[], hroot⟩
  · rw [rank_eq_zero_of_nil_not_mem hT hroot]
    exact omega_pos 1

/-- **Boundedness theorem for the well-founded-tree rank.** An analytic family contained in
`wellFoundedTrees` has a strict uniform rank bound below `ω₁`. The conclusion quantifies over the
well-foundedness proof so that it is independent of the particular proof supplied by the subset
hypothesis.-/
theorem rank_bounded_of_analytic_subset_wellFounded {A : Set TreeCode}
    (hA : MeasureTheory.AnalyticSet A) (hAWF : A ⊆ wellFoundedTrees) :
    ∃ ξ : Ordinal.{0}, ξ < ω₁ ∧
      ∀ (T : TreeCode), T ∈ A →
        ∀ hT : IsWellFounded (decodeTree T), rank (decodeTree T) hT < ξ := by
  have hdownAnalytic := analyticSet_treeRankDownwardClosure hA
  have hdownSubset := treeRankDownwardClosure_subset_wellFoundedTrees hAWF
  have hdownNe : treeRankDownwardClosure A ≠ wellFoundedTrees := by
    intro heq
    apply not_analyticSet_wellFoundedTrees
    rw [← heq]
    exact hdownAnalytic
  have hexists : ∃ U : TreeCode,
      U ∈ wellFoundedTrees ∧ U ∉ treeRankDownwardClosure A := by
    by_contra hnone
    apply hdownNe
    apply Set.Subset.antisymm hdownSubset
    intro U hU
    by_contra hnot
    exact hnone ⟨U, hU, hnot⟩
  obtain ⟨U, hU, hUoutside⟩ := hexists
  refine ⟨rank (decodeTree U) hU, treeRank_lt_omega_one (decodeTree U) hU, ?_⟩
  intro T hTA hT
  by_contra hnot
  have hle : rank (decodeTree U) hU ≤ rank (decodeTree T) hT := not_lt.mp hnot
  apply hUoutside
  exact ⟨T, hTA, (mem_treeRankLeAnalytic_iff_of_isWellFounded hT).2 ⟨hU, hle⟩⟩

/-- A continuous Baire-space family of well-founded tree codes has one countable strict rank
bound.-/
theorem rank_bounded_of_continuous_baire_family (f : (ℕ → ℕ) → TreeCode)
    (hf : Continuous f) (hWF : ∀ x, IsWellFounded (decodeTree (f x))) :
    ∃ ξ : Ordinal.{0}, ξ < ω₁ ∧
      ∀ x, rank (decodeTree (f x)) (hWF x) < ξ := by
  have hrange : MeasureTheory.AnalyticSet (Set.range f) :=
    MeasureTheory.analyticSet_range_of_polishSpace hf
  have hrangeWF : Set.range f ⊆ wellFoundedTrees := by
    rintro T ⟨x, rfl⟩
    exact hWF x
  obtain ⟨ξ, hξ, hbound⟩ :=
    rank_bounded_of_analytic_subset_wellFounded hrange hrangeWF
  refine ⟨ξ, hξ, fun x => ?_⟩
  exact hbound (f x) (Set.mem_range_self x) (hWF x)

/-- The empty family has a countable strict rank bound.-/
theorem rank_bounded_empty :
    ∃ ξ : Ordinal.{0}, ξ < ω₁ ∧
      ∀ (T : TreeCode), T ∈ (∅ : Set TreeCode) →
        ∀ hT : IsWellFounded (decodeTree T), rank (decodeTree T) hT < ξ := by
  exact ⟨0, omega_pos 1, fun _ hT => hT.elim⟩

end DescriptiveSetTheory.Tree
