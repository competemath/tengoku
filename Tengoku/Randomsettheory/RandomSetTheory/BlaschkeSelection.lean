/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.RadstromEmbedding
import Tengoku.Seed.Topology.Sets.VietorisTopology
import Tengoku.Seed.Topology.Sequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Blaschke selection for compact convex sets

In a finite-dimensional real inner-product space, the family of all
nonempty compact convex subsets of a fixed compact set is compact for the
Hausdorff metric.  In particular, every uniformly bounded sequence of such
sets has a Hausdorff-convergent subsequence whose limit is again nonempty,
compact, and convex.

The compactness of all nonempty compact subsets of a fixed compact set is
the Vietoris-hyperspace theorem already available in Mathlib.  The only
additional ingredient is that convex compact sets form a closed subset of
that hyperspace, proved in `RadstromEmbedding`.
-/

open Set Metric TopologicalSpace Filter

noncomputable section

namespace RandomSetTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Blaschke compactness.** Nonempty compact convex subsets of a fixed
compact set form a compact family for the Hausdorff metric.-/
theorem isCompact_nonemptyCompactConvex_subsets_of_isCompact
    {C : Set E} (hC : IsCompact C) :
    IsCompact {K : NonemptyCompacts E |
      (K : Set E) ⊆ C ∧ Convex ℝ (K : Set E)} := by
  have hsubsets : IsCompact {K : NonemptyCompacts E | (K : Set E) ⊆ C} :=
    NonemptyCompacts.isCompact_subsets_of_isCompact hC
  have hconvex : IsClosed {K : NonemptyCompacts E |
      Convex ℝ (K : Set E)} :=
    isClosed_compactConvexSet
  simpa only [Set.mem_ofPred_eq, Set.ofPred_and] using
    hsubsets.inter_right hconvex

/-- Radius-bounded form of Blaschke compactness.-/
theorem isCompact_nonemptyCompactConvex_subsets_closedBall (R : ℝ) :
    IsCompact {K : NonemptyCompacts E |
      (K : Set E) ⊆ Metric.closedBall (0 : E) R ∧
        Convex ℝ (K : Set E)} :=
  isCompact_nonemptyCompactConvex_subsets_of_isCompact
    (isCompact_closedBall (0 : E) R)

/-- Pointwise norm-bound form of Blaschke compactness.-/
theorem isCompact_nonemptyCompactConvex_of_norm_le (R : ℝ) :
    IsCompact {K : NonemptyCompacts E |
      (∀ x ∈ (K : Set E), ‖x‖ ≤ R) ∧ Convex ℝ (K : Set E)} := by
  simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using
    isCompact_nonemptyCompactConvex_subsets_closedBall (E := E) R

/-- Sequential Blaschke selection inside an arbitrary fixed compact set.-/
theorem exists_hausdorff_tendsto_subseq_of_compactConvex_subsets
    {C : Set E} (hC : IsCompact C) (K : ℕ → NonemptyCompacts E)
    (hsubset : ∀ n, (K n : Set E) ⊆ C)
    (hconvex : ∀ n, Convex ℝ (K n : Set E)) :
    ∃ L : NonemptyCompacts E,
      (L : Set E) ⊆ C ∧ Convex ℝ (L : Set E) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto
          (fun n ↦ hausdorffDist (K (phi n) : Set E) (L : Set E))
          atTop (nhds 0) := by
  let A : Set (NonemptyCompacts E) := {L |
    (L : Set E) ⊆ C ∧ Convex ℝ (L : Set E)}
  have hA : IsCompact A := by
    simpa only [A] using
      isCompact_nonemptyCompactConvex_subsets_of_isCompact (E := E) hC
  have hK : ∀ n, K n ∈ A := fun n ↦ ⟨hsubset n, hconvex n⟩
  obtain ⟨L, hL, phi, hphi, hlim⟩ := hA.isSeqCompact hK
  refine ⟨L, hL.1, hL.2, phi, hphi, ?_⟩
  have hdist := (tendsto_iff_dist_tendsto_zero).1 hlim
  simpa only [Function.comp_apply, NonemptyCompacts.dist_eq] using hdist

/-- Classical uniformly bounded sequential form of Blaschke's selection
theorem.  The limit remains in the same closed ball.-/
theorem exists_hausdorff_tendsto_subseq_of_uniformlyBounded_compactConvex
    (K : ℕ → NonemptyCompacts E) (R : ℝ)
    (hbound : ∀ n, ∀ x ∈ (K n : Set E), ‖x‖ ≤ R)
    (hconvex : ∀ n, Convex ℝ (K n : Set E)) :
    ∃ L : NonemptyCompacts E,
      (∀ x ∈ (L : Set E), ‖x‖ ≤ R) ∧ Convex ℝ (L : Set E) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto
          (fun n ↦ hausdorffDist (K (phi n) : Set E) (L : Set E))
          atTop (nhds 0) := by
  have hsubset : ∀ n, (K n : Set E) ⊆
      Metric.closedBall (0 : E) R := by
    intro n x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n x hx
  obtain ⟨L, hLsub, hLconv, phi, hphi, hlim⟩ :=
    exists_hausdorff_tendsto_subseq_of_compactConvex_subsets
      (E := E) (isCompact_closedBall (0 : E) R) K hsubset hconvex
  refine ⟨L, ?_, hLconv, phi, hphi, hlim⟩
  intro x hx
  have := hLsub hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using this

end RandomSetTheory
