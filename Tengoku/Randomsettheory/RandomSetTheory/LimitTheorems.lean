/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Geometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transfer principles for random-set limits and concentration

For compact convex sets, convergence and deviation bounds for support
functions transfer exactly to Hausdorff distance.  These deterministic and
almost-sure wrappers are the final geometric step in laws of large numbers,
functional central limit theorems, and finite-net concentration arguments.
-/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

noncomputable section

namespace RandomSetTheory

/-- Uniform support convergence on the unit ball is equivalent to Hausdorff
convergence for a family of compact nonempty convex sets.
@isnad1 id=iff.6h5v.s8.960617a854e8 from=translated src=- shape=336460a5 vocab=32a9ef86
-/
theorem tendsto_supportHausdorffGap_iff_hausdorffDist
    {ι E : Type*} {l : Filter ι}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : ι → Set E} {L : Set E}
    (hKcompact : ∀ i, IsCompact (K i)) (hLcompact : IsCompact L)
    (hKne : ∀ i, (K i).Nonempty) (hLne : L.Nonempty)
    (hKconv : ∀ i, Convex ℝ (K i)) (hLconv : Convex ℝ L) :
    Tendsto (fun i => supportHausdorffGap (K i) L) l (𝓝 0) ↔
      Tendsto (fun i => hausdorffDist (K i) L) l (𝓝 0) := by
  have hEq : ∀ i, supportHausdorffGap (K i) L = hausdorffDist (K i) L :=
    fun i => supportHausdorffGap_eq_hausdorffDist
      (hKcompact i) hLcompact (hKne i) hLne (hKconv i) hLconv
  simp_rw [hEq]

/-- Almost-sure support convergence transfers pointwise to almost-sure
Hausdorff convergence.
@isnad1 id=eventual.7h5v.s8.4cb7b36680b8 from=translated src=- shape=a48de33b vocab=634e4c7c
-/
theorem ae_tendsto_hausdorffDist_of_supportHausdorffGap
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} {K : ℕ → Ω → Set E} {L : Ω → Set E}
    (hKcompact : ∀ n ω, IsCompact (K n ω))
    (hLcompact : ∀ ω, IsCompact (L ω))
    (hKne : ∀ n ω, (K n ω).Nonempty) (hLne : ∀ ω, (L ω).Nonempty)
    (hKconv : ∀ n ω, Convex ℝ (K n ω))
    (hLconv : ∀ ω, Convex ℝ (L ω))
    (h : ∀ᵐ ω ∂μ,
      Tendsto (fun n => supportHausdorffGap (K n ω) (L ω)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => hausdorffDist (K n ω) (L ω)) atTop (𝓝 0) := by
  filter_upwards [h] with ω hω
  exact (tendsto_supportHausdorffGap_iff_hausdorffDist
    (fun n => hKcompact n ω) (hLcompact ω)
    (fun n => hKne n ω) (hLne ω)
    (fun n => hKconv n ω) (hLconv ω)).mp hω

/-- The Hausdorff upper-tail event is exactly the corresponding uniform
support-function upper-tail event.
@isnad1 id=eq.6h5v.s8.47b4245697fa from=translated src=- shape=2576ef51 vocab=514feb89
-/
theorem hausdorffDist_ge_event_eq_supportHausdorffGap_ge_event
    {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Ω → Set E}
    (hKcompact : ∀ ω, IsCompact (K ω))
    (hLcompact : ∀ ω, IsCompact (L ω))
    (hKne : ∀ ω, (K ω).Nonempty) (hLne : ∀ ω, (L ω).Nonempty)
    (hKconv : ∀ ω, Convex ℝ (K ω))
    (hLconv : ∀ ω, Convex ℝ (L ω)) (r : ℝ) :
    {ω | r ≤ hausdorffDist (K ω) (L ω)} =
      {ω | r ≤ supportHausdorffGap (K ω) (L ω)} := by
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [supportHausdorffGap_eq_hausdorffDist
    (hKcompact ω) (hLcompact ω) (hKne ω) (hLne ω)
    (hKconv ω) (hLconv ω)]

/-- Any probability or outer-measure bound proved for the uniform support gap
immediately yields the identical Hausdorff bound.
@isnad1 id=le.7h7v.s8.0e405e8ef596 from=translated src=- shape=817e8f9e vocab=79e5fde5
-/
theorem measure_hausdorffDist_ge_le_of_supportHausdorffGap_ge_le
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} {K L : Ω → Set E}
    (hKcompact : ∀ ω, IsCompact (K ω))
    (hLcompact : ∀ ω, IsCompact (L ω))
    (hKne : ∀ ω, (K ω).Nonempty) (hLne : ∀ ω, (L ω).Nonempty)
    (hKconv : ∀ ω, Convex ℝ (K ω))
    (hLconv : ∀ ω, Convex ℝ (L ω))
    {r : ℝ} {δ : ℝ≥0∞}
    (hbound : μ {ω | r ≤ supportHausdorffGap (K ω) (L ω)} ≤ δ) :
    μ {ω | r ≤ hausdorffDist (K ω) (L ω)} ≤ δ := by
  rw [hausdorffDist_ge_event_eq_supportHausdorffGap_ge_event
    hKcompact hLcompact hKne hLne hKconv hLconv]
  exact hbound

/-- Finite-net union bound for Hausdorff deviations.  Any scalar tail bound
available for the support functions at the net points can be summed directly
to give a Hausdorff tail bound.
@isnad1 id=le.12h11v.s9.f4fe0701263b from=translated src=- shape=3a522cdb vocab=7549bba9
-/
theorem measure_hausdorffDist_gt_le_finset_support
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} {K L : Ω → Set E}
    (hKcompact : ∀ ω, IsCompact (K ω))
    (hLcompact : ∀ ω, IsCompact (L ω))
    (hKne : ∀ ω, (K ω).Nonempty) (hLne : ∀ ω, (L ω).Nonempty)
    (hKconv : ∀ ω, Convex ℝ (K ω))
    (hLconv : ∀ ω, Convex ℝ (L ω))
    {RK RL eps s : ℝ}
    (hRK : ∀ ω, ∀ x ∈ K ω, ‖x‖ ≤ RK)
    (hRL : ∀ ω, ∀ x ∈ L ω, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (hs : 0 ≤ s)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    {δ : ℝ≥0∞}
    (htail : ∀ v ∈ N,
      μ {ω | s < |supportFunction (K ω) v - supportFunction (L ω) v|} ≤ δ) :
    μ {ω | s + (RK + RL) * eps < hausdorffDist (K ω) (L ω)} ≤
      ∑ _v ∈ N, δ := by
  classical
  let A : E → Set Ω := fun v =>
    {ω | s < |supportFunction (K ω) v - supportFunction (L ω) v|}
  have hsub :
      {ω | s + (RK + RL) * eps < hausdorffDist (K ω) (L ω)} ⊆
        ⋃ v ∈ N, A v := by
    intro ω hω
    by_contra hnone
    have hN : ∀ v ∈ N,
        |supportFunction (K ω) v - supportFunction (L ω) v| ≤ s := by
      intro v hv
      by_contra hvbad
      apply hnone
      exact Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨hv, lt_of_not_ge hvbad⟩⟩
    have hhd := hausdorffDist_le_of_finset_net_supportFunction
      (hKcompact ω) (hLcompact ω) (hKne ω) (hLne ω)
      (hKconv ω) (hLconv ω) (hRK ω) (hRL ω)
      heps hs N hnet hN
    exact (not_lt_of_ge hhd) hω
  calc
    μ {ω | s + (RK + RL) * eps < hausdorffDist (K ω) (L ω)} ≤
        μ (⋃ v ∈ N, A v) := measure_mono hsub
    _ ≤ ∑ v ∈ N, μ (A v) := measure_biUnion_finset_le N A
    _ ≤ ∑ _v ∈ N, δ := by
      exact Finset.sum_le_sum fun v hv => htail v hv

end RandomSetTheory
