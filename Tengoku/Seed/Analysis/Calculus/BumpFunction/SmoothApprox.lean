/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.BumpFunction.Convolution
public import Tengoku.Seed.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Density of smooth functions in the space of continuous functions

In this file we prove that smooth functions are dense in the set of continuous functions
from a real finite-dimensional vector space to a Banach space,
see `ContinuousMap.dense_setOfPred_contDiff`.
We also prove several unbundled versions of this statement.

The heavy part of the proof is done upstream in `ContDiffBump.dist_normed_convolution_le`
and `HasCompactSupport.contDiff_convolution_left`.
Here we wrap these results removing measure-related arguments from the assumptions.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {ε : ℝ}

open scoped ContDiff unitInterval Topology
open Set Metric MeasureTheory

/--
@isnad1 id=ex.2h5v.s7.728927e153d7 from=seed src=0 shape=048ad9ce vocab=c7c64d3a
-/
theorem MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    (hf : LocallyIntegrable f μ) (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, ∀ δ, (∀ x ∈ ball a ε, dist (f x) (f a) ≤ δ) →
      dist (g a) (f a) ≤ δ := by
  set φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨_, ?_, fun a δ ↦ φ.dist_normed_convolution_le hf.aestronglyMeasurable⟩
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

/--
@isnad1 id=ex.2h4v.s7.5e9b3137a805 from=seed src=0 shape=1f0da5c1 vocab=d0fcd267
-/
theorem Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (hf : Continuous f)
    (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, ∀ δ, (∀ x ∈ ball a ε, dist (f x) (f a) ≤ δ) →
      dist (g a) (f a) ≤ δ := by
  borelize E
  exact (hf.locallyIntegrable (μ := .addHaar)).exists_contDiff_dist_le_of_forall_mem_ball_dist_le hε

/--
@isnad1 id=ex.2h4v.s7.d2f7c5705431 from=seed src=0 shape=493da76b vocab=e00e809c
-/
theorem UniformContinuous.exists_contDiff_dist_le (hf : UniformContinuous f) (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, dist (g a) (f a) < ε := by
  rcases Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases hf.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hδ with ⟨g, hgc, hg⟩
  exact ⟨g, hgc, fun a ↦ (hg a _ fun _ h ↦ (hfδ h).le).trans_lt (half_lt_self hε)⟩

/-- Infinitely smooth functions are dense in the space of continuous functions.
@isnad1 id=dense.0h2v.s7.4b5c45576ecd from=seed src=0 shape=90407d90 vocab=e219b928
-/
theorem ContinuousMap.dense_setOfPred_contDiff : Dense {f : C(E, F) | ContDiff ℝ ∞ f} := by
  intro f
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)]
  simp only [Prod.forall, mem_ofPred_eq, and_imp]
  intro K ε hK hε
  have : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous <| by fun_prop
  rcases Metric.uniformContinuousOn_iff.mp this (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases (map_continuous f).exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  refine ⟨⟨g, hgc.continuous⟩, hgc, fun x hx ↦ (hg _ _ fun y hy ↦ ?_).trans_lt (half_lt_self hε)⟩
  rw [mem_ball, lt_min_iff] at hy
  exact hfδ _ (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) _
    (self_subset_cthickening _ hx) hy.2 |>.le

/--
@isnad1 id=dense.0h2v.s7.4b5c45576ecd from=seed src=0 shape=90407d90 vocab=e219b928
-/
@[deprecated (since := "2026-07-09")]
alias ContinuousMap.dense_setOf_contDiff := ContinuousMap.dense_setOfPred_contDiff
