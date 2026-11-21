/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosMinkowski
import Tengoku.Randomsettheory.RandomSetTheory.MinkowskiSelectionDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aumann expectation of finite Minkowski sums

The binary measurable-decomposition theorem extends by induction to every
finite family of compact nonempty Effros-measurable correspondences with
individual integrable envelopes.  Consequently, Aumann expectation commutes
exactly both with finite Minkowski sums and with nonempty finite Minkowski
averages.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory Set
open scoped Pointwise BigOperators InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- Aumann expectation commutes exactly with a finite Minkowski sum of
compact nonempty Effros-measurable correspondences admitting individual
integrable envelopes.
@isnad1 id=eq.5h7v.s8.b285a82fcb21 from=translated src=- shape=b993dd99 vocab=9b50ceed
-/
theorem aumannExpectation_finset_sum_of_effros_of_envelopes
    {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {μ : Measure Ω} (s : Finset ι) (S : ι → Ω → Set E)
    (hS : ∀ i ∈ s, RandomSet.IsEffrosMeasurable (S i))
    (hcompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    (g : ι → Ω → ℝ)
    (hg : ∀ i ∈ s, Integrable (g i) μ)
    (hdom : ∀ i ∈ s, ∀ ω, ∀ x ∈ S i ω, ‖x‖ ≤ g i ω) :
    aumannExpectation μ (fun ω => ∑ i ∈ s, S i ω) =
      ∑ i ∈ s, aumannExpectation μ (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : Integrable (fun _ : Ω => (0 : E)) μ :=
        integrable_zero Ω E μ
      simpa only [Finset.sum_empty, ← Set.singleton_zero, integral_zero] using
        (aumannExpectation_singleton hzero)
  | @insert a s ha ih =>
      have hSa : RandomSet.IsEffrosMeasurable (S a) :=
        hS a (Finset.mem_insert_self a s)
      have hSrest : RandomSet.IsEffrosMeasurable
          (fun ω => ∑ i ∈ s, S i ω) :=
        RandomSet.IsEffrosMeasurable.finset_sum s S
          (fun i hi => hS i (Finset.mem_insert_of_mem hi))
          (fun i hi ω => hcompact i (Finset.mem_insert_of_mem hi) ω)
          (fun i hi ω => hne i (Finset.mem_insert_of_mem hi) ω)
      have hcompactRest : ∀ ω, IsCompact (∑ i ∈ s, S i ω) :=
        fun ω => isCompact_finset_sum s (fun i => S i ω)
          (fun i hi => hcompact i (Finset.mem_insert_of_mem hi) ω)
      have hneRest : ∀ ω, (∑ i ∈ s, S i ω).Nonempty :=
        fun ω => nonempty_finset_sum s (fun i => S i ω)
          (fun i hi => hne i (Finset.mem_insert_of_mem hi) ω)
      have hgRest : Integrable (fun ω => ∑ i ∈ s, g i ω) μ :=
        integrable_finsetSum s
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have hdomRest : ∀ ω, ∀ x ∈ ∑ i ∈ s, S i ω,
          ‖x‖ ≤ ∑ i ∈ s, g i ω := by
        intro ω x hx
        exact norm_le_sum_radius_of_mem_finset_sum s
          (fun i => S i ω) (fun i => g i ω)
          (fun i hi y hy =>
            hdom i (Finset.mem_insert_of_mem hi) ω y hy) hx
      have hadd := aumannExpectation_add_of_effros_of_envelopes
        (μ := μ) (S := S a) (T := fun ω => ∑ i ∈ s, S i ω)
        hSa hSrest
        (fun ω => hcompact a (Finset.mem_insert_self a s) ω)
        hcompactRest
        (fun ω => hne a (Finset.mem_insert_self a s) ω)
        hneRest
        (hg a (Finset.mem_insert_self a s)) hgRest
        (fun ω x hx =>
          hdom a (Finset.mem_insert_self a s) ω x hx)
        hdomRest
      have hih := ih
        (fun i hi => hS i (Finset.mem_insert_of_mem hi))
        (fun i hi ω => hcompact i (Finset.mem_insert_of_mem hi) ω)
        (fun i hi ω => hne i (Finset.mem_insert_of_mem hi) ω)
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi ω x hx =>
          hdom i (Finset.mem_insert_of_mem hi) ω x hx)
      calc
        aumannExpectation μ (fun ω => ∑ i ∈ insert a s, S i ω) =
            aumannExpectation μ
              (fun ω => S a ω + ∑ i ∈ s, S i ω) := by
                congr 1
                funext ω
                rw [Finset.sum_insert ha]
        _ = aumannExpectation μ (S a) +
              aumannExpectation μ (fun ω => ∑ i ∈ s, S i ω) := hadd
        _ = aumannExpectation μ (S a) +
              ∑ i ∈ s, aumannExpectation μ (S i) := by rw [hih]
        _ = ∑ i ∈ insert a s, aumannExpectation μ (S i) := by
          rw [Finset.sum_insert ha]

/-- For a nonempty finite family, Aumann expectation commutes exactly with
the empirical Minkowski average.
@isnad1 id=eq.6h7v.s8.b9a19b3d8450 from=translated src=- shape=1cee89ee vocab=a6234e71
-/
theorem aumannExpectation_minkowskiAverage_of_effros_of_envelopes
    {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    (S : ι → Ω → Set E)
    (hS : ∀ i ∈ s, RandomSet.IsEffrosMeasurable (S i))
    (hcompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    (g : ι → Ω → ℝ)
    (hg : ∀ i ∈ s, Integrable (g i) μ)
    (hdom : ∀ i ∈ s, ∀ ω, ∀ x ∈ S i ω, ‖x‖ ≤ g i ω) :
    aumannExpectation μ
        (fun ω => minkowskiAverage s (fun i => S i ω)) =
      minkowskiAverage s (fun i => aumannExpectation μ (S i)) := by
  have hcard : ((s.card : ℝ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (Nat.cast_ne_zero.mpr hs.card_ne_zero)
  unfold minkowskiAverage
  rw [aumannExpectation_smul_of_ne (s.card : ℝ)⁻¹ hcard]
  rw [aumannExpectation_finset_sum_of_effros_of_envelopes
    s S hS hcompact hne g hg hdom]

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
