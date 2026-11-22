/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aumann expectations of random intervals

The Aumann expectation of an integrably bounded random interval is exactly
the interval between the integrals of its endpoints.  This is the basic
one-dimensional closedness theorem and the canonical exact computation for
interval-valued missing-data correspondences.
-/

open Set MeasureTheory

noncomputable section

namespace RandomSetTheory

/-- **Aumann expectation of a random interval.**  No atomlessness,
measurability-of-the-correspondence, or closure operation is needed: the two
integrable endpoints are selections, every other selection integrates
between them, and convexity fills the resulting interval.
@isnad1 id=eq.3h4v.s7.11a2bbbf3a43 from=translated src=- shape=d83cadc1 vocab=647bf949
-/
theorem aumannExpectation_Icc
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : Ω → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hab : ∀ᵐ ω ∂μ, a ω ≤ b ω) :
    aumannExpectation μ (fun ω => Icc (a ω) (b ω)) =
      Icc (∫ ω, a ω ∂μ) (∫ ω, b ω ∂μ) := by
  let S : Ω → Set ℝ := fun ω => Icc (a ω) (b ω)
  have haSel : IsIntegrableSelection μ S a := by
    refine ⟨ha, ?_⟩
    filter_upwards [hab] with ω hω
    exact ⟨le_rfl, hω⟩
  have hbSel : IsIntegrableSelection μ S b := by
    refine ⟨hb, ?_⟩
    filter_upwards [hab] with ω hω
    exact ⟨hω, le_rfl⟩
  have haMem : (∫ ω, a ω ∂μ) ∈ aumannExpectation μ S :=
    ⟨a, haSel, rfl⟩
  have hbMem : (∫ ω, b ω ∂μ) ∈ aumannExpectation μ S :=
    ⟨b, hbSel, rfl⟩
  have habInt : (∫ ω, a ω ∂μ) ≤ ∫ ω, b ω ∂μ :=
    integral_mono_ae ha hb hab
  apply Set.Subset.antisymm
  · rintro x ⟨f, hf, rfl⟩
    have haf : ∀ᵐ ω ∂μ, a ω ≤ f ω := by
      filter_upwards [hf.2] with ω hω
      exact hω.1
    have hfb : ∀ᵐ ω ∂μ, f ω ≤ b ω := by
      filter_upwards [hf.2] with ω hω
      exact hω.2
    exact ⟨integral_mono_ae ha hf.1 haf,
      integral_mono_ae hf.1 hb hfb⟩
  · intro x hx
    have hconv : Convex ℝ (aumannExpectation μ S) :=
      aumannExpectation_convex
        (Filter.Eventually.of_forall fun ω => convex_Icc (a ω) (b ω))
    have hseg := hconv.segment_subset haMem hbMem
    rw [segment_eq_Icc habInt] at hseg
    exact hseg hx

/-- A deterministic interval is fixed by Aumann expectation on a probability
space.
@isnad1 id=eq.1h4v.s5.60360f14d485 from=translated src=- shape=34a93f32 vocab=896a2747
-/
theorem aumannExpectation_const_Icc
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    aumannExpectation μ (fun _ : Ω => Icc a b) = Icc a b := by
  simpa using aumannExpectation_Icc
    (μ := μ) (integrable_const a) (integrable_const b)
    (Filter.Eventually.of_forall fun _ => hab)

end RandomSetTheory
