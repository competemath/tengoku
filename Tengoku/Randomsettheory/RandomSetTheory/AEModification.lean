/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableBergeMaximum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Almost-everywhere regularization of correspondences

Random-set assumptions are often stated only almost surely, whereas exact
measurable-selection theorems are most convenient for correspondences whose
fibres are nonempty and compact everywhere.  This module replaces a
correspondence outside a measurable full-measure set by a fixed default
fibre.  The replacement remains Effros measurable, has the desired
pointwise properties everywhere, and does not change its Aumann expectation.

As applications, the measurable Berge maximum/minimum and metric projection
theorems are upgraded to hypotheses that hold on a measurable set of full
measure.  Their conclusions are exact almost surely for the original
correspondence.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory

noncomputable section

namespace RandomSetTheory

/-- Use `S` on `A` and a fixed default fibre `K` outside `A`.-/
noncomputable def correspondenceOn {Ω X : Type*} (A : Set Ω)
    (S : Ω → Set X) (K : Set X) : Ω → Set X := by
  classical
  exact fun ω => if ω ∈ A then S ω else K

@[simp]
theorem correspondenceOn_of_mem {Ω X : Type*} {A : Set Ω}
    {S : Ω → Set X} {K : Set X} {ω : Ω} (hω : ω ∈ A) :
    correspondenceOn A S K ω = S ω := by
  simp [correspondenceOn, hω]

@[simp]
theorem correspondenceOn_of_not_mem {Ω X : Type*} {A : Set Ω}
    {S : Ω → Set X} {K : Set X} {ω : Ω} (hω : ω ∉ A) :
    correspondenceOn A S K ω = K := by
  simp [correspondenceOn, hω]

/-- Measurable gluing of an Effros correspondence with a fixed fibre.-/
theorem effrosMeasurable_correspondenceOn
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    {A : Set Ω} (hA : MeasurableSet A) {S : Ω → Set X}
    (hS : RandomSet.IsEffrosMeasurable S) (K : Set X) :
    RandomSet.IsEffrosMeasurable (correspondenceOn A S K) := by
  intro U hU
  have hEq :
      {ω | (correspondenceOn A S K ω ∩ U).Nonempty} =
        (A ∩ {ω | (S ω ∩ U).Nonempty}) ∪
          (Aᶜ ∩ {ω | (K ∩ U).Nonempty}) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [correspondenceOn, hω]
  rw [hEq]
  exact (hA.inter (hS U hU)).union
    (hA.compl.inter (RandomSet.isEffrosMeasurable_const K U hU))

theorem correspondenceOn_isCompact
    {Ω X : Type*} [TopologicalSpace X]
    {A : Set Ω} {S : Ω → Set X} {K : Set X}
    (hS : ∀ ω ∈ A, IsCompact (S ω)) (hK : IsCompact K) (ω : Ω) :
    IsCompact (correspondenceOn A S K ω) := by
  by_cases hω : ω ∈ A
  · simpa [correspondenceOn, hω] using hS ω hω
  · simpa [correspondenceOn, hω] using hK

theorem correspondenceOn_nonempty
    {Ω X : Type*} {A : Set Ω} {S : Ω → Set X} {K : Set X}
    (hS : ∀ ω ∈ A, (S ω).Nonempty) (hK : K.Nonempty) (ω : Ω) :
    (correspondenceOn A S K ω).Nonempty := by
  by_cases hω : ω ∈ A
  · simpa [correspondenceOn, hω] using hS ω hω
  · simpa [correspondenceOn, hω] using hK

theorem correspondenceOn_isClosed
    {Ω X : Type*} [TopologicalSpace X]
    {A : Set Ω} {S : Ω → Set X} {K : Set X}
    (hS : ∀ ω ∈ A, IsClosed (S ω)) (hK : IsClosed K) (ω : Ω) :
    IsClosed (correspondenceOn A S K ω) := by
  by_cases hω : ω ∈ A
  · simpa [correspondenceOn, hω] using hS ω hω
  · simpa [correspondenceOn, hω] using hK

theorem correspondenceOn_convex
    {Ω E : Type*} {A : Set Ω} {S : Ω → Set E} {K : Set E}
    {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [IsOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (hS : ∀ ω ∈ A, Convex 𝕜 (S ω)) (hK : Convex 𝕜 K) (ω : Ω) :
    Convex 𝕜 (correspondenceOn A S K ω) := by
  by_cases hω : ω ∈ A
  · simpa [correspondenceOn, hω] using hS ω hω
  · simpa [correspondenceOn, hω] using hK

/-- On a full-measure set, regularization agrees almost everywhere with the
original correspondence.-/
theorem correspondenceOn_ae_eq
    {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Set Ω} {S : Ω → Set X} {K : Set X}
    (hA : ∀ᵐ ω ∂μ, ω ∈ A) :
    correspondenceOn A S K =ᵐ[μ] S := by
  filter_upwards [hA] with ω hω
  exact correspondenceOn_of_mem hω

/-- Changing exceptional fibres on a measurable null set leaves the Aumann
expectation unchanged.-/
theorem aumannExpectation_correspondenceOn
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {A : Set Ω} {S : Ω → Set E} {K : Set E}
    (hA : ∀ᵐ ω ∂μ, ω ∈ A) :
    aumannExpectation μ (correspondenceOn A S K) =
      aumannExpectation μ S :=
  aumannExpectation_congr_ae (correspondenceOn_ae_eq hA)

/-! ## Almost-everywhere Berge theorems -/

/-- Exact measurable maximization when compactness and nonemptiness hold on
a measurable set of full measure.-/
theorem exists_measurable_bergeMaximizer_ae
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    {μ : Measure Ω} {A : Set Ω} (hAmeas : MeasurableSet A)
    (hA : ∀ᵐ ω ∂μ, ω ∈ A)
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω ∈ A, IsCompact (S ω))
    (hne : ∀ ω ∈ A, (S ω).Nonempty)
    (x₀ : X) {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    ∃ s : Ω → X, Measurable s ∧
      ∀ᵐ ω ∂μ, s ω ∈ S ω ∧
        f (ω, s ω) = bergeMaxValue S f ω := by
  letI : Nonempty X := ⟨x₀⟩
  let T : Ω → Set X := correspondenceOn A S {x₀}
  have hT : RandomSet.IsEffrosMeasurable T :=
    effrosMeasurable_correspondenceOn hAmeas hS {x₀}
  have hTcompact : ∀ ω, IsCompact (T ω) := fun ω =>
    correspondenceOn_isCompact hcompact (isCompact_singleton) ω
  have hTne : ∀ ω, (T ω).Nonempty := fun ω =>
    correspondenceOn_nonempty hne (Set.singleton_nonempty x₀) ω
  obtain ⟨s, hsmeas, hs⟩ :=
    exists_measurable_bergeMaximizer hT hTcompact hTne hfmeas hfcont
  refine ⟨s, hsmeas, ?_⟩
  filter_upwards [hA] with ω hω
  have hTω : T ω = S ω := by simp [T, hω]
  refine ⟨hTω ▸ (hs ω).1, ?_⟩
  exact (hs ω).2.trans (by simp only [bergeMaxValue, hTω])

/-- Exact measurable minimization under almost-everywhere compactness and
nonemptiness.-/
theorem exists_measurable_bergeMinimizer_ae
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    {μ : Measure Ω} {A : Set Ω} (hAmeas : MeasurableSet A)
    (hA : ∀ᵐ ω ∂μ, ω ∈ A)
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω ∈ A, IsCompact (S ω))
    (hne : ∀ ω ∈ A, (S ω).Nonempty)
    (x₀ : X) {f : Ω × X → ℝ} (hfmeas : Measurable f)
    (hfcont : ∀ ω, Continuous fun x => f (ω, x)) :
    ∃ s : Ω → X, Measurable s ∧
      ∀ᵐ ω ∂μ, s ω ∈ S ω ∧
        f (ω, s ω) = bergeMinValue S f ω := by
  letI : Nonempty X := ⟨x₀⟩
  let T : Ω → Set X := correspondenceOn A S {x₀}
  have hT : RandomSet.IsEffrosMeasurable T :=
    effrosMeasurable_correspondenceOn hAmeas hS {x₀}
  have hTcompact : ∀ ω, IsCompact (T ω) := fun ω =>
    correspondenceOn_isCompact hcompact (isCompact_singleton) ω
  have hTne : ∀ ω, (T ω).Nonempty := fun ω =>
    correspondenceOn_nonempty hne (Set.singleton_nonempty x₀) ω
  obtain ⟨s, hsmeas, hs⟩ :=
    exists_measurable_bergeMinimizer hT hTcompact hTne hfmeas hfcont
  refine ⟨s, hsmeas, ?_⟩
  filter_upwards [hA] with ω hω
  have hTω : T ω = S ω := by simp [T, hω]
  refine ⟨hTω ▸ (hs ω).1, ?_⟩
  exact (hs ω).2.trans (by simp only [bergeMinValue, hTω])

/-- A measurable nearest point exists almost surely when the original
correspondence is compact and nonempty almost surely on a measurable set.-/
theorem exists_measurable_metricProjection_ae
    {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    {μ : Measure Ω} {A : Set Ω} (hAmeas : MeasurableSet A)
    (hA : ∀ᵐ ω ∂μ, ω ∈ A)
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω ∈ A, IsCompact (S ω))
    (hne : ∀ ω ∈ A, (S ω).Nonempty)
    (x₀ : X) {y : Ω → X} (hy : Measurable y) :
    ∃ p : Ω → X, Measurable p ∧
      ∀ᵐ ω ∂μ, p ω ∈ S ω ∧
        dist (y ω) (p ω) = Metric.infDist (y ω) (S ω) := by
  letI : Nonempty X := ⟨x₀⟩
  let T : Ω → Set X := correspondenceOn A S {x₀}
  have hT : RandomSet.IsEffrosMeasurable T :=
    effrosMeasurable_correspondenceOn hAmeas hS {x₀}
  have hTcompact : ∀ ω, IsCompact (T ω) := fun ω =>
    correspondenceOn_isCompact hcompact (isCompact_singleton) ω
  have hTne : ∀ ω, (T ω).Nonempty := fun ω =>
    correspondenceOn_nonempty hne (Set.singleton_nonempty x₀) ω
  obtain ⟨p, hpmeas, hp⟩ :=
    exists_measurable_metricProjection hT hTcompact hTne hy
  refine ⟨p, hpmeas, ?_⟩
  filter_upwards [hA] with ω hω
  simpa [T, correspondenceOn, hω] using hp ω

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
