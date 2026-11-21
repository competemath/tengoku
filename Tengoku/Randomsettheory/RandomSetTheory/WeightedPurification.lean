/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.LyapunovVector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Purification of measurable binary mixtures

On a finite atomless measure space, a measurable weight with values in the
unit interval can be replaced by the indicator of one measurable set without
changing any prescribed finite-dimensional vector integral.  Applying this
to the difference of two integrable functions purifies a measurable binary
mixture pointwise.

The proof uses the compact moment fibres developed in
`RandomSetTheory.LyapunovVector`: the weight defines a positive content
dominated by the reference measure, a compact nonempty fibre has an extreme
point, and the bang--bang theorem identifies every such extreme point with a
restriction of the reference measure.
-/

open MeasureTheory Set

noncomputable section

namespace RandomSetTheory

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **Weighted bang--bang principle.**  A measurable `[0,1]`-valued weight
can be purified to a measurable set while preserving the integral of one
finite-dimensional vector-valued function.  The bounds need only hold almost
everywhere.
@isnad1 id=ex.5h5v.s8.091110516976 from=translated src=- shape=80f1d595 vocab=c26b63e4
-/
theorem exists_measurableSet_setIntegral_eq_integral_weighted_of_atomless
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f : Omega → E} (hf : Integrable f mu)
    {a : Omega → ℝ} (ha : Measurable a)
    (ha0 : ∀ᵐ omega ∂mu, 0 ≤ a omega)
    (ha1 : ∀ᵐ omega ∂mu, a omega ≤ 1) :
    ∃ A : Set Omega, MeasurableSet A ∧
      (∫ omega in A, f omega ∂mu) =
        ∫ omega, a omega • f omega ∂mu := by
  let g : Omega → E := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[mu] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g mu := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.measurable_mk
  let z : E := ∫ omega, a omega • g omega ∂mu
  let m0 : MeasurableSubset Omega → ℝ := clippedDensityContent mu a
  have hm0dom : m0 ∈ dominatedContents mu :=
    clippedDensityContent_mem_dominatedContents mu a
  have hm0Moment :
      dominatedContentIntegral mu g ⟨m0, hm0dom⟩ = z := by
    exact dominatedContentIntegral_clippedDensityContent
      mu g ha ha0 ha1
  have hm0Fiber : m0 ∈ dominatedIntegralFiber mu g z :=
    (mem_dominatedIntegralFiber_iff mu g z m0).2 ⟨hm0dom, hm0Moment⟩
  have hfiber : (dominatedIntegralFiber mu g z).Nonempty := ⟨m0, hm0Fiber⟩
  obtain ⟨m, hmext⟩ :=
    (isCompact_dominatedIntegralFiber mu hg hgm z).extremePoints_nonempty
      hfiber
  obtain ⟨A, hA, hmA⟩ :=
    extreme_dominatedIntegralFiber_is_restriction mu hmu hg hmext
  have hmfiber : m ∈ dominatedIntegralFiber mu g z :=
    (mem_extremePoints_iff_left.mp hmext).1
  obtain ⟨hm, hmz⟩ :=
    (mem_dominatedIntegralFiber_iff mu g z m).mp hmfiber
  subst m
  have hset : (∫ omega in A, g omega ∂mu) = z := by
    rw [← dominatedContentIntegral_restrictionContent mu g A]
    exact hmz
  refine ⟨A, hA, ?_⟩
  calc
    (∫ omega in A, f omega ∂mu) = ∫ omega in A, g omega ∂mu :=
      integral_congr_ae (ae_restrict_of_ae hfg)
    _ = z := hset
    _ = ∫ omega, a omega • g omega ∂mu := rfl
    _ = ∫ omega, a omega • f omega ∂mu := by
      apply integral_congr_ae
      filter_upwards [hfg] with omega homega
      rw [homega]

/-- A measurable binary mixture of two integrable functions can be replaced
by an integrable function choosing pointwise between them, with exactly the
same vector integral.
@isnad1 id=ex.6h6v.s8.e12547eb6d7d from=translated src=- shape=0290b9bc vocab=7e1bb440
-/
theorem exists_integrable_binarySelection_integral_eq_of_atomless
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f g : Omega → E} (hf : Integrable f mu) (hg : Integrable g mu)
    {a : Omega → ℝ} (ha : Measurable a)
    (ha0 : ∀ᵐ omega ∂mu, 0 ≤ a omega)
    (ha1 : ∀ᵐ omega ∂mu, a omega ≤ 1) :
    ∃ q : Omega → E, Integrable q mu ∧
      (∀ omega, q omega = f omega ∨ q omega = g omega) ∧
      (∫ omega, q omega ∂mu) =
        ∫ omega, a omega • f omega +
          (1 - a omega) • g omega ∂mu := by
  have hfg : Integrable (fun omega ↦ f omega - g omega) mu := hf.sub hg
  have haNorm : ∀ᵐ omega ∂mu, ‖a omega‖ ≤ 1 := by
    filter_upwards [ha0, ha1] with omega h0 h1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have haWeighted :
      Integrable (fun omega ↦ a omega • (f omega - g omega)) mu :=
    hfg.bdd_smul 1 ha.aestronglyMeasurable haNorm
  obtain ⟨A, hA, hsplit⟩ :=
    exists_measurableSet_setIntegral_eq_integral_weighted_of_atomless
      mu hmu hfg ha ha0 ha1
  let q : Omega → E := fun omega ↦
    g omega + A.indicator (fun omega ↦ f omega - g omega) omega
  have hq : Integrable q mu :=
    hg.add (hfg.integrableOn.integrable_indicator hA)
  refine ⟨q, hq, ?_, ?_⟩
  · intro omega
    by_cases homega : omega ∈ A
    · left
      simp [q, Set.indicator_of_mem homega]
    · right
      simp [q, Set.indicator_of_notMem homega]
  · rw [show q = fun omega ↦
        g omega + A.indicator (fun omega ↦ f omega - g omega) omega
      from rfl]
    rw [integral_add hg (hfg.integrableOn.integrable_indicator hA)]
    rw [integral_indicator hA, hsplit]
    rw [← integral_add hg haWeighted]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega ↦ by module

/-- Selection-valued form of binary purification.  If both endpoints select
the same correspondence, the purified pointwise choice is again an
integrable selection of that correspondence.
@isnad1 id=ex.6h7v.s8.0bdcfd78d98e from=translated src=- shape=31f6385d vocab=f260cae8
-/
theorem exists_binary_purification_of_integrableSelections_of_atomless
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {S : Omega → Set E} {f g : Omega → E}
    (hf : IsIntegrableSelection mu S f)
    (hg : IsIntegrableSelection mu S g)
    {a : Omega → ℝ} (ha : Measurable a)
    (ha0 : ∀ᵐ omega ∂mu, 0 ≤ a omega)
    (ha1 : ∀ᵐ omega ∂mu, a omega ≤ 1) :
    ∃ q : Omega → E, IsIntegrableSelection mu S q ∧
      (∀ omega, q omega = f omega ∨ q omega = g omega) ∧
      (∫ omega, q omega ∂mu) =
        ∫ omega, a omega • f omega +
          (1 - a omega) • g omega ∂mu := by
  obtain ⟨q, hq, hchoice, hqIntegral⟩ :=
    exists_integrable_binarySelection_integral_eq_of_atomless
      mu hmu hf.1 hg.1 ha ha0 ha1
  refine ⟨q, ⟨hq, ?_⟩, hchoice, hqIntegral⟩
  filter_upwards [hf.2, hg.2] with omega hfmem hgmem
  rcases hchoice omega with hqf | hqg
  · simpa [hqf] using hfmem
  · simpa [hqg] using hgmem

end RandomSetTheory
