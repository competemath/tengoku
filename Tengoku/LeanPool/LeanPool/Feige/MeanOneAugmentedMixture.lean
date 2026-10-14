/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.ProductTwoPointKernel
public import Tengoku

/-!
# A total augmented mixture for mean-one laws

The positive-moment branch uses the latent two-point measure from Lemma
4.6.  When the lower moment vanishes, the original law is `δ₁`, so the
latent law is simply the atom branch.  This removes the artificial
coordinatewise strict-moment assumption from the finite product mixture.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- The augmented latent law, including the degenerate zero-below-moment case. -/
def meanOneAugmentedLatent (μ : Measure ℝ) :
    Measure AugmentedTwoPointParams :=
  if belowMoment μ = 0 then
    Measure.dirac (Sum.inl ())
  else
    augmentedLatentMeasure μ (belowMoment μ)

/--
@isnad1 id=isprobab.2h1v.s6.1d78065eac12 from=translated src=- shape=ac606027 vocab=ea46b02a
-/
theorem meanOneAugmentedLatent_isProbability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    IsProbabilityMeasure (meanOneAugmentedLatent μ) := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, ite_eq_left hM]
    infer_instance
  · rw [meanOneAugmentedLatent, ite_eq_right hM]
    exact augmentedLatentMeasure_isProbability hμ hmean
      (lt_of_le_of_ne belowMoment_nonneg (Ne.symm hM))

/--
@isnad1 id=eq.2h1v.s6.df5f7e70a1cd from=translated src=- shape=3ff47eae vocab=56fefc66
-/
theorem augmentedTwoPointKernel_comp_meanOneLatent
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    augmentedTwoPointKernel ∘ₘ meanOneAugmentedLatent μ = μ := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, ite_eq_left hM]
    rw [Measure.dirac_bind augmentedTwoPointKernel.measurable]
    rw [augmentedTwoPointKernel_atom]
    exact (eq_dirac_one_of_belowMoment_eq_zero
      hμ hmean hM).symm
  · rw [meanOneAugmentedLatent, ite_eq_right hM,
      augmentedTwoPointKernel_comp_latent,
      fullKernelMixture_eq hμ hmean
        (lt_of_le_of_ne belowMoment_nonneg (Ne.symm hM))]

/-- Every finite product of mean-one laws is a mixture of the conditionally
independent augmented two-point systems, including all degenerate `δ₁`
coordinates.
@isnad1 id=eq.2h2v.s8.8efe44cb1f01 from=translated src=- shape=55656043 vocab=85772053
-/
theorem pi_eq_recursiveMeanOneAugmented_mixture
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1) :
    recursiveAugmentedKernel n ∘ₘ
        recursiveAugmentedLatent n
          (fun i ↦ meanOneAugmentedLatent (μ i)) =
      Measure.pi μ := by
  let hlatent : ∀ i, IsProbabilityMeasure
      (meanOneAugmentedLatent (μ i)) :=
    fun i ↦ meanOneAugmentedLatent_isProbability
      (hμ i) (hmean i)
  rw [recursiveAugmentedKernel_comp_latent]
  have hcoord :
      (fun i => augmentedTwoPointKernel ∘ₘ
          meanOneAugmentedLatent (μ i)) = μ := by
    funext i
    exact augmentedTwoPointKernel_comp_meanOneLatent
      (hμ i) (hmean i)
  rw [hcoord, recursiveRealProduct_eq_pi]

end

end Feige
