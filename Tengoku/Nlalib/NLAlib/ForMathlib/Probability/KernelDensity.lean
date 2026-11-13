import Tengoku.Seed.Probability.Kernel.WithDensity
import Tengoku.Seed.Probability.Kernel.Composition.MeasureComp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Markov kernels and mixture laws from densities

Nonnegative real densities of integral one define actual Markov kernels.
Their mixtures have the averaged density against the common reference
measure, by Tonelli. These generic facts support positive polynomial
smoothing without assuming an output probability law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Jointly measurable real densities which are nonnegative almost everywhere
and have integral one define a Markov kernel against the reference measure.
@isnad1 id=ismarkov.4h4v.s7.2244f7ae74dc from=translated src=- shape=706ce1e7 vocab=44cb0cc6
-/
theorem isMarkovKernel_const_withDensity_of_integral_eq_one
    (ν : Measure β) [SFinite ν] {f : α → β → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hi : ∀ a, Integrable (f a) ν) (hpos : ∀ a, 0 ≤ᵐ[ν] f a)
    (hmass : ∀ a, ∫ b, f a b ∂ν = 1) :
    IsMarkovKernel ((Kernel.const α ν).withDensity (fun a b => ENNReal.ofReal (f a b))) where
  isProbabilityMeasure a := by
    constructor
    rw [Kernel.withDensity_apply _ hf.ennreal_ofReal]
    simp only [Kernel.const_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi a) (hpos a), hmass a]
    exact ENNReal.ofReal_one

/-- Mixing densities against an input measure averages those densities. The
identity is for actual measures and permits infinite-valued densities.
@isnad1 id=eq.1h5v.s6.7a082444a7bb from=translated src=- shape=8140e9ab vocab=64af2e66
-/
theorem comp_const_withDensity (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    ((Kernel.const α ν).withDensity f) ∘ₘ μ =
      ν.withDensity (fun b => ∫⁻ a, f a b ∂μ) := by
  ext s hs
  rw [Measure.bind_apply hs ((Kernel.const α ν).withDensity f).aemeasurable,
    withDensity_apply _ hs]
  simp_rw [Kernel.withDensity_apply _ hf, Kernel.const_apply, withDensity_apply _ hs]
  exact lintegral_lintegral_swap hf.aemeasurable

end ProbabilityTheory.Kernel
