module

public import Tengoku
public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

public section

open MeasureTheory ENNReal NNReal Set

attribute [fun_prop] MeasureTheory.StronglyMeasurable.integral_kernel

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}
  {A B : Set X} {f g : X → ℝ≥0∞} {x₀ : X}

class IsCondExp (π : Kernel[𝓑, 𝓧] X X) (μ : Measure[𝓧] X) : Prop where
  condExp_ae_eq_kernel_apply ⦃A : Set X⦄ : MeasurableSet[𝓧] A →
    μ[A.indicator 1| 𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal

lemma condExp_ae_eq_kernel_apply
    (h : ∀ (f : X → ℝ), Bornology.IsBounded (Set.range f) → Measurable[𝓧] f →
      condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    {A : Set X} (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal) := by
  have ind_bdd : Bornology.IsBounded (Set.range (A.indicator (fun _ ↦ (1 : ℝ)))) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rw [range_subset_iff]
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have ind_mble : Measurable[𝓧] (A.indicator (fun _ ↦ (1 : ℝ))) := by
    exact (measurable_indicator_const_iff 1).mpr A_mble
  specialize h _ ind_bdd ind_mble
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

variable [π.IsCondExp μ]

end ProbabilityTheory.Kernel
