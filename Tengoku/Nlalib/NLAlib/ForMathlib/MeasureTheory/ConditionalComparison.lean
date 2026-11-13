import Tengoku.Seed.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional comparison on measurable cuts

The pull-out property of indicators preserves an integrable scalar comparison
on any event measurable with respect to the conditioning sigma-algebra.
-/

noncomputable section

open MeasureTheory Set Filter

namespace MeasureTheory

/-- An integrable real comparison on a conditioning-measurable cut remains true for
the conditional expectations on that cut.
Source: Mathlib conditional indicator pull-out and conditional monotonicity;
helper for Tropp 2011 (matrix Freedman), atlas `matrix-freedman` (partial).
@isnad1 id=eventual.5h7v.s7.7651aa64d521 from=translated src=- shape=a366376f vocab=3f0c8026
-/
theorem ae_condExp_le_condExp_on_of_ae_le_on {Ω : Type*}
    {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} (hm : m ≤ mΩ)
    {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    {s : Set Ω} (hs : MeasurableSet[m] s) (hXY : ∀ᵐ ω ∂μ, ω ∈ s → X ω ≤ Y ω) :
    ∀ᵐ ω ∂μ, ω ∈ s → μ[X | m] ω ≤ μ[Y | m] ω := by
  have hpoint : s.indicator X ≤ᵐ[μ] s.indicator Y := by
    filter_upwards [hXY] with ω hω
    by_cases hsω : ω ∈ s
    · simpa only [Set.indicator_of_mem hsω] using hω hsω
    · simp only [Set.indicator_of_notMem hsω, le_refl]
  have h := condExp_mono (m := m) (hX.indicator (hm _ hs)) (hY.indicator (hm _ hs)) hpoint
  filter_upwards [h, condExp_indicator hX hs, condExp_indicator hY hs] with ω hω h₁ h₂
  intro hsω
  rw [h₁, h₂] at hω
  simpa only [Set.indicator_of_mem hsω] using hω

end MeasureTheory
