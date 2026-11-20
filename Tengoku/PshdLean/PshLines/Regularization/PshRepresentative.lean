import Tengoku.PshdLean.PshLines.Regularization.DistributionRegularizationFinal
import Tengoku.PshdLean.PshLines.Regularization.PshRegularizationLimit
import Tengoku.PshdLean.PshLines.Regularization.PshRepresentativeGluing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive distributional Levi and PSH representatives

A distribution with nonnegative constant-direction Levi derivatives has a
plurisubharmonic representative, and conversely.

Source: Demailly, Complex Analytic and Differential Geometry, I.5.8,
using the regularization argument of I.4.18--4.20: local decreasing smooth
regularization, the decreasing weak-limit theorem, and local-to-global gluing.
-/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace PshLines.Regularization

/-- Existence of the canonical PSH representative. There is no
connectedness or preassigned locally integrable density assumption.-/
theorem exists_pshRepresentative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E} {T : 𝓓'(Ω, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T) :
    ∃ u : E → EReal, IsPshRepresentative μ T u := by
  apply exists_pshRepresentative_of_locally μ
  intro x hx
  obtain ⟨U, hUΩ, f, hxU, hf⟩ := exists_local_decreasing_psh_regularization μ hT x hx
  obtain ⟨u, hu⟩ := exists_pshRepresentative_of_decreasing_approximation μ hf
  exact ⟨U, hUΩ, u, hxU, hu⟩

/-- Nonnegative distributional Levi derivatives characterize distributions
represented by plurisubharmonic functions.-/
theorem hasNonnegativeDistributionalLevi_iff_exists_pshRepresentative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}
    (T : 𝓓'(Ω, ℝ)) :
    HasNonnegativeDistributionalLevi T ↔ ∃ u : E → EReal, IsPshRepresentative μ T u := by
  constructor
  · exact exists_pshRepresentative μ
  · rintro ⟨u, hu⟩
    exact hu.hasNonnegativeDistributionalLevi

end PshLines.Regularization
