import Tengoku.PaperCLean.PaperC.Analysis.SpatialMarkedParameters
import Tengoku.Seed.Probability.Distributions.Poisson.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Poisson Laplace functionals

This module records the algebraic identity behind the void-probability
argument of Section 14 and packages the final analytic convergence criterion.
It deliberately states convergence of Laplace functionals, which is the
source-facing endpoint needed by the manuscript and does not depend on a
separate topology-of-point-measures API.
-/

namespace PaperC
namespace PoissonLaplaceFunctional

open scoped BigOperators Topology NNReal
open Filter MeasureTheory Set ProbabilityTheory
open SpatialMarkedParameters

noncomputable section

/--
Analytic closing lemma: if a finite-model Laplace functional differs from
`exp(-parameter)` by an error tending to zero, and the parameter tends to
`a`, then the functional tends to `exp(-a)`.-/
theorem tendsto_laplace_of_parameter_and_error
    {ι : Type*} {l : Filter ι}
    {laplace parameter error : ι → ℝ} {a : ℝ}
    (hparameter : Tendsto parameter l (𝓝 a))
    (herror : Tendsto error l (𝓝 0))
    (happrox :
      ∀ᶠ n in l,
        |laplace n - Real.exp (-parameter n)| ≤ error n) :
    Tendsto laplace l (𝓝 (Real.exp (-a))) := by
  have habs :
      Tendsto
        (fun n ↦ |laplace n - Real.exp (-parameter n)|)
        l (𝓝 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
      happrox herror
  have hdiff :
      Tendsto
        (fun n ↦ laplace n - Real.exp (-parameter n))
        l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hexp :
      Tendsto
        (fun n ↦ Real.exp (-parameter n))
        l (𝓝 (Real.exp (-a))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hparameter.neg
  convert hdiff.add hexp using 1
  · funext n
    ring
  · simp

/--
Section 14.2 endpoint in Laplace-functional form.  The test function is
continuous and nonnegative, the arithmetic/probabilistic layer supplies only
the displayed vanishing approximation error, and the conclusion is the
Laplace functional of `PPP(rate dt)` on `[1,2)`.-/
theorem sectionFourteenTwo_laplaceFunctional
    {N L : ℕ → ℕ} {rate : ℝ} {g : ℝ → ℝ}
    {laplace error : ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ContinuousOn g (Set.Icc (1 : ℝ) 2))
    (_hg0 : ∀ t, 0 ≤ g t)
    (herror : Tendsto error atTop (𝓝 0))
    (happrox :
      ∀ᶠ n in atTop,
        |laplace n -
          Real.exp
            (-spatialThinnedParameter (N n) (L n) g)| ≤
          error n) :
    Tendsto laplace atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          (1 - Real.exp (-g t)))))) := by
  have hparam :=
    tendsto_spatialThinnedParameter hN hscale hg
  simpa only [spatialRetention] using
    tendsto_laplace_of_parameter_and_error
      hparam herror happrox

/--
Section 14.4 endpoint for a fixed mark cutoff `E`.  It is the Laplace
functional of the Poisson intensity
`rate · dt ⊗ (∑_{e≤E} 2^{-(e+1)} δ_e)`.-/
theorem sectionFourteenFour_laplaceFunctional
    {N L : ℕ → ℕ} {rate : ℝ} {E : ℕ}
    {g : ℝ → ℕ → ℝ} {laplace error : ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ∀ e ≤ E,
      ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2))
    (_hg0 : ∀ t e, 0 ≤ g t e)
    (herror : Tendsto error atTop (𝓝 0))
    (happrox :
      ∀ᶠ n in atTop,
        |laplace n -
          Real.exp
            (-markedThinnedParameter (N n) (L n) E g)| ≤
          error n) :
    Tendsto laplace atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          ∑ e ∈ Finset.range (E + 1),
            (1 / (2 : ℝ) ^ (e + 1)) *
              (1 - Real.exp (-g t e)))))) := by
  have hparam :=
    tendsto_markedThinnedParameter hN hscale hg
  simpa only [markedRetentionIntegrand, geometricMarkWeight,
    spatialRetention] using
      tendsto_laplace_of_parameter_and_error
        hparam herror happrox

end

end PoissonLaplaceFunctional
end PaperC
