import Tengoku.Nlalib.NLAlib.Probability.SubGaussian.LpMoments
import Tengoku.Seed.Algebra.Order.Floor.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real-exponent moments of centered sub-Gaussian observables

Round the exponent up to an even integer, use the actual even Gaussian-type
moment bound, and compare probability-space norms. This gives square-root
growth for every real exponent at least two, including zero variance proxies.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace NLAlib

/-- A centered sub-Gaussian observable belongs to every finite `L^q`; the
uncentered mean is the actual Bochner integral.-/
theorem memLp_of_centered_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω => X ω - ∫ y, X y ∂μ) c μ) (q : ℝ≥0) :
    MemLp X q μ := by
  have hh := (h.memLp q).add (memLp_const (∫ y, X y ∂μ))
  have heq : ((fun ω => X ω - ∫ y, X y ∂μ) + fun _ => ∫ y, X y ∂μ) = X := by
    ext ω
    simp
  rwa [heq] at hh

end NLAlib
