import Tengoku.SingularityCompleteLean.Singularity.FourierReduction
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.Analysis.Fourier.Convolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A logarithmic exponential density and its Fourier transform

The density g(t) = exp(t) exp(-exp(t)) has Fourier transform
Gamma(1 - 2πiξ). Its autocorrelation will give the Liouville kernel.
-/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform

namespace Singularity

/-- The logarithm of a unit exponential random variable has this density.-/
def gammaDensity (t : ℝ) : ℝ := Real.exp t * Real.exp (-Real.exp t)

/-- Complex-valued version, used by the Fourier integral.-/
def gammaDensityC (t : ℝ) : ℂ := gammaDensity t

theorem gammaDensity_pos (t : ℝ) : 0 < gammaDensity t := by
  unfold gammaDensity
  positivity

theorem gammaDensity_continuous : Continuous gammaDensity := by
  unfold gammaDensity
  fun_prop

/-- Complex powers of a positive real exponential.-/
theorem cpow_real_exp (t : ℝ) (z : ℂ) : (Real.exp t : ℂ) ^ z = Complex.exp ((t : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne')]
  rw [← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

/-- Pointwise identity for the change of variables in the Fourier integral.-/
theorem gammaDensity_fourier_integrand (ξ t : ℝ) :
    Complex.exp ((-2 * Real.pi * t * ξ : ℝ) * Complex.I) * gammaDensityC t =
      Real.exp t • ((Real.exp (-Real.exp t) : ℂ) *
        (Real.exp t : ℂ) ^ ((1 - (2 * Real.pi * ξ : ℝ) * Complex.I) - 1)) := by
  rw [cpow_real_exp]
  simp only [gammaDensityC, gammaDensity, Complex.ofReal_mul, Complex.real_smul]
  have he : ((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I =
      (t : ℂ) * ((1 - (2 * Real.pi * ξ : ℝ) * Complex.I) - 1) := by push_cast; ring
  push_cast at he ⊢
  rw [he]
  ring

end Singularity
