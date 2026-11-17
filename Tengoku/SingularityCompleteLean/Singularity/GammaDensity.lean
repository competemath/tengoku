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

/--
@isnad1 id=lt.0h1v.s3.cf9f52f597a3 from=translated src=- shape=8a62b088 vocab=1cb4190d
-/
theorem gammaDensity_pos (t : ℝ) : 0 < gammaDensity t := by
  unfold gammaDensity
  positivity

/--
@isnad1 id=continuo.0h0v.s3.88fa859f73fa from=translated src=- shape=e3d48bcb vocab=8588a99e
-/
theorem gammaDensity_continuous : Continuous gammaDensity := by
  unfold gammaDensity
  fun_prop

/-- Complex powers of a positive real exponential.
@isnad1 id=eq.0h2v.s4.0f4aa4a7e894 from=translated src=- shape=d72d682b vocab=af5a6e51
-/
theorem cpow_real_exp (t : ℝ) (z : ℂ) : (Real.exp t : ℂ) ^ z = Complex.exp ((t : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne')]
  rw [← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

/-- Pointwise identity for the change of variables in the Fourier integral.
@isnad1 id=eq.0h2v.s7.75538599a6c7 from=translated src=- shape=a0e44e60 vocab=70c55626
-/
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
