import Tengoku.SingularityCompleteLean.Singularity.GammaDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Liouville kernel as an autocorrelation

This identifies its ordinary Fourier transform with a product of Gamma values,
which is nonzero at every real frequency.
-/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform Convolution ComplexConjugate

namespace Singularity

/-- The logarithmic-coordinate Liouville kernel, written using exponentials.-/
def liouvilleKernel (t : ℝ) : ℝ := Real.exp (-t) / (1 + Real.exp (-t)) ^ 2

def liouvilleKernelC (t : ℝ) : ℂ := liouvilleKernel t

/-- The familiar hyperbolic-secant expression for the same kernel.
@isnad1 id=eq.0h1v.s6.c7ddecef52ab from=translated src=- shape=367d307d vocab=20b2fb29
-/
theorem liouvilleKernel_eq_cosh (t : ℝ) :
    liouvilleKernel t = 1 / (4 * Real.cosh (t / 2) ^ 2) := by
  have he : Real.exp (-t) = (Real.exp (t / 2))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold liouvilleKernel
  rw [he, Real.cosh_eq, Real.exp_neg]
  have hp := Real.exp_pos (t / 2)
  field_simp
  ring

/-- The identity which permits the substitution x = exp(s).
@isnad1 id=eq.0h2v.s6.af3cb7537af5 from=translated src=- shape=862aea81 vocab=134981a7
-/
theorem gammaDensity_autocorrelation_integrand (t s : ℝ) :
    gammaDensity s * gammaDensity (s - t) =
      Real.exp (-t) * (Real.exp s *
        (Real.exp s * Real.exp (-((1 + Real.exp (-t)) * Real.exp s)))) := by
  have he : Real.exp (s - t) = Real.exp s * Real.exp (-t) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have he' : Real.exp (-Real.exp s) * Real.exp (-(Real.exp s * Real.exp (-t))) =
      Real.exp (-((1 + Real.exp (-t)) * Real.exp s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gammaDensity
  rw [he]
  calc
    Real.exp s * Real.exp (-Real.exp s) *
        (Real.exp s * Real.exp (-t) * Real.exp (-(Real.exp s * Real.exp (-t)))) =
        Real.exp (-t) * (Real.exp s * (Real.exp s *
          (Real.exp (-Real.exp s) * Real.exp (-(Real.exp s * Real.exp (-t)))))) := by ring
    _ = _ := by rw [he']

/-- Reflection reverses the frequency in the ordinary Fourier transform.
@isnad1 id=eq.0h1v.s6.afd4a9c3e92f from=translated src=- shape=8110978f vocab=212b588a
-/
theorem fourier_reflected_gammaDensity (ξ : ℝ) :
    𝓕 (fun t => gammaDensityC (-t)) ξ = 𝓕 gammaDensityC (-ξ) := by
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) gammaDensityC ξ

/-- Euler's reflection formula evaluates the Gamma product explicitly.
@isnad1 id=eq.0h1v.s5.9ce915baca54 from=translated src=- shape=149f719f vocab=ee00492b
-/
theorem gamma_product_liouvilleMultiplier (ω : ℝ) :
    Complex.Gamma (1 - (ω : ℂ) * Complex.I) *
      Complex.Gamma (1 + (ω : ℂ) * Complex.I) = (liouvilleMultiplier ω : ℂ) := by
  by_cases hω : ω = 0
  · simp [hω, liouvilleMultiplier]
  have hz : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
  have hs : Real.sinh (Real.pi * ω) ≠ 0 := by
    simpa using mul_ne_zero Real.pi_ne_zero hω
  have hsc : (Real.sinh (Real.pi * ω) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [show (1 + (ω : ℂ) * Complex.I) = (ω : ℂ) * Complex.I + 1 by ring,
    Complex.Gamma_add_one _ hz]
  calc
    Complex.Gamma (1 - (ω : ℂ) * Complex.I) *
        ((ω : ℂ) * Complex.I * Complex.Gamma ((ω : ℂ) * Complex.I)) =
        (ω : ℂ) * Complex.I * (Complex.Gamma ((ω : ℂ) * Complex.I) *
          Complex.Gamma (1 - (ω : ℂ) * Complex.I)) := by ring
    _ = (ω : ℂ) * Complex.I * (Real.pi / Complex.sin (Real.pi * ((ω : ℂ) * Complex.I))) := by
      rw [Complex.Gamma_mul_Gamma_one_sub]
    _ = (liouvilleMultiplier ω : ℂ) := by
      rw [← mul_assoc (Real.pi : ℂ), Complex.sin_mul_I,
        ← Complex.ofReal_mul, ← Complex.ofReal_sinh]
      simp only [liouvilleMultiplier, ite_eq_right hω, Complex.ofReal_div, Complex.ofReal_mul]
      field_simp

end Singularity
