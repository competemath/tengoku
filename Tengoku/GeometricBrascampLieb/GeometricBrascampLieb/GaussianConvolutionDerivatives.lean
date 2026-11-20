import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianKernel
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianConvolution
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionDifferentiation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spatial derivatives of Gaussian convolution

These are actual derivatives for every integrable initial datum, with no
regularity or bounded-support assumption on that datum.
-/

noncomputable section
open MeasureTheory

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianConvolutionGradient (b : ℝ) (f : E → ℝ) (x : E) : E :=
  ∫ z, f z • gaussianKernelGradient b (x-z)

def gaussianConvolutionHessian (b : ℝ) (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  ∫ z, f z • gaussianKernelHessian b (x-z)

theorem gaussianConvolutionGradient_integrand_integrable {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    Integrable (fun z => f z • gaussianKernelGradient b (x-z)) :=
  integrable_smul_bounded_kernel hf (gaussianKernelGradient_continuous b)
    (gaussianKernelGradient_norm_le hb) x

theorem gaussianConvolutionHessian_integrand_integrable {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    Integrable (fun z => f z • gaussianKernelHessian b (x-z)) :=
  integrable_smul_bounded_kernel hf (gaussianKernelHessian_continuous b)
    (gaussianKernelHessian_norm_le hb) x

theorem gaussianConvolution_hasFDerivAt {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    HasFDerivAt (gaussianConvolution b f)
      (innerSL ℝ (gaussianConvolutionGradient b f x)) x := by
  have h := hasFDerivAt_convolution_of_bounded_kernel (C := 1)
    (C' := 2*b*(1+1/(b/2))) hf (gaussianKernel_continuous b)
    ((innerSL ℝ).continuous.comp (gaussianKernelGradient_continuous b))
    (gaussianKernel_hasFDerivAt b)
    (fun y => by simpa only [gaussianKernel, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      gaussianKernel_le_one hb.le y)
    (fun y => by simpa only [Function.comp_apply, innerSL_apply_norm] using
      gaussianKernelGradient_norm_le hb y) x
  have he : (∫ z, f z • innerSL ℝ (gaussianKernelGradient b (x-z))) =
      innerSL ℝ (gaussianConvolutionGradient b f x) := by
    simp_rw [← map_smul]
    exact (innerSL ℝ).integral_comp_comm (gaussianConvolutionGradient_integrand_integrable hf hb x)
  simp only [Function.comp_apply] at h
  rw [he] at h
  exact h

theorem gaussianConvolutionGradient_hasFDerivAt {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    HasFDerivAt (gaussianConvolutionGradient b f) (gaussianConvolutionHessian b f x) x :=
  hasFDerivAt_convolution_of_bounded_kernel hf (gaussianKernelGradient_continuous b)
    (gaussianKernelHessian_continuous b) (gaussianKernelGradient_hasFDerivAt b)
    (gaussianKernelGradient_norm_le hb) (gaussianKernelHessian_norm_le hb) x

end GeometricBrascampLieb
