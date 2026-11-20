import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.HeatConvolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Continuity of the Hessian of logarithmic Gaussian regularization -/

noncomputable section
open MeasureTheory Set

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussianConvolutionGradient_continuous {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) : Continuous (gaussianConvolutionGradient b f) :=
  continuous_iff_continuousAt.mpr fun x => (gaussianConvolutionGradient_hasFDerivAt hf hb x).continuousAt

theorem gaussianConvolutionHessian_continuous {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) : Continuous (gaussianConvolutionHessian b f) := by
  have hbound : BddAbove (range fun x : E => ‖gaussianKernelHessian b x‖) := by
    refine ⟨2*b+4*b^2*(1+2/(b/2)^2), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact gaussianKernelHessian_norm_le hb x
  exact hbound.continuous_convolution_right_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hf (gaussianKernelHessian_continuous b)

theorem convolutionLogHeatFlow_hessian_continuous {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) (hmass : 0 < ∫ z, f z)
    {t : ℝ} (ht : 0 < t) : Continuous ((convolutionLogHeatFlow hf hf0 hmass).hessian t) := by
  have hu : Continuous (fun x => (heatConvolution f t x)⁻¹) :=
    (heatConvolution_continuous hf ht).inv₀ (fun x => (heatConvolution_pos hf hf0 hmass ht x).ne')
  have hg : Continuous (heatConvolutionGradient f t) :=
    continuous_iff_continuousAt.mpr fun x => (heatConvolutionGradient_hasFDerivAt hf ht x).continuousAt
  have hH : Continuous (heatConvolutionHessian f t) := by
    change Continuous (fun x => heatNormalization (E := E) t • gaussianConvolutionHessian (4*t)⁻¹ f x)
    exact (continuous_const : Continuous (fun _ : E => heatNormalization (E := E) t)).smul
      (gaussianConvolutionHessian_continuous hf (by positivity : 0 < (4*t)⁻¹))
  have hr : Continuous (fun x => (innerSL ℝ (heatConvolutionGradient f t x)).smulRight
      (heatConvolutionGradient f t x)) :=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp ((innerSL ℝ).continuous.comp hg)).clm_apply hg
  exact (hu.smul hH).sub ((hu.pow 2).smul hr)

end GeometricBrascampLieb
