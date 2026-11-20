import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.HeatConvolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic derivative bounds for bounded-support initial data

The derivative integrals are bounded by the convolution itself times a
polynomial. Dividing by the positive convolution therefore gives polynomial
growth bounds, without needing covariance identities.
-/

noncomputable section
open MeasureTheory

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
@isnad1 id=eq.1h3v.s6.6ff7dce7e037 from=translated src=- shape=1fe0cf85 vocab=94dd9f2a
-/
theorem gaussianKernelGradient_norm_eq {b : ℝ} (hb : 0 ≤ b) (x : E) :
    ‖gaussianKernelGradient b x‖ = 2*b*‖x‖*gaussianKernel b x := by
  simp only [gaussianKernelGradient, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hb, gaussianKernel, abs_of_pos (Real.exp_pos _)]
  norm_num
  ring

/--
@isnad1 id=le.1h3v.s7.39f71c72a2a1 from=translated src=- shape=bc6e1e91 vocab=b48483b3
-/
theorem gaussianKernelHessian_norm_le_kernel {b : ℝ} (hb : 0 ≤ b) (x : E) :
    ‖gaussianKernelHessian b x‖ ≤ (2*b + 4*b^2*‖x‖^2)*gaussianKernel b x := by
  have hk : 0 ≤ gaussianKernel b x := (Real.exp_pos _).le
  calc
    _ ≤ ‖(-2*b*gaussianKernel b x) • ContinuousLinearMap.id ℝ E‖ +
        ‖(4*b^2*gaussianKernel b x) • (innerSL ℝ x).smulRight x‖ := norm_add_le _ _
    _ ≤ (2*b*gaussianKernel b x)*1 + (4*b^2*gaussianKernel b x)*(‖x‖*‖x‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb,
        abs_of_nonneg hk, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      norm_num only [abs_neg, abs_pow, abs_of_nonneg hb]
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = _ := by ring

/--
@isnad1 id=le.2h4v.s7.833b8e4fc5fb from=translated src=- shape=8290a44c vocab=007a0e96
-/
theorem norm_inv_smul_le_of_norm_le_mul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {u C : ℝ} {g : G} (hu : 0 < u) (hg : ‖g‖ ≤ C*u) :
    ‖u⁻¹ • g‖ ≤ C := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu)]
  calc
    _ ≤ u⁻¹*(C*u) := mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hu.le)
    _ = C := by field_simp

/--
@isnad1 id=le.3h6v.s8.4b0824337db3 from=translated src=- shape=c1fdac6f vocab=a9e4600c
-/
theorem logarithmicHessian_norm_le {u C K : ℝ} {g : E} {H : E →L[ℝ] E}
    (hu : 0 < u) (hg : ‖g‖ ≤ C*u) (hH : ‖H‖ ≤ K*u) :
    ‖logarithmicHessian u g H‖ ≤ K + C^2 := by
  have h1 := norm_inv_smul_le_of_norm_le_mul hu hg
  have h2 := norm_inv_smul_le_of_norm_le_mul hu hH
  calc
    _ ≤ ‖u⁻¹ • H‖ + ‖(u⁻¹^2) • (innerSL ℝ g).smulRight g‖ := norm_sub_le _ _
    _ = ‖u⁻¹ • H‖ + ‖u⁻¹ • g‖^2 := by
      simp only [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply,
        innerSL_apply_norm, abs_pow, mul_pow]
      ring
    _ ≤ K + C^2 := add_le_add h2 (pow_le_pow_left₀ (norm_nonneg _) h1 2)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=le.4h5v.s7.5c825cf0f7dd from=translated src=- shape=4506425b vocab=94e90294
-/
theorem gaussianConvolutionGradient_norm_le_of_support_bound {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {b : ℝ} (hb : 0 < b) (x : E) :
    ‖gaussianConvolutionGradient b f x‖ ≤
      (2*b*(‖x‖+R))*gaussianConvolution b f x := by
  rw [gaussianConvolutionGradient, gaussianConvolution, ← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((gaussianConvolution_integrand_integrable hf hb x).const_mul _)
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : f z = 0
    · simp only [hz, zero_smul, norm_zero, zero_mul, mul_zero, le_refl]
    · have hd : ‖x-z‖ ≤ ‖x‖+R := (norm_sub_le x z).trans (add_le_add le_rfl (hsupport z hz))
      have hfz := hf0 z
      have hk : 0 ≤ gaussianKernel b (x-z) := (Real.exp_pos _).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 z), gaussianKernelGradient_norm_eq hb.le]
      calc
        _ ≤ f z * (2*b*(‖x‖+R)*gaussianKernel b (x-z)) := by
          gcongr
        _ = _ := by unfold gaussianKernel; ring

/--
@isnad1 id=le.4h5v.s8.e278db5f4ce2 from=translated src=- shape=b90a487d vocab=b30a8726
-/
theorem gaussianConvolutionHessian_norm_le_of_support_bound {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {b : ℝ} (hb : 0 < b) (x : E) :
    ‖gaussianConvolutionHessian b f x‖ ≤
      (2*b+4*b^2*(‖x‖+R)^2)*gaussianConvolution b f x := by
  rw [gaussianConvolutionHessian, gaussianConvolution, ← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((gaussianConvolution_integrand_integrable hf hb x).const_mul _)
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : f z = 0
    · simp only [hz, zero_smul, norm_zero, zero_mul, mul_zero, le_refl]
    · have hd : ‖x-z‖ ≤ ‖x‖+R := (norm_sub_le x z).trans (add_le_add le_rfl (hsupport z hz))
      have hfz := hf0 z
      have hk : 0 ≤ gaussianKernel b (x-z) := (Real.exp_pos _).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
      calc
        _ ≤ f z * ((2*b+4*b^2*‖x-z‖^2)*gaussianKernel b (x-z)) :=
          mul_le_mul_of_nonneg_left (gaussianKernelHessian_norm_le_kernel hb.le _) (hf0 z)
        _ ≤ f z * ((2*b+4*b^2*(‖x‖+R)^2)*gaussianKernel b (x-z)) := by
          gcongr
        _ = _ := by unfold gaussianKernel; ring

/--
@isnad1 id=le.4h5v.s7.c382fb7da536 from=translated src=- shape=1527cc23 vocab=49ccb58a
-/
theorem heatConvolutionGradient_norm_le_of_support_bound {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖heatConvolutionGradient f t x‖ ≤
      (2*(4*t)⁻¹*(‖x‖+R))*heatConvolution f t x := by
  rw [heatConvolutionGradient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (show 0 < heatNormalization (E := E) t from Real.exp_pos _)]
  calc
    _ ≤ heatNormalization (E := E) t *
        ((2*(4*t)⁻¹*(‖x‖+R))*gaussianConvolution (4*t)⁻¹ f x) :=
      mul_le_mul_of_nonneg_left (gaussianConvolutionGradient_norm_le_of_support_bound
        hf hf0 hsupport (by positivity) x) (Real.exp_pos _).le
    _ = _ := by unfold heatConvolution; ring

/--
@isnad1 id=le.4h5v.s8.2db453b7ca0e from=translated src=- shape=9be5c3c6 vocab=4bff7b7a
-/
theorem heatConvolutionHessian_norm_le_of_support_bound {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖heatConvolutionHessian f t x‖ ≤
      (2*(4*t)⁻¹+4*((4*t)⁻¹)^2*(‖x‖+R)^2)*heatConvolution f t x := by
  rw [heatConvolutionHessian, norm_smul, Real.norm_eq_abs,
    abs_of_pos (show 0 < heatNormalization (E := E) t from Real.exp_pos _)]
  calc
    _ ≤ heatNormalization (E := E) t *
        ((2*(4*t)⁻¹+4*((4*t)⁻¹)^2*(‖x‖+R)^2)*gaussianConvolution (4*t)⁻¹ f x) :=
      mul_le_mul_of_nonneg_left (gaussianConvolutionHessian_norm_le_of_support_bound
        hf hf0 hsupport (by positivity) x) (Real.exp_pos _).le
    _ = _ := by unfold heatConvolution; ring

/--
@isnad1 id=le.5h5v.s8.0eec8ed0cefd from=translated src=- shape=fc79d9b7 vocab=5fb5794c
-/
theorem convolutionLogHeatFlow_gradient_norm_le {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) (hmass : 0 < ∫ z, f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖(convolutionLogHeatFlow hf hf0 hmass).gradient t x‖ ≤ 2*(4*t)⁻¹*(‖x‖+R) :=
  norm_inv_smul_le_of_norm_le_mul (heatConvolution_pos hf hf0 hmass ht x)
    (heatConvolutionGradient_norm_le_of_support_bound hf hf0 hsupport ht x)

/--
@isnad1 id=le.5h5v.s8.94b43e806861 from=translated src=- shape=a17ba490 vocab=04dd357e
-/
theorem convolutionLogHeatFlow_hessian_norm_le {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) (hmass : 0 < ∫ z, f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖(convolutionLogHeatFlow hf hf0 hmass).hessian t x‖ ≤
      2*(4*t)⁻¹ + 8*((4*t)⁻¹)^2*(‖x‖+R)^2 := by
  have h := logarithmicHessian_norm_le (heatConvolution_pos hf hf0 hmass ht x)
    (heatConvolutionGradient_norm_le_of_support_bound hf hf0 hsupport ht x)
    (heatConvolutionHessian_norm_le_of_support_bound hf hf0 hsupport ht x)
  calc
    _ ≤ (2*(4*t)⁻¹+4*((4*t)⁻¹)^2*(‖x‖+R)^2) + (2*(4*t)⁻¹*(‖x‖+R))^2 := h
    _ = _ := by ring

end GeometricBrascampLieb
