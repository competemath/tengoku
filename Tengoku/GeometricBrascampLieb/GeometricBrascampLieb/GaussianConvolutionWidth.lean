import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianConvolutionDerivatives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentiation in the Gaussian inverse-width parameter
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianConvolutionWidthDerivative (b : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f z * (-‖x-z‖ ^ 2 * gaussianKernel b (x-z))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=le.2h4v.s7.76f73e60d743 from=translated src=- shape=74b212a2 vocab=74e634b8
-/
theorem gaussianKernel_widthDerivative_norm_le {b a : ℝ} (hb : 0 < b) (hba : b ≤ a) (x : E) :
    ‖-‖x‖ ^ 2 * gaussianKernel a x‖ ≤ 1 + 2 / (b / 2) ^ 2 := by
  have he : gaussianKernel a x ≤ gaussianKernel b x := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hba (sq_nonneg ‖x‖)]
  have hp := norm_pow_mul_gaussianKernel_le 2 hb x
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul] at hp
  calc
    _ = ‖x‖ ^ 2 * gaussianKernel a x := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (sq_nonneg _), gaussianKernel, abs_of_pos (Real.exp_pos _)]
    _ ≤ ‖x‖ ^ 2 * gaussianKernel b x := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ ≤ _ := hp

/--
@isnad1 id=integrab.2h4v.s7.9618e33873eb from=translated src=- shape=555b3e8a vocab=f7791686
-/
theorem gaussianConvolutionWidthDerivative_integrand_integrable {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    Integrable (fun z => f z * (-‖x-z‖ ^ 2 * gaussianKernel b (x-z))) := by
  exact integrable_smul_bounded_kernel hf (by unfold gaussianKernel; fun_prop)
    (gaussianKernel_widthDerivative_norm_le hb le_rfl) x

/--
@isnad1 id=hasderiv.2h4v.s7.f68860f0b2f9 from=translated src=- shape=1c85174d vocab=95246dbf
-/
theorem gaussianConvolution_hasDerivAt_width {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    HasDerivAt (fun a => gaussianConvolution a f x) (gaussianConvolutionWidthDerivative b f x) b := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun a z => f z * gaussianKernel a (x-z))
    (F' := fun a z => f z * (-‖x-z‖ ^ 2 * gaussianKernel a (x-z)))
    (s := Ioi (b/2)) (bound := fun z => ‖f z‖ * (1 + 2 / ((b/2)/2) ^ 2))
    (Ioi_mem_nhds (by linarith : b/2 < b)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun a => hf.aestronglyMeasurable.mul
      ((gaussianKernel_continuous a).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact gaussianConvolution_integrand_integrable hf hb x
  · exact (gaussianConvolutionWidthDerivative_integrand_integrable hf hb x).aestronglyMeasurable
  · exact Eventually.of_forall fun z a ha => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (gaussianKernel_widthDerivative_norm_le (half_pos hb) ha.le (x-z)) (norm_nonneg _)
  · exact hf.norm.mul_const _
  · exact Eventually.of_forall fun z a _ => (gaussianKernel_hasDerivAt a (x-z)).const_mul (f z)

end GeometricBrascampLieb
