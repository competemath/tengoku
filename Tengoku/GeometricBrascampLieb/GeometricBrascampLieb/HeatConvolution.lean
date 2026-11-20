import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianConvolutionWidth
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.PositiveHeat
import Tengoku.Seed.Analysis.InnerProductSpace.Trace
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The classical heat equation for arbitrary integrable initial data

The normalization is `(4πt)^(-dim/2)`. At positive times the convolution has
the stated spatial gradient and Hessian and satisfies `∂t u = Δu`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem trace_integral_operator {A : E → E →L[ℝ] E} (hA : Integrable A) :
    LinearMap.trace ℝ E (∫ z, A z).toLinearMap =
      ∫ z, LinearMap.trace ℝ E (A z).toLinearMap := by
  let b := stdOrthonormalBasis ℝ E
  have hi (i) : Integrable (fun z => inner ℝ (b i) (A z (b i))) :=
    (innerSL ℝ (b i)).integrable_comp (hA.apply_continuousLinearMap (b i))
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    _ = ∑ i, ∫ z, inner ℝ (b i) (A z (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      change inner ℝ (b i) ((∫ z, A z) (b i)) = _
      rw [ContinuousLinearMap.integral_apply hA]
      exact ((innerSL ℝ (b i)).integral_comp_comm (hA.apply_continuousLinearMap (b i))).symm
    _ = ∫ z, ∑ i, inner ℝ (b i) (A z (b i)) :=
      (integral_finsetSum _ (fun i _ => hi i)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simpa only [ContinuousLinearMap.coe_coe] using (LinearMap.trace_eq_sum_inner (A z).toLinearMap b).symm)

theorem trace_gaussianConvolutionHessian {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    LinearMap.trace ℝ E (gaussianConvolutionHessian b f x).toLinearMap =
      (-2 * b * (Module.finrank ℝ E : ℝ)) * gaussianConvolution b f x -
        4 * b ^ 2 * gaussianConvolutionWidthDerivative b f x := by
  rw [gaussianConvolutionHessian, trace_integral_operator
    (gaussianConvolutionHessian_integrand_integrable hf hb x)]
  simp only [ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul,
    trace_gaussianKernelHessian]
  have he : (fun z => f z *
      ((-2*b*(Module.finrank ℝ E : ℝ) + 4*b^2*‖x-z‖^2) * gaussianKernel b (x-z))) =
      (fun z => (-2*b*(Module.finrank ℝ E : ℝ)) * (f z * gaussianKernel b (x-z)) -
        (4*b^2) * (f z * (-‖x-z‖^2 * gaussianKernel b (x-z)))) := by
    funext z
    ring
  have hki : Integrable (fun z => f z * gaussianKernel b (x-z)) :=
    gaussianConvolution_integrand_integrable hf hb x
  rw [he, integral_sub (hki.const_mul _)
    ((gaussianConvolutionWidthDerivative_integrand_integrable hf hb x).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

def heatNormalization (t : ℝ) : ℝ :=
  Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi * t))

def heatConvolution (f : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  heatNormalization (E := E) t * gaussianConvolution (4*t)⁻¹ f x

def heatConvolutionGradient (f : E → ℝ) (t : ℝ) (x : E) : E :=
  heatNormalization (E := E) t • gaussianConvolutionGradient (4*t)⁻¹ f x

def heatConvolutionHessian (f : E → ℝ) (t : ℝ) (x : E) : E →L[ℝ] E :=
  heatNormalization (E := E) t • gaussianConvolutionHessian (4*t)⁻¹ f x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem heatNormalization_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatNormalization (E := E))
      (heatNormalization (E := E) t * (-((Module.finrank ℝ E : ℝ)/2) / t)) t := by
  have hp : 4 * Real.pi * t ≠ 0 := by positivity
  have h := ((((hasDerivAt_id t).const_mul (4*Real.pi)).log hp).const_mul
    (-((Module.finrank ℝ E : ℝ)/2))).exp
  apply h.congr_deriv
  simp only [heatNormalization, id_eq, mul_one]
  field_simp

theorem heatConvolution_eq_gaussianRegularization {t : ℝ} (ht : 0 < t)
    (f : E → ℝ) (x : E) :
    heatConvolution f t x = gaussianRegularization (4*t)⁻¹ f x := by
  have hp : 0 < 4*Real.pi*t := by positivity
  have he : Real.pi / (4*t)⁻¹ = 4*Real.pi*t := by
    rw [div_inv_eq_mul]
    ring
  simp only [heatConvolution, heatNormalization, gaussianRegularization, he,
    Real.rpow_def_of_pos hp, div_eq_mul_inv, ← Real.exp_neg]
  rw [mul_comm]
  congr 2
  ring

theorem integral_heatConvolution {f : E → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) : ∫ x, heatConvolution f t x = ∫ x, f x := by
  simp_rw [heatConvolution_eq_gaussianRegularization ht]
  exact integral_gaussianRegularization hf (by positivity)

theorem heatConvolution_integrable {f : E → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) : Integrable (heatConvolution f t) :=
  (gaussianConvolution_integrable hf (by positivity : 0 < (4*t)⁻¹)).const_mul _

theorem heatConvolution_continuous {f : E → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) : Continuous (heatConvolution f t) :=
  continuous_const.mul (gaussianConvolution_continuous hf (by positivity : 0 < (4*t)⁻¹))

theorem heatConvolution_pos {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    (hmass : 0 < ∫ x, f x) {t : ℝ} (ht : 0 < t) (x : E) : 0 < heatConvolution f t x :=
  mul_pos (Real.exp_pos _) (gaussianConvolution_pos hf hf0 hmass (by positivity) x)

theorem heatConvolution_hasFDerivAt {f : E → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (x : E) :
    HasFDerivAt (heatConvolution f t) (innerSL ℝ (heatConvolutionGradient f t x)) x := by
  change HasFDerivAt (fun y => heatNormalization (E := E) t * gaussianConvolution (4*t)⁻¹ f y)
    (innerSL ℝ (heatNormalization (E := E) t • gaussianConvolutionGradient (4*t)⁻¹ f x)) x
  rw [map_smul]
  exact
    (gaussianConvolution_hasFDerivAt hf (by positivity : 0 < (4*t)⁻¹) x).const_mul
      (heatNormalization (E := E) t)

theorem heatConvolutionGradient_hasFDerivAt {f : E → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (x : E) :
    HasFDerivAt (heatConvolutionGradient f t) (heatConvolutionHessian f t x) x :=
  (gaussianConvolutionGradient_hasFDerivAt hf (by positivity : 0 < (4*t)⁻¹) x).fun_const_smul _

theorem heatConvolution_hasDerivAt {f : E → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heatConvolution f s x)
      (LinearMap.trace ℝ E (heatConvolutionHessian f t x).toLinearMap) t := by
  have hb : 0 < (4*t)⁻¹ := by positivity
  have hi := ((hasDerivAt_id t).const_mul 4).inv (by positivity : 4*t ≠ 0)
  have hc := (gaussianConvolution_hasDerivAt_width hf hb x).comp t hi
  apply ((heatNormalization_hasDerivAt (E := E) ht).mul hc).congr_deriv
  simp only [heatConvolutionHessian, ContinuousLinearMap.toLinearMap_smul,
    map_smul, smul_eq_mul, trace_gaussianConvolutionHessian hf hb x,
    Function.comp_apply, Pi.inv_apply, id_eq, mul_one]
  field_simp
  ring

/-- The logarithmic heat flow of a nonnegative integrable datum of positive mass.-/
def convolutionLogHeatFlow {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    (hmass : 0 < ∫ x, f x) : LogHeatFlow E :=
  logHeatFlowOfPositiveSolution (heatConvolution f) (heatConvolutionGradient f)
    (heatConvolutionHessian f)
    (fun _ ht => heatConvolution_pos hf hf0 hmass ht)
    (fun _ ht => heatConvolution_hasFDerivAt hf ht)
    (fun _ ht => heatConvolutionGradient_hasFDerivAt hf ht)
    (fun _ ht => heatConvolution_hasDerivAt hf ht)

end GeometricBrascampLieb
