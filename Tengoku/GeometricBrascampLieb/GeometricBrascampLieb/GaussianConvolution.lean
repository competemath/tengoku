import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianCompactBounds
import Tengoku.Seed.Analysis.Convolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gaussian regularization of integrable initial data

The convolution is continuous, integrable, strictly positive for nonnegative
data of positive mass, and has a uniform Gaussian tail for bounded support.
Normalization preserves the input mass. The heat equation is not asserted here.
-/

noncomputable section
open MeasureTheory Set
open scoped Convolution

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianConvolution (b : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f z * Real.exp (-b * ‖x - z‖ ^ 2)

theorem gaussianConvolution_integrand_integrable {f : E → ℝ} (hf : Integrable f)
    {b : ℝ} (hb : 0 < b) (x : E) :
    Integrable (fun z => f z * Real.exp (-b * ‖x - z‖ ^ 2)) := by
  have he : Continuous (fun z => Real.exp (-b * ‖x - z‖ ^ 2)) := by fun_prop
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul he.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    change ‖f z * Real.exp (-b * ‖x - z‖ ^ 2)‖ ≤ ‖f z‖
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    have hk : Real.exp (-b * ‖x - z‖ ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hk (norm_nonneg (f z))

theorem gaussianConvolution_integrable {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianConvolution b f) := by
  exact hf.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (integrable_gaussian hb)

theorem gaussianConvolution_continuous {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Continuous (gaussianConvolution b f) := by
  have hbound : BddAbove (range fun x : E => ‖Real.exp (-b * ‖x‖ ^ 2)‖) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    change ‖Real.exp (-b * ‖x‖ ^ 2)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _)
  exact hbound.continuous_convolution_right_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℝ) hf (by fun_prop)

theorem gaussianConvolution_nonneg {f : E → ℝ} (hf : ∀ z, 0 ≤ f z) (b : ℝ) (x : E) :
    0 ≤ gaussianConvolution b f x :=
  integral_nonneg fun z => mul_nonneg (hf z) (Real.exp_pos _).le

theorem gaussianConvolution_pos {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z)
    (hmass : 0 < ∫ z, f z) {b : ℝ} (hb : 0 < b) (x : E) :
    0 < gaussianConvolution b f x := by
  have hs : Function.support (fun z => f z * Real.exp (-b * ‖x - z‖ ^ 2)) = Function.support f := by
    ext z
    simp only [Function.mem_support, mul_ne_zero_iff]
    exact ⟨And.left, fun hz => ⟨hz, (Real.exp_pos _).ne'⟩⟩
  rw [gaussianConvolution, integral_pos_iff_support_of_nonneg
    (fun z => mul_nonneg (hf0 z) (Real.exp_pos _).le)
    (gaussianConvolution_integrand_integrable hf hb x), hs]
  exact (integral_pos_iff_support_of_nonneg hf0 hf).mp hmass

theorem integral_gaussianConvolution {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    ∫ x, gaussianConvolution b f x =
      (∫ z, f z) * (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ) := by
  change (∫ x, (f ⋆[ContinuousLinearMap.mul ℝ ℝ]
    (fun y : E => Real.exp (-b * ‖y‖ ^ 2))) x) = _
  rw [integral_convolution _ hf (integrable_gaussian hb)]
  change (∫ z, f z) * (∫ y : E, Real.exp (-b * ‖y‖ ^ 2)) = _
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]

/-- Nonnegative data supported in a ball have an explicit Gaussian tail.-/
theorem gaussianConvolution_le_of_support_bound {f : E → ℝ} (hf : Integrable f)
    (hf0 : ∀ z, 0 ≤ f z) {R : ℝ} (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R)
    {b : ℝ} (hb : 0 < b) (x : E) :
    gaussianConvolution b f x ≤
      (∫ z, f z) * (Real.exp (b * R ^ 2) * Real.exp (-(b / 2) * ‖x‖ ^ 2)) := by
  rw [← integral_mul_const]
  apply integral_mono (gaussianConvolution_integrand_integrable hf hb x) (hf.mul_const _)
  intro z
  by_cases hz : f z = 0
  · simp only [hz, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (gaussian_shift_le_uniform x z (hsupport z hz) hb.le) (hf0 z)

/-- The Gaussian convolution normalized to have the same mass as its input.-/
def gaussianRegularization (b : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  gaussianConvolution b f x / (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ)

theorem gaussianRegularization_integrable {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianRegularization b f) :=
  (gaussianConvolution_integrable hf hb).div_const _

theorem gaussianRegularization_continuous {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Continuous (gaussianRegularization b f) :=
  (gaussianConvolution_continuous hf hb).div_const _

theorem gaussianRegularization_pos {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z)
    (hmass : 0 < ∫ z, f z) {b : ℝ} (hb : 0 < b) (x : E) :
    0 < gaussianRegularization b f x :=
  div_pos (gaussianConvolution_pos hf hf0 hmass hb x)
    (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _)

theorem integral_gaussianRegularization {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    ∫ x, gaussianRegularization b f x = ∫ z, f z := by
  simp only [gaussianRegularization, div_eq_mul_inv, integral_mul_const, integral_gaussianConvolution hf hb]
  exact mul_inv_cancel_right₀ (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne' _

end GeometricBrascampLieb
