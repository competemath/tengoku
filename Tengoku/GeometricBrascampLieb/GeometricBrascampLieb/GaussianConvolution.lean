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

/--
@isnad1 id=integrab.2h4v.s7.7314779b6208 from=translated src=- shape=76943242 vocab=e32d20bb
-/
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

/--
@isnad1 id=integrab.2h3v.s7.39ee75b4c168 from=translated src=- shape=ab67ea45 vocab=66f4bf97
-/
theorem gaussianConvolution_integrable {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianConvolution b f) := by
  exact hf.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (integrable_gaussian hb)

/--
@isnad1 id=continuo.2h3v.s7.41f76ff7afc0 from=translated src=- shape=5add288e vocab=1775589d
-/
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

/--
@isnad1 id=le.1h4v.s6.526bc02eafc4 from=translated src=- shape=115f6c18 vocab=e2b6cef6
-/
theorem gaussianConvolution_nonneg {f : E → ℝ} (hf : ∀ z, 0 ≤ f z) (b : ℝ) (x : E) :
    0 ≤ gaussianConvolution b f x :=
  integral_nonneg fun z => mul_nonneg (hf z) (Real.exp_pos _).le

/--
@isnad1 id=lt.4h4v.s7.93e2dbf0e804 from=translated src=- shape=e5d733a5 vocab=9eef2d3d
-/
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

/--
@isnad1 id=eq.2h3v.s8.ac9b7a37462c from=translated src=- shape=39fea985 vocab=a95335df
-/
theorem integral_gaussianConvolution {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    ∫ x, gaussianConvolution b f x =
      (∫ z, f z) * (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ) := by
  change (∫ x, (f ⋆[ContinuousLinearMap.mul ℝ ℝ]
    (fun y : E => Real.exp (-b * ‖y‖ ^ 2))) x) = _
  rw [integral_convolution _ hf (integrable_gaussian hb)]
  change (∫ z, f z) * (∫ y : E, Real.exp (-b * ‖y‖ ^ 2)) = _
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]

/-- Nonnegative data supported in a ball have an explicit Gaussian tail.
@isnad1 id=le.4h5v.s8.c4d8be9c2435 from=translated src=- shape=830a5aee vocab=51e7549b
-/
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

/--
@isnad1 id=integrab.2h3v.s7.4c189e4e7ad0 from=translated src=- shape=ab67ea45 vocab=cb4c80f2
-/
theorem gaussianRegularization_integrable {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianRegularization b f) :=
  (gaussianConvolution_integrable hf hb).div_const _

/--
@isnad1 id=continuo.2h3v.s7.8d518b576ecc from=translated src=- shape=5add288e vocab=8c01d386
-/
theorem gaussianRegularization_continuous {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Continuous (gaussianRegularization b f) :=
  (gaussianConvolution_continuous hf hb).div_const _

/--
@isnad1 id=lt.4h4v.s7.bba4be3f75ae from=translated src=- shape=e5d733a5 vocab=5d349791
-/
theorem gaussianRegularization_pos {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z)
    (hmass : 0 < ∫ z, f z) {b : ℝ} (hb : 0 < b) (x : E) :
    0 < gaussianRegularization b f x :=
  div_pos (gaussianConvolution_pos hf hf0 hmass hb x)
    (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _)

/--
@isnad1 id=eq.2h3v.s7.569cb707c0e7 from=translated src=- shape=1f9c9a1f vocab=92f0c61c
-/
theorem integral_gaussianRegularization {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    ∫ x, gaussianRegularization b f x = ∫ z, f z := by
  simp only [gaussianRegularization, div_eq_mul_inv, integral_mul_const, integral_gaussianConvolution hf hb]
  exact mul_inv_cancel_right₀ (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne' _

end GeometricBrascampLieb
