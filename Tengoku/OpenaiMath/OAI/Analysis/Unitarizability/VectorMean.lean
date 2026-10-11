import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.Average
import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.Model
import Tengoku

namespace OAI

/-! Vector means and their translation error bounds. -/
noncomputable section
namespace Dixmier
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [Group G] [TopologicalSpace G] in
theorem summable_l2_sq (ξ : ScalarL2 G) : Summable (fun x => ‖ξ x‖ ^ 2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num)

def vectorMeanValue (ξ : ScalarL2 G) (b : G →ᵇ ℂ) : ℂ :=
  ∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)

theorem vectorMean_summable (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    Summable (fun x => (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹) : G → ℂ) := by
  apply Summable.of_norm_bounded ((summable_l2_sq ξ).mul_right ‖b‖)
  intro x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
  exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)

theorem vectorMean_norm_le (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    ‖vectorMeanValue ξ b‖ ≤ ‖ξ‖ ^ 2 * ‖b‖ := by
  have hb : ∀ x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ ≤ ‖ξ x‖ ^ 2 * ‖b‖ := by
    intro x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)
  calc
    ‖vectorMeanValue ξ b‖ ≤ ∑' x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ :=
      norm_tsum_le_tsum_norm (vectorMean_summable ξ b).norm
    _ ≤ ∑' x, ‖ξ x‖ ^ 2 * ‖b‖ :=
      Summable.tsum_le_tsum hb (vectorMean_summable ξ b).norm ((summable_l2_sq ξ).mul_right ‖b‖)
    _ = ‖ξ‖ ^ 2 * ‖b‖ := by rw [tsum_mul_right, ← l2_norm_sq]

def vectorMeanLinear (ξ : ScalarL2 G) : (G →ᵇ ℂ) →ₗ[ℂ] ℂ where
  toFun := vectorMeanValue ξ
  map_add' b c := by
    simp only [vectorMeanValue, BoundedContinuousFunction.add_apply, mul_add]
    exact (vectorMean_summable ξ b).tsum_add (vectorMean_summable ξ c)
  map_smul' z b := by
    simp only [vectorMeanValue, BoundedContinuousFunction.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm _ z, mul_assoc]
    exact tsum_mul_left

def vectorMean (ξ : ScalarL2 G) : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  (vectorMeanLinear ξ).mkContinuous (‖ξ‖ ^ 2) (vectorMean_norm_le ξ)

@[simp] theorem vectorMean_apply (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    vectorMean ξ b = vectorMeanValue ξ b := rfl

theorem vectorMean_one (ξ : ScalarL2 G) :
    vectorMean ξ (BoundedContinuousFunction.const G 1) = (‖ξ‖ ^ 2 : ℝ) := by
  simp only [vectorMean_apply, vectorMeanValue, BoundedContinuousFunction.const_apply, mul_one]
  rw [← Complex.ofReal_tsum, ← l2_norm_sq]

theorem vectorMean_opNorm_le (ξ : ScalarL2 G) : ‖vectorMean ξ‖ ≤ ‖ξ‖ ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) (vectorMean_norm_le ξ)

theorem vectorMean_positive (ξ : ScalarL2 G) (b : G →ᵇ ℂ)
    (hb : ∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) :
    0 ≤ (vectorMean ξ b).re ∧ (vectorMean ξ b).im = 0 := by
  change 0 ≤ (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).re ∧
    (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).im = 0
  rw [Complex.re_tsum (vectorMean_summable ξ b), Complex.im_tsum (vectorMean_summable ξ b)]
  constructor
  · apply tsum_nonneg
    intro x
    simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_nonneg (sq_nonneg ‖ξ x‖) (hb x⁻¹).1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, fun x => (hb x).2, mul_zero, tsum_zero]

end Dixmier

end

end OAI
