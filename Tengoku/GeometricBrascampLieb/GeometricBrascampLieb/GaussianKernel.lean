import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianCompactBounds
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.LinearAlgebra.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Derivatives and global bounds for the Gaussian kernel

The first two spatial derivatives and the derivative in the inverse-width
parameter have polynomial Gaussian bounds. These justify differentiating
convolutions with arbitrary integrable initial data.
-/

noncomputable section

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussianKernel (b : ℝ) (x : E) : ℝ := Real.exp (-b * ‖x‖ ^ 2)

def gaussianKernelGradient (b : ℝ) (x : E) : E := (-2 * b * gaussianKernel b x) • x

def gaussianKernelHessian (b : ℝ) (x : E) : E →L[ℝ] E :=
  (-2 * b * gaussianKernel b x) • ContinuousLinearMap.id ℝ E +
    (4 * b ^ 2 * gaussianKernel b x) • (innerSL ℝ x).smulRight x

theorem gaussianKernel_hasFDerivAt (b : ℝ) (x : E) :
    HasFDerivAt (gaussianKernel b) (innerSL ℝ (gaussianKernelGradient b x)) x := by
  have h := (((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).const_mul (-b)).exp
  apply h.congr_fderiv
  ext y
  simp only [gaussianKernelGradient, gaussianKernel, map_smul, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    innerSL_apply_apply, id_eq]
  ring

theorem gaussianKernelGradient_hasFDerivAt (b : ℝ) (x : E) :
    HasFDerivAt (gaussianKernelGradient b) (gaussianKernelHessian b x) x := by
  have h := ((gaussianKernel_hasFDerivAt b x).const_mul (-2 * b)).fun_smul
    (hasFDerivAt_id (𝕜 := ℝ) x)
  apply h.congr_fderiv
  ext y
  simp only [gaussianKernelHessian, gaussianKernelGradient, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, real_inner_smul_left, smul_smul]
  congr 1
  congr 1
  ring

omit [InnerProductSpace ℝ E] in
theorem gaussianKernel_hasDerivAt (b : ℝ) (x : E) :
    HasDerivAt (fun a => gaussianKernel a x) (-‖x‖ ^ 2 * gaussianKernel b x) b := by
  have h : HasDerivAt (fun a : ℝ => -a * ‖x‖ ^ 2) (-‖x‖ ^ 2) b := by
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul] using
      (hasDerivAt_id b).neg.mul_const (‖x‖ ^ 2)
  exact h.exp.congr_deriv (mul_comm _ _)

omit [InnerProductSpace ℝ E] in
theorem gaussianKernel_continuous (b : ℝ) : Continuous (gaussianKernel b : E → ℝ) := by
  unfold gaussianKernel
  fun_prop

theorem gaussianKernelGradient_continuous (b : ℝ) :
    Continuous (gaussianKernelGradient b : E → E) := by
  unfold gaussianKernelGradient
  exact (continuous_const.mul (gaussianKernel_continuous b)).smul continuous_id

theorem gaussianKernelHessian_continuous (b : ℝ) :
    Continuous (gaussianKernelHessian b : E → E →L[ℝ] E) := by
  have hr : Continuous (fun x : E => (innerSL ℝ x).smulRight x) :=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
      (innerSL ℝ).continuous).clm_apply continuous_id
  exact ((continuous_const.mul (gaussianKernel_continuous b)).smul continuous_const).add
    ((continuous_const.mul (gaussianKernel_continuous b)).smul hr)

omit [InnerProductSpace ℝ E] in
theorem gaussianKernel_le_one {b : ℝ} (hb : 0 ≤ b) (x : E) : gaussianKernel b x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _)

omit [InnerProductSpace ℝ E] in
theorem norm_pow_mul_gaussianKernel_le (n : ℕ) {b : ℝ} (hb : 0 < b) (x : E) :
    ‖x‖ ^ n * gaussianKernel b x ≤ 1 + (n.factorial : ℝ) / (b / 2) ^ n := by
  exact (pow_mul_gaussian_le ‖x‖ n hb).trans (by
    simpa only [mul_one, gaussianKernel] using mul_le_mul_of_nonneg_left
      (gaussianKernel_le_one (half_pos hb).le x) (by positivity))

theorem gaussianKernelGradient_norm_le {b : ℝ} (hb : 0 < b) (x : E) :
    ‖gaussianKernelGradient b x‖ ≤ 2 * b * (1 + 1 / (b / 2)) := by
  have h := norm_pow_mul_gaussianKernel_le 1 hb x
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h
  calc
    _ = (2 * b) * (‖x‖ * gaussianKernel b x) := by
      simp only [gaussianKernelGradient, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_pos hb, abs_of_pos (Real.exp_pos _), gaussianKernel]
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem gaussianKernelHessian_norm_le {b : ℝ} (hb : 0 < b) (x : E) :
    ‖gaussianKernelHessian b x‖ ≤
      2 * b + 4 * b ^ 2 * (1 + 2 / (b / 2) ^ 2) := by
  have h2 := norm_pow_mul_gaussianKernel_le 2 hb x
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul] at h2
  have hk : 0 ≤ gaussianKernel b x := (Real.exp_pos _).le
  calc
    _ ≤ ‖(-2 * b * gaussianKernel b x) • ContinuousLinearMap.id ℝ E‖ +
        ‖(4 * b ^ 2 * gaussianKernel b x) • (innerSL ℝ x).smulRight x‖ := norm_add_le _ _
    _ ≤ (2 * b * gaussianKernel b x) * 1 +
        (4 * b ^ 2 * gaussianKernel b x) * (‖x‖ * ‖x‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hb,
        abs_of_nonneg hk, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      norm_num only [abs_neg, abs_pow, abs_of_pos hb]
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = 2 * b * gaussianKernel b x + 4 * b ^ 2 * (‖x‖ ^ 2 * gaussianKernel b x) := by ring
    _ ≤ _ := add_le_add (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (gaussianKernel_le_one hb.le x) (by positivity : 0 ≤ 2*b))
      (mul_le_mul_of_nonneg_left h2 (by positivity))

variable [FiniteDimensional ℝ E]

theorem trace_gaussianKernelHessian (b : ℝ) (x : E) :
    LinearMap.trace ℝ E (gaussianKernelHessian b x).toLinearMap =
      (-2 * b * (Module.finrank ℝ E : ℝ) + 4 * b ^ 2 * ‖x‖ ^ 2) * gaussianKernel b x := by
  simp only [gaussianKernelHessian, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul,
    ContinuousLinearMap.coe_id, LinearMap.trace_id, smul_eq_mul]
  rw [show ((innerSL ℝ x).smulRight x).toLinearMap =
    (innerSL ℝ x).toLinearMap.smulRight x from rfl]
  rw [LinearMap.trace_smulRight, ContinuousLinearMap.toLinearMap_innerSL_apply,
    innerₛₗ_apply_apply, real_inner_self_eq_norm_sq]
  ring

end GeometricBrascampLieb
