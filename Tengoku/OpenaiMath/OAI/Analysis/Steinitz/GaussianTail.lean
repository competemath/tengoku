import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.Scales

namespace OAI

/-! Scalar and matrix Gaussian tail estimates. -/

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace GaussianTail

lemma integral_exp_square (t : ℝ) :
    (∫ x : ℝ, Real.exp (-t * x ^ 2 / 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (-t * x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 + t) / 2) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [smul_eq_mul, he, integral_const_mul, integral_gaussian]
  rw [show Real.pi / ((1 + t) / 2) = (2 * Real.pi) / (1 + t) by rw [div_div_eq_mul_div]; ring]
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hp : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma integrable_exp_square {t : ℝ} (ht : -1 < t) :
    Integrable (fun x : ℝ => Real.exp (-t * x ^ 2 / 2)) (gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_square t]
  exact ne_of_gt (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith)))

lemma inverse_sqrt_one_sub_le_exp {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/2) :
    (Real.sqrt (1-u))⁻¹ ≤ Real.exp u := by
  have hpos : 0 < 1-u := by linarith
  have hlog : -Real.log (1-u) ≤ 2*u := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have hi : (1-u)⁻¹ - 1 ≤ 2*u := by
      rw [inv_eq_one_div]
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hpos).mpr
      nlinarith
    exact h.trans hi
  apply (Real.log_le_log_iff (inv_pos.mpr (Real.sqrt_pos.mpr hpos)) (Real.exp_pos u)).mp
  rw [Real.log_inv, Real.log_sqrt hpos.le, Real.log_exp]
  linarith

open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_eigenbasis {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ) :
    ⟪∑ i, x i • hA.eigenvectorBasis i,
      toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ =
      ∑ i, hA.eigenvalues i * x i ^ 2 := by
  have he (i : ι) : toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  simp only [map_sum, map_smul, he, smul_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    hA.eigenvectorBasis.inner_eq_ite]
  simp [mul_ite, ite_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma quadratic_mgf_eq {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = ∏ i, (Real.sqrt (1-hA.eigenvalues i))⁻¹ := by
  have he (x : ι → ℝ) :
      Real.exp (⟪∑ i, x i • hA.eigenvectorBasis i,
        toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ / 2) =
      ∏ i, Real.exp (hA.eigenvalues i * x i ^ 2 / 2) := by
    rw [quadratic_eigenbasis, ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_div]
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [he]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => Real.exp (hA.eigenvalues i * x ^ 2 / 2))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [neg_neg, sub_eq_add_neg] using integral_exp_square (-hA.eigenvalues i)

lemma quadratic_mgf_integrable {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hEig : ∀ i, hA.eigenvalues i < 1) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  apply Integrable.of_integral_ne_zero
  rw [quadratic_mgf_eq hA]
  apply ne_of_gt
  exact Finset.prod_pos fun i _ => inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [hEig i]))

lemma eigenvalue_le_of_form_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {b : ℝ}
    (hb : ∀ x : EuclideanSpace ℝ ι, ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ b*‖x‖^2) :
    ∀ i, hA.eigenvalues i ≤ b := by
  intro i
  have h := hb (hA.eigenvectorBasis i)
  rw [hA.eigenvectorBasis.orthonormal.norm_eq_one, one_pow, mul_one] at h
  have he : toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  simpa [he, real_inner_smul_right, hA.eigenvectorBasis.inner_eq_ite] using h

end GaussianTail

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace GaussianTail
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

noncomputable def matrixMap (B : Matrix κ ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (Matrix.toEuclideanLin B).toContinuousLinearMap

noncomputable def squareMass (B : Matrix κ ι ℝ) : ℝ := ∑ i,∑ j,B i j^2

omit [DecidableEq ι] in
lemma squareMass_nonneg (B : Matrix κ ι ℝ) : 0 ≤ squareMass B := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gram_form (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x,toEuclideanCLM (𝕜 := ℝ) (B.transpose*B) x⟫ = ‖matrixMap B x‖^2 := by
  rw [inner_toEuclideanCLM,← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [← real_inner_self_eq_norm_sq]
  rfl

omit [DecidableEq ι] in
lemma gram_trace (B : Matrix κ ι ℝ) : (B.transpose*B).trace = squareMass B := by
  change (∑ i,∑ j,B j i*B j i) = ∑ i,∑ j,B i j^2
  simp only [← sq]
  exact Finset.sum_comm

lemma norm_sq_le_squareMass (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    ‖matrixMap B x‖^2 ≤ squareMass B*‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i,(∑ j,B i j*x j)^2) ≤ (∑ i,∑ j,B i j^2)*(∑ j,x j^2)
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma interpolated_form (B : Matrix κ ι ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hS : squareMass B ≤ v) (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ 4*‖x‖^2) :
    ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ (2*Real.sqrt v)*‖x‖^2 := by
  intro x
  by_cases h : v ≤ 4
  · apply (norm_sq_le_squareMass B x).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply hS.trans
    have hs := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg v
    have hle : Real.sqrt v ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
    nlinarith
  · apply (hB x).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hs := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg v
    have hle : 2 ≤ Real.sqrt v := (Real.le_sqrt (by norm_num) hv).mpr (by linarith)
    linarith

end GaussianTail

end

end OAI
