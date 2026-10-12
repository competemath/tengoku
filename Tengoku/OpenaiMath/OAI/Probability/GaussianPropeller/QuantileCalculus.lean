import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.Quantile

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

open scoped RealInnerProductSpace
namespace GaussianPropeller.QuantilePDE
open GaussianPropeller.Quantile

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma trace_quantile_hessian {ι : Type uι} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (v a : ℝ) (g : E) (K : E →L[ℝ] E) :
    (∑ i : ι, (a*⟪K (e i),e i⟫ + v*a^2*⟪g,e i⟫^2)) - v*‖a • g‖^2 =
      a*(∑ i : ι, ⟪K (e i),e i⟫) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    e.sum_sq_inner_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end GaussianPropeller.QuantilePDE

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma abs_mul_φ_le (a : ℝ) : |a| *φ a ≤ φ 0 := by
  have hsq : |a| ≤ 1+a^2/2 := by nlinarith [sq_nonneg (|a|-1), sq_abs a]
  have he : |a| ≤ Real.exp (a^2/2) := hsq.trans (by nlinarith [Real.add_one_le_exp (a^2/2)])
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a^2/2)).le
  rw [← Real.exp_add] at hh
  have heq : a^2/2 + -a^2/2 = 0 := by ring
  rw [heq, Real.exp_zero] at hh
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹)]

noncomputable def grad (f : E → ℝ) (g : E → E) (x : E) : E := φ (f x) • g x
noncomputable def hess (f : E → ℝ) (g : E → E) (K : E → E →L[ℝ] E) (x : E) : E →L[ℝ] E :=
  φ (f x) • K x - (f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cdf_bound [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : ‖Φ (f x)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact (Φ_lt_one _).le

lemma grad_bound {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : ∀ x, ‖g x‖ ≤ L) (x : E) : ‖grad f g x‖ ≤ φ 0*L := by
  rw [grad, norm_smul, Real.norm_eq_abs, abs_of_pos (φ_pos _)]
  exact mul_le_mul (φ_le_zero _) (hL x) (norm_nonneg _) (φ_pos _).le

lemma hess_bound {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E} {L D : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D) (x : E) :
    ‖hess f g K x‖ ≤ φ 0*(D+L^2) := by
  have hD0 : 0 ≤ D := (norm_nonneg (K x)).trans (hD x)
  calc
    ‖hess f g K x‖ ≤ ‖φ (f x) • K x‖ +
        ‖(f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))‖ := norm_sub_le _ _
    _ = φ (f x)*‖K x‖ + (|f x| *φ (f x))*‖g x‖^2 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (φ_pos _), abs_mul, abs_of_pos (φ_pos _),
        ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      ring
    _ ≤ φ 0*D + φ 0*L^2 := add_le_add
      (mul_le_mul (φ_le_zero _) (hD x) (norm_nonneg _) (φ_pos _).le)
      (mul_le_mul (abs_mul_φ_le _) ((sq_le_sq₀ (norm_nonneg _) hL0).2 (hL x))
        (sq_nonneg _) (φ_pos _).le)
    _ = _ := by ring

end GaussianPropeller.SmoothCDF

end OAI
