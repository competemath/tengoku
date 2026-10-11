import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.GaussianPoincare

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianCDF
local notation "μ" => gaussianReal 0 1
def Φ (x : ℝ) : ℝ := cdf μ x
def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma φ_pos (x : ℝ) : 0 < φ x := gaussianPDFReal_pos _ _ _ (by norm_num)
lemma φ_contDiff : ContDiff ℝ ∞ φ := by unfold φ gaussianPDFReal; fun_prop
lemma φ_integrable : Integrable φ := integrable_gaussianPDFReal _ _
lemma Φ_integral (x : ℝ) : Φ x = ∫ t in Iic x, φ t := by
  rw [Φ, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun t => gaussianPDFReal_nonneg (0:ℝ) 1 t))

lemma Φ_primitive (x : ℝ) : Φ x = Φ 0 + ∫ t in (0:ℝ)..x, φ t := by
  rw [Φ_integral, Φ_integral]
  have h := intervalIntegral.integral_Iic_sub_Iic
    (φ_integrable.integrableOn (s := Iic 0)) (φ_integrable.integrableOn (s := Iic x))
  linarith

def ψ (x : ℝ) : ℝ := 2*Φ x-1

lemma ψ_deriv_bound (x : ℝ) : |2*φ x| ≤ 1 := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hge : 2 ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.pi_gt_three]
  have he : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have he0 : 0 ≤ Real.exp (-x^2/2) := (Real.exp_pos _).le
  rw [abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (φ_pos x))]
  change 2*((Real.sqrt (2*Real.pi*1))⁻¹*Real.exp (-(x-0)^2/(2*1))) ≤ 1
  simp only [mul_one, sub_zero]
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹*(2*Real.exp (-x^2/2)) := by ring
    _ ≤ 1 := (inv_mul_le_iff₀ hs).mpr (by nlinarith)

def uniform : Measure ℝ := (2:ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1:ℝ) 1)

end UniformSparsestCut.GaussianCDF

end

end OAI
