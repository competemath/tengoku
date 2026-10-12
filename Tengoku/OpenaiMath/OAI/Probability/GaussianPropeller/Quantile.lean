import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.HeatConvolution

namespace OAI

universe uX

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

namespace GaussianPropeller.Quantile

noncomputable def φ (x : ℝ) : ℝ := (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-x^2/2)
noncomputable def Φ (x : ℝ) : ℝ := ∫ y in Iic x, φ y

lemma φ_pos (x : ℝ) : 0 < φ x := by unfold φ; positivity
lemma φ_neg (x : ℝ) : φ (-x) = φ x := by simp [φ]
lemma integrable_φ : Integrable φ := by
  unfold φ
  have h := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  simpa only [φ, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring] using
    h.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
lemma integral_φ : ∫ x, φ x = 1 := by
  unfold φ
  rw [integral_const_mul]
  simp_rw [show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
  rw [integral_gaussian]
  have hp : Real.pi/(1/2:ℝ) = 2*Real.pi := by ring
  rw [hp, inv_mul_cancel₀ (by positivity)]
lemma Φ_pos (x : ℝ) : 0 < Φ x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun x => (φ_pos x).le))
    integrable_φ.integrableOn).mpr
  simp [Function.support, ne_of_gt (φ_pos _)]
lemma Φ_eq_one_sub_tail (x : ℝ) : Φ x = 1 - ∫ y in Ioi x, φ y := by
  have h := integral_add_compl measurableSet_Iic integrable_φ (s := Iic x)
  rw [compl_Iic, integral_φ] at h
  unfold Φ
  linarith only [h]
lemma Φ_neg (x : ℝ) : Φ (-x) = 1-Φ x := by
  have h := integral_comp_neg_Iic (-x) φ
  simp only [φ_neg, neg_neg] at h
  change Φ (-x) = (∫ y in Ioi x, φ y) at h
  rw [h, Φ_eq_one_sub_tail]
  ring
lemma Φ_lt_one (x : ℝ) : Φ x < 1 := by
  have h := Φ_pos (-x)
  rw [Φ_neg] at h
  linarith only [h]
lemma Φ_mem (x : ℝ) : Φ x ∈ Ioo (0:ℝ) 1 := ⟨Φ_pos x, Φ_lt_one x⟩
lemma Φ_zero : Φ 0 = 1/2 := by
  have h := Φ_neg 0
  simp only [neg_zero] at h
  linarith only [h]
lemma tendsto_Φ_atTop : Tendsto Φ atTop (𝓝 1) := by
  have ht := tendsto_integral_Ioi_zero (f := φ) (μ := volume) tendsto_id
  convert ht.const_sub 1 using 1
  · exact funext Φ_eq_one_sub_tail
  · norm_num
lemma tendsto_Φ_atBot : Tendsto Φ atBot (𝓝 0) := by
  have ht := tendsto_Φ_atTop.comp tendsto_neg_atBot_atTop
  have hh := ht.const_sub 1
  simpa only [Function.comp_def, Φ_neg, sub_sub_cancel, sub_self] using hh

lemma concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) :
    f y ≤ f x+d*(y-x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']

lemma φ_le_zero (x : ℝ) : φ x ≤ φ 0 := by
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

end Integration
end GaussianPropeller.Quantile

end OAI
