import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.Koebe

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma integralMean_pos {f : ℂ → ℂ} (hf : UnivalentOn f disk) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) : 0 < integralMean f t r := by
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    (continuous_circle_deriv_rpow hf hr0 hr1 t).continuousOn
    (fun θ _ => Real.rpow_nonneg (norm_nonneg _) t)
  refine ⟨0,⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩,?_⟩
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball hf
    (circlePoint_mem_disk hr0 hr1 0))) t

lemma tendsto_log_boundary : Tendsto (fun r : ℝ => Real.log (1/(1-r))) (𝓝[<] (1:ℝ)) atTop := by
  have hδ : Tendsto (fun r : ℝ => 1-r) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun r : ℝ => 1-r) := continuous_const.sub continuous_id
      have h := hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (1:ℝ) ≤ 𝓝 1)
      simpa only [sub_self] using h
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (show r < 1 from hr)
  have h := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hδ)
  simpa only [Function.comp_def,one_div,Real.log_inv] using h

lemma eventually_radius : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), 1/2 ≤ r ∧ r < 1 := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num : (1/2:ℝ) < 1)),self_mem_nhdsWithin] with r hr hr1
  exact ⟨hr.le,hr1⟩

lemma log_power_upper {M C a r : ℝ} (hM : 0 < M) (hC : 0 < C)
    (hr : 0 < r) (hr1 : r < 1) (h : M ≤ C*(1-r)^(-a)) :
    Real.log M / Real.log (1/(1-r)) ≤ Real.log C / Real.log (1/(1-r)) + a := by
  have hd : 0 < 1-r := by linarith
  have hl : 0 < Real.log (1/(1-r)) := Real.log_pos ((one_lt_div hd).mpr (by linarith))
  have hb := Real.log_le_log hM h
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hd _).ne',Real.log_rpow hd] at hb
  have he : Real.log (1/(1-r)) = -Real.log (1-r) := by simp [one_div]
  rw [div_le_iff₀ hl]
  calc
    Real.log M ≤ Real.log C + (-a)*Real.log (1-r) := hb
    _ = (Real.log C / Real.log (1/(1-r))+a)*Real.log (1/(1-r)) := by
      rw [add_mul,div_mul_cancel₀ _ hl.ne',he]; ring

lemma koebe_beta_ge_one : 1 ≤ beta koebeMap (-2) := by
  let C : ℝ := 1/(4*Real.pi)
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : Tendsto (fun r : ℝ => ((Real.log C/Real.log (1/(1-r))+1:ℝ):EReal))
      (𝓝[<] (1:ℝ)) (𝓝 (1:EReal)) := by
    have hh := (tendsto_log_boundary.const_div_atTop (Real.log C)).add_const 1
    simpa [Function.comp_def] using continuous_coe_real_ereal.continuousAt.tendsto.comp hh
  rw [← hc.limsup_eq]
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_radius] with r hr
  apply EReal.coe_le_coe
  have hd : 0 < 1-r := by linarith [hr.2]
  have hl : 0 < Real.log (1/(1-r)) := Real.log_pos ((one_lt_div hd).mpr (by linarith [hr.1]))
  have hb := koebe_mean_lower hr.1 hr.2
  have hid : 1/(4*Real.pi*(1-r)) = C*(1/(1-r)) := by dsimp [C]; field_simp
  rw [hid] at hb
  have hh := Real.log_le_log (mul_pos hC (by positivity)) hb
  rw [Real.log_mul hC.ne' (by positivity)] at hh
  rw [le_div_iff₀ hl,add_mul,div_mul_cancel₀ _ hl.ne',one_mul]
  exact hh

end Brennan

end

end OAI
