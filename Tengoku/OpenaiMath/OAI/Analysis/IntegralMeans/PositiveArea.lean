import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.SmoothMeans

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma continuousOn_smoothPower_comp {f : ℂ → ℂ} (hf : Schlicht f) (a : ℝ) :
    ContinuousOn (fun z => smoothPower a (f z)) disk :=
  (smoothPower_contDiff a 0).continuous.comp_continuousOn hf.1.1.continuousOn

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma bracketSq_negative_integrable {η : ℝ} (hη : 0 < η) :
    Integrable (fun z : ℂ => bracketSq z^(-1-η)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 2+2*η)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring

lemma schlicht_weighted_derivative_integrable {f : ℂ → ℂ} (hf : Schlicht f) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)) disk := by
  have hc : ContinuousOn (fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)) disk :=
    ((continuousOn_deriv_univalent hf.1).norm.pow 2).mul (continuousOn_smoothPower_comp hf _)
  have hn : ∀ z : ℂ, 0 ≤ ‖deriv f z‖^2*bracketSq (f z)^(-1-η) :=
    fun z => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _)
  refine ⟨hc.aestronglyMeasurable Metric.isOpen_ball.measurableSet,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr
  have hh := conformal_lintegral_le Metric.isOpen_ball.measurableSet
    (fun z hz => hf.1.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hf.1.2
    (fun w => ENNReal.ofReal (bracketSq w^(-1-η)))
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)] at hh
  refine lt_of_le_of_lt hh ?_
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun z : ℂ => Real.rpow_nonneg (bracketSq_pos z).le (-1-η)))).mp
      (bracketSq_negative_integrable hη).hasFiniteIntegral

end Brennan

end

end OAI
