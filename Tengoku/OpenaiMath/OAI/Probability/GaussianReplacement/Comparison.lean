import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Posterior

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma critical_entropy_scalars {d : ℕ} (hd : 1 ≤ d) {H E F : ℝ}
    (hH0 : 0 ≤ H) (hH : H ≤ (d:ℝ)^2)
    (hE : E ≤ 1+2*Real.log (20*((d:ℝ)+1+H)+1)) (hF0 : 0 ≤ F) (hF : F ≤ H+E) :
    E ≤ 127*(d:ℝ) ∧ Real.log (1+F) ≤ 131*(d:ℝ) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have hd2 : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hd21 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have harg : 20*((d:ℝ)+1+H)+1 ≤ 61*(d:ℝ)^2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0<20*((d:ℝ)+1+H)+1) harg
  rw [Real.log_mul (by norm_num : (61:ℝ) ≠ 0) (by positivity),Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hl61 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 61)
  have hld := Real.log_le_self hd0.le
  have hEb : E ≤ 127*(d:ℝ) := by nlinarith
  refine ⟨hEb,?_⟩
  have harg2 : 1+F ≤ 129*(d:ℝ)^2 := by nlinarith
  have hlog2 := Real.log_le_log (by positivity : 0<1+F) harg2
  rw [Real.log_mul (by norm_num : (129:ℝ) ≠ 0) (by positivity),Real.log_pow] at hlog2
  norm_num only [Nat.cast_ofNat] at hlog2
  have hl129 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 129)
  nlinarith

lemma critical_dimensions {d : ℕ} (hd : 100 ≤ d) :
    AdmissibleDimensions d (d/10) (d/2-d/10) (d/10) ∧ d/10+(d/2-d/10) ≤ d ∧
    d ≤ 20*(d/10) := by
  unfold AdmissibleDimensions
  omega

lemma uniformSphere_probability_of_pos {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (uniformSphere d) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  constructor
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero
    (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := Vector d)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

lemma level_entropy_scalars {d : ℕ} (hd : 1 ≤ d) {H E F : ℝ}
    (hH0 : 0 ≤ H) (hE : E ≤ 1+2*Real.log (20*((d:ℝ)+1+H)+1))
    (hF0 : 0 ≤ F) (hF : F ≤ H+E) :
    E ≤ 43+2*Real.log (1+(d:ℝ)+H) ∧ Real.log (1+F) ≤ 47+Real.log (1+(d:ℝ)+H) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have ht : (1:ℝ) ≤ 1+(d:ℝ)+H := by linarith
  have ht0 : (0:ℝ) < 1+(d:ℝ)+H := by linarith
  have harg : 20*((d:ℝ)+1+H)+1 ≤ 21*(1+(d:ℝ)+H) := by linarith
  have hl := Real.log_le_log (by positivity : 0<20*((d:ℝ)+1+H)+1) harg
  rw [Real.log_mul (by norm_num : (21:ℝ) ≠ 0) ht0.ne'] at hl
  have hl21 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 21)
  have he : E ≤ 43+2*Real.log (1+(d:ℝ)+H) := by linarith
  refine ⟨he,?_⟩
  have hlt := Real.log_le_self ht0.le
  have harg2 : 1+F ≤ 47*(1+(d:ℝ)+H) := by linarith
  have hl2 := Real.log_le_log (by positivity : 0<1+F) harg2
  rw [Real.log_mul (by norm_num : (47:ℝ) ≠ 0) ht0.ne'] at hl2
  linarith [Real.log_le_self (by norm_num : (0:ℝ) ≤ 47)]

lemma oneLevel_dimensions {d : ℕ} (hd : 100 ≤ d) :
    AdmissibleDimensions d (d/32) (d/4-d/32) (d/16) ∧
      d/32+(d/4-d/32) ≤ d ∧ d ≤ 32*(d/16) := by
  unfold AdmissibleDimensions
  omega

lemma twoLabel_dimensions {d : ℕ} (hd : 100 ≤ d) :
    AdmissibleDimensions d (d/8) (d/2-d/8) (d/8) ∧
      d/8+(d/2-d/8) ≤ d ∧ d ≤ 20*(d/8) := by
  unfold AdmissibleDimensions
  omega

end CurrentProjection

end

end OAI
