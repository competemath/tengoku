import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.EntropySeries
import Tengoku

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem large_parameter_gt_81 {u : ℝ} (hu0 : 0 ≤ u) (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    (81 / 100 : ℝ) < u := by
  by_contra h
  have hsq := pow_le_pow_left₀ hu0 (le_of_not_gt h) 2
  norm_num at hsq
  linarith

theorem entropy_eq_large_parameter_form {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    entropy u = (1 - u) * Real.artanh u + Real.log (1 + (1 - u) / (1 + u)) := by
  have hp : 0 < 1 + u := by linarith
  have heq : 1 + (1 - u) / (1 + u) = 2 / (1 + u) := by
    field_simp
    ring
  rw [heq, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne',
    artanh_eq_log_sub ⟨by linarith, hu1⟩]
  unfold entropy psi ell
  ring

theorem large_parameter_polynomial_bound {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ (5 / 11 : ℝ)) :
    (1 / 2 : ℝ) * (1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2 ≤ 2 / 3 := by
  have hfirst : (1 - y) * (1 + 10 * y / 9) ^ 2 ≤ (13718 / 10935 : ℝ) := by
    have hc : (13718 / 10935 : ℝ) - (1 - y) * (1 + 10 * y / 9) ^ 2 =
        (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) := by ring
    have hp : 0 ≤ (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hsecond : (1 + y) * (1 + 10 * y / 9) ^ 2 / 81 ≤
      (355216 / 8732691 : ℝ) := by
    calc
      _ ≤ (1 + (5 / 11 : ℝ)) * (1 + 10 * (5 / 11 : ℝ) / 9) ^ 2 / 81 := by
        gcongr
      _ = _ := by norm_num
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI
