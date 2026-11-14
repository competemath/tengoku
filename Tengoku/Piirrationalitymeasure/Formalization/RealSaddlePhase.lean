import Tengoku.Piirrationalitymeasure.Formalization.ArcPhase
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientGrowthNumerics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The real stationary phase is the actual coefficient rate used in Theorem 1.1. -/

namespace PiIrrationality

theorem complexPhase_ofReal_of_gt_twenty_five (alpha beta : ℝ) {y : ℝ} (hy : 25 < y) :
    complexPhase alpha beta (y : ℂ) =
      alpha * Real.log y + beta * Real.log (y ^ 2 + 6 * y + 25) - Real.log (y - 25) := by
  have hq : (y : ℂ) ^ 2 + 6 * y + 25 = ((y ^ 2 + 6 * y + 25 : ℝ) : ℂ) := by push_cast; rfl
  have hp : (25 : ℂ) - y = ((25 - y : ℝ) : ℂ) := by push_cast; rfl
  unfold complexPhase
  rw [hq, hp]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by linarith : 0 < y), abs_of_pos (by nlinarith : 0 < y ^ 2 + 6 * y + 25),
    abs_of_neg (by linarith : 25 - y < 0), neg_sub]

theorem real_phase_mobius (alpha beta : ℝ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    complexPhase alpha beta ((25 * (1 + z) ^ 2 / (1 - z) ^ 2 : ℝ) : ℂ) =
      (alpha + beta - 1) * Real.log 25 + (4 * beta - 2) * Real.log 2 +
      2 * alpha * Real.log (1 + z) + beta * Real.log (PReal z) +
      (-2 * alpha - 4 * beta + 2) * Real.log (1 - z) - Real.log z := by
  let y := 25 * (1 + z) ^ 2 / (1 - z) ^ 2
  have hplus : 0 < 1 + z := by linarith
  have hminus : 0 < 1 - z := by linarith
  have hP : 0 < PReal z := PReal_strictPositive z hz0.le
  have hyminus : y - 25 = 100 * z / (1 - z) ^ 2 := by
    dsimp [y]
    field_simp
    ring
  have hy : 25 < y := by
    have h : 0 < 100 * z / (1 - z) ^ 2 := by positivity
    linarith
  have hyquad : y ^ 2 + 6 * y + 25 = 400 * PReal z / (1 - z) ^ 4 := by
    dsimp [y, PReal]
    field_simp
    ring
  have hlog400 : Real.log 400 = Real.log 25 + 4 * Real.log 2 := by
    rw [show (400 : ℝ) = 25 * 2 ^ 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hlog100 : Real.log 100 = Real.log 25 + 2 * Real.log 2 := by
    rw [show (100 : ℝ) = 25 * 2 ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  change complexPhase alpha beta (y : ℂ) = _
  rw [complexPhase_ofReal_of_gt_twenty_five alpha beta hy, hyquad, hyminus]
  have hlogy : Real.log y = Real.log 25 + 2 * Real.log (1 + z) - 2 * Real.log (1 - z) := by
    unfold y
    rw [Real.log_div (mul_ne_zero (by norm_num) (pow_ne_zero _ hplus.ne'))
      (pow_ne_zero _ hminus.ne'), Real.log_mul (by norm_num) (pow_ne_zero _ hplus.ne'),
      Real.log_pow, Real.log_pow]
    norm_num
  rw [hlogy, Real.log_div (mul_ne_zero (by norm_num) hP.ne') (pow_ne_zero _ hminus.ne'),
    Real.log_mul (by norm_num) hP.ne', Real.log_pow,
    Real.log_div (mul_ne_zero (by norm_num) hz0.ne') (pow_ne_zero _ hminus.ne'),
    Real.log_mul (by norm_num) hz0.ne', Real.log_pow, hlog400, hlog100]
  ring

theorem realSaddle_phase_eq_coefficientGrowthRate :
    complexPhase (1857 / 5570) (3714 / 5570) (stationaryRoot : ℂ) = coefficientGrowthRate := by
  rw [coefficientSaddle_real_root,
    real_phase_mobius _ _ coefficientSaddle_mem.1 coefficientSaddle_mem.2,
    coefficientGrowthRate_eq_log_terms]
  ring

end PiIrrationality
