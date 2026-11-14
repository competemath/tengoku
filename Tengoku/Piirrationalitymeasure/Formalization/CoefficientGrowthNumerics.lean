import Tengoku.Piirrationalitymeasure.Formalization.CoefficientGrowth
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientSaddleAlgebra
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientLogCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The printed strict coefficient-rate enclosure (4.12). -/

namespace PiIrrationality

@[simp] theorem coefficientZLowerRat_cast :
    (coefficientZLowerRat : ℝ) = coefficientSaddleLower := by
  norm_num [coefficientZLowerRat, coefficientSaddleLower]

@[simp] theorem coefficientZUpperRat_cast :
    (coefficientZUpperRat : ℝ) = coefficientSaddleUpper := by
  norm_num [coefficientZUpperRat, coefficientSaddleUpper]

@[simp] theorem coefficientPRat_cast (z : ℚ) :
    (coefficientPRat z : ℝ) = PReal (z : ℝ) := by
  unfold coefficientPRat PReal
  push_cast
  rfl

theorem coefficientGrowthRate_eq_log_terms :
    coefficientGrowthRate = (Real.log 25 + 3716 * Real.log 2 +
      3714 * Real.log (1 + coefficientSaddle) + 3714 * Real.log (PReal coefficientSaddle) -
      7430 * Real.log (1 - coefficientSaddle) - 5570 * Real.log coefficientSaddle) / 5570 := by
  have hx0 := coefficientSaddle_mem.1
  have hx1 := coefficientSaddle_mem.2
  have hp : 0 < 1 + coefficientSaddle := by linarith
  have hm : 0 < 1 - coefficientSaddle := by linarith
  have hP := PReal_strictPositive coefficientSaddle hx0.le
  unfold coefficientGrowthRate SReal
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hp.ne') (pow_ne_zero _ hP.ne'))
    (pow_ne_zero _ hm.ne'), Real.log_mul (pow_ne_zero _ hp.ne') (pow_ne_zero _ hP.ne'),
    Real.log_pow, Real.log_pow, Real.log_pow]
  norm_num
  ring

theorem coefficientGrowthRate_enclosure :
    (333194398617829933828283250382326 : ℝ) / 10 ^ 32 < coefficientGrowthRate ∧
      coefficientGrowthRate < (333194398617829933828283250382327 : ℝ) / 10 ^ 32 := by
  have h0 := abs_lt.mp (coefficientLog_enclosure 0)
  have h1 := abs_lt.mp (coefficientLog_enclosure 1)
  have h2 := abs_lt.mp (coefficientLog_enclosure 2)
  have h3 := abs_lt.mp (coefficientLog_enclosure 3)
  have h4 := abs_lt.mp (coefficientLog_enclosure 4)
  have h5 := abs_lt.mp (coefficientLog_enclosure 5)
  have h6 := abs_lt.mp (coefficientLog_enclosure 6)
  have h7 := abs_lt.mp (coefficientLog_enclosure 7)
  have h8 := abs_lt.mp (coefficientLog_enclosure 8)
  have h9 := abs_lt.mp (coefficientLog_enclosure 9)
  norm_num [coefficientLogInput, coefficientLogRounded] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨hzL, hzU⟩ := coefficientSaddle_fine_bounds
  have hz0 := coefficientSaddle_mem.1
  have hz1 := coefficientSaddle_mem.2
  have hL0 : 0 < coefficientSaddleLower := by norm_num [coefficientSaddleLower]
  have hU1 : coefficientSaddleUpper < 1 := by norm_num [coefficientSaddleUpper]
  have hplusL : Real.log (1 + coefficientSaddleLower) ≤ Real.log (1 + coefficientSaddle) :=
    Real.log_le_log (by positivity) (by linarith)
  have hplusU : Real.log (1 + coefficientSaddle) ≤ Real.log (1 + coefficientSaddleUpper) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpolyL : Real.log (PReal coefficientSaddleLower) ≤
      Real.log (PReal coefficientSaddle) := by
    apply Real.log_le_log (PReal_strictPositive _ hL0.le)
    unfold PReal
    gcongr
  have hpolyU : Real.log (PReal coefficientSaddle) ≤
      Real.log (PReal coefficientSaddleUpper) := by
    apply Real.log_le_log (PReal_strictPositive _ hz0.le)
    unfold PReal
    gcongr
  have hminusL : Real.log (1 - coefficientSaddleUpper) ≤
      Real.log (1 - coefficientSaddle) := Real.log_le_log (by linarith) (by linarith)
  have hminusU : Real.log (1 - coefficientSaddle) ≤
      Real.log (1 - coefficientSaddleLower) := Real.log_le_log (by linarith) (by linarith)
  have hzlogL : Real.log coefficientSaddleLower ≤ Real.log coefficientSaddle :=
    Real.log_le_log hL0 hzL.le
  have hzlogU : Real.log coefficientSaddle ≤ Real.log coefficientSaddleUpper :=
    Real.log_le_log hz0 hzU.le
  rw [coefficientGrowthRate_eq_log_terms]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h3.2,
    h4.1, h5.2, h6.2, h7.1, h8.1, h9.2]

end PiIrrationality
