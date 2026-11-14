import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionZeroFreeRegion
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaZeroFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic conductor and height bounds for the zero-free region

The explicit analytic budgets are bounded by one absolute constant times
`1 + log q + log (|t|+4)`. The resulting narrower region retains the proved
per-character uniqueness, reality, and actual order-one conclusion.
-/

noncomputable section

namespace TwinPrime.Analytic

def zeroFreeLogConstant : ℝ := 144 * (1 + Real.log 5 / Real.log (6 / 5))

/--
@isnad1 id=le.0h0v.s3.beafd0cfebd1 from=translated src=- shape=ff3a10fc vocab=1a46f709
-/
theorem zeroFreeLogConstant_ge : 144 ≤ zeroFreeLogConstant := by
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have hquot := div_nonneg h5 h65
  unfold zeroFreeLogConstant
  linarith

/--
@isnad1 id=lt.0h0v.s3.9c7dd3d5d3e3 from=translated src=- shape=ff3a10fc vocab=637b3361
-/
theorem zeroFreeLogConstant_pos : 0 < zeroFreeLogConstant := by
  have h := zeroFreeLogConstant_ge
  linarith

/--
@isnad1 id=le.0h2v.s6.e680de690fc7 from=translated src=- shape=50410fcb vocab=ab85798c
-/
theorem primitiveLFunctionLogBudget_le_log_abs (q : ℕ) (t : ℝ) :
    primitiveLFunctionLogBudget q t ≤
      zeroFreeLogConstant * (1 + Real.log 16 + 2 * Real.log q + Real.log (|t| + 4)) := by
  have hn : ‖(2 : ℂ) + Complex.I * t‖ ≤ |t| + 2 := by
    have h := norm_add_le (2 : ℂ) (Complex.I * t)
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hl : Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2) ≤ Real.log (|t| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  change zeroFreeLogConstant * _ ≤ _
  exact mul_le_mul_of_nonneg_left (by linarith) zeroFreeLogConstant_pos.le

/--
@isnad1 id=le.0h1v.s6.dbe750b4fc19 from=translated src=- shape=a06384cf vocab=c4cec830
-/
theorem log_abs_double_add_four_le (t : ℝ) :
    Real.log (|2 * t| + 4) ≤ 2 * Real.log (|t| + 4) := by
  have htwo : Real.log (2 : ℝ) ≤ Real.log (|t| + 4) :=
    Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)
  calc
    _ ≤ Real.log (2 * (|t| + 4)) :=
      Real.log_le_log (by positivity) (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
    _ = Real.log 2 + Real.log (|t| + 4) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ _ := by linarith

/-- The complete primitive budget has a uniform logarithmic conductor and
height bound; this is an actual estimate of the previously proved budget.
@isnad1 id=le.0h2v.s6.be5decd83c00 from=translated src=- shape=671aae29 vocab=e442f7c6
-/
theorem primitiveZeroFreeBudget_le_log_conductor_height (q : ℕ) (t : ℝ) :
    primitiveZeroFreeBudget q t ≤
      100 * zeroFreeLogConstant * (1 + Real.log q + Real.log (|t| + 4)) := by
  let C := zeroFreeLogConstant
  let L := Real.log (q : ℝ)
  let H := Real.log (|t| + 4)
  have hC : 144 ≤ C := zeroFreeLogConstant_ge
  have hC0 : 0 ≤ C := by linarith
  have hL : 0 ≤ L := Real.log_natCast_nonneg q
  have hH : 0 ≤ H := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have htwo : Real.log (2 : ℝ) ≤ H :=
    Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)
  have hfour : Real.log (4 : ℝ) ≤ H :=
    Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)
  have h16 : Real.log (16 : ℝ) ≤ 4 * H := by
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hdouble : Real.log (|2 * t| + 4) ≤ 2 * H := log_abs_double_add_four_le t
  have hK : primitiveLFunctionLogBudget q t ≤ C * (1 + 2 * L + 5 * H) := by
    have hk := primitiveLFunctionLogBudget_le_log_abs q t
    change primitiveLFunctionLogBudget q t ≤ C * (1 + Real.log 16 + 2 * L + H) at hk
    nlinarith [mul_le_mul_of_nonneg_left h16 hC0]
  have hK2 : primitiveLFunctionLogBudget q (2 * t) ≤ C * (1 + 2 * L + 6 * H) := by
    have hk := primitiveLFunctionLogBudget_le_log_abs q (2 * t)
    change primitiveLFunctionLogBudget q (2 * t) ≤
      C * (1 + Real.log 16 + 2 * L + Real.log (|2 * t| + 4)) at hk
    nlinarith [mul_le_mul_of_nonneg_left h16 hC0, mul_le_mul_of_nonneg_left hdouble hC0]
  have hK0 : primitiveLFunctionLogBudget q 0 ≤ C * (1 + 2 * L + 5 * H) := by
    have hk := primitiveLFunctionLogBudget_le_log_abs q 0
    simp only [abs_zero, zero_add] at hk
    change primitiveLFunctionLogBudget q 0 ≤ C * (1 + Real.log 16 + 2 * L + Real.log 4) at hk
    nlinarith [mul_le_mul_of_nonneg_left h16 hC0, mul_le_mul_of_nonneg_left hfour hC0]
  have hZ : zetaLogBudget (2 * t) ≤ C * (1 + 8 * H) := by
    have hz := zetaLogBudget_le_log_abs (2 * t)
    change zetaLogBudget (2 * t) ≤ C * (1 + Real.log 16 + 2 * Real.log (|2 * t| + 4)) at hz
    nlinarith [mul_le_mul_of_nonneg_left h16 hC0, mul_le_mul_of_nonneg_left hdouble hC0]
  have heq : primitiveZeroFreeBudget q t = 400 + 8 * primitiveLFunctionLogBudget q t +
      primitiveLFunctionLogBudget q (2 * t) + 4 * primitiveLFunctionLogBudget q 0 +
      zetaLogBudget (2 * t) + 2 * L := by
    unfold primitiveZeroFreeBudget nonquadraticZeroFreeBudget quadraticZeroFreeBudget
      nearOneZeroBudget L
    ring
  rw [heq]
  change _ ≤ 100 * C * (1 + L + H)
  have h400 : 400 ≤ 3 * C := by linarith
  have hCL : 2 * L ≤ C * L :=
    mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ C) hL
  nlinarith [mul_nonneg hC0 hL, mul_nonneg hC0 hH]

def primitiveLogZeroFreeWidth (q : ℕ) (t : ℝ) : ℝ :=
  1 / (4000 * zeroFreeLogConstant * (1 + Real.log q + Real.log (|t| + 4)))

/--
@isnad1 id=lt.0h2v.s4.f01a4a56d471 from=translated src=- shape=787c1379 vocab=f1092afa
-/
theorem primitiveLogZeroFreeWidth_pos (q : ℕ) (t : ℝ) :
    0 < primitiveLogZeroFreeWidth q t := by
  have hq := Real.log_natCast_nonneg q
  have ht : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_pos
  unfold primitiveLogZeroFreeWidth
  positivity

/--
@isnad1 id=le.0h2v.s3.388ba99e70c5 from=translated src=- shape=d802f31c vocab=c6325acc
-/
theorem primitiveLogZeroFreeWidth_le (q : ℕ) (t : ℝ) :
    primitiveLogZeroFreeWidth q t ≤ primitiveZeroFreeWidth q t := by
  have hR := (primitiveZeroFreeBudget_bounds q t).1
  have hbound := primitiveZeroFreeBudget_le_log_conductor_height q t
  unfold primitiveLogZeroFreeWidth primitiveZeroFreeWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 40 * primitiveZeroFreeBudget q t)
  nlinarith

/-- The principal zero-free budget has logarithmic height growth as well.
@isnad1 id=le.0h1v.s6.05693262fe72 from=translated src=- shape=da34ad71 vocab=37042792
-/
theorem zetaZeroFreeBudget_le_log_height (t : ℝ) :
    zetaZeroFreeBudget t ≤ 100 * zeroFreeLogConstant * (1 + Real.log (|t| + 4)) := by
  let C := zeroFreeLogConstant
  let H := Real.log (|t| + 4)
  have hC : 144 ≤ C := zeroFreeLogConstant_ge
  have hC0 : 0 ≤ C := by linarith
  have hH : 0 ≤ H := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have htwo : Real.log (2 : ℝ) ≤ H :=
    Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)
  have h16 : Real.log (16 : ℝ) ≤ 4 * H := by
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hdouble : Real.log (|2 * t| + 4) ≤ 2 * H := log_abs_double_add_four_le t
  have hZ : zetaLogBudget t ≤ C * (1 + 6 * H) := by
    have hz := zetaLogBudget_le_log_abs t
    change zetaLogBudget t ≤ C * (1 + Real.log 16 + 2 * H) at hz
    nlinarith [mul_le_mul_of_nonneg_left h16 hC0]
  have hZ2 : zetaLogBudget (2 * t) ≤ C * (1 + 8 * H) := by
    have hz := zetaLogBudget_le_log_abs (2 * t)
    change zetaLogBudget (2 * t) ≤ C * (1 + Real.log 16 + 2 * Real.log (|2 * t| + 4)) at hz
    nlinarith [mul_le_mul_of_nonneg_left h16 hC0, mul_le_mul_of_nonneg_left hdouble hC0]
  unfold zetaZeroFreeBudget
  change _ ≤ 100 * C * (1 + H)
  nlinarith [mul_nonneg hC0 hH]

def zetaLogZeroFreeWidth (t : ℝ) : ℝ :=
  1 / (8000 * zeroFreeLogConstant * (1 + Real.log (|t| + 4)))

/--
@isnad1 id=lt.0h1v.s3.d6f5ee5cea93 from=translated src=- shape=8a62b088 vocab=d5c53f26
-/
theorem zetaLogZeroFreeWidth_pos (t : ℝ) : 0 < zetaLogZeroFreeWidth t := by
  have ht : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_pos
  unfold zetaLogZeroFreeWidth
  positivity

/--
@isnad1 id=le.0h1v.s5.699eec7c2eac from=translated src=- shape=13804d8c vocab=d5f13737
-/
theorem zetaLogZeroFreeWidth_le (t : ℝ) :
    zetaLogZeroFreeWidth t ≤ 1 / (80 * zetaZeroFreeBudget t) := by
  have hE := zetaZeroFreeBudget_ge t
  have hbound := zetaZeroFreeBudget_le_log_height t
  unfold zetaLogZeroFreeWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 80 * zetaZeroFreeBudget t)
  nlinarith

end TwinPrime.Analytic
