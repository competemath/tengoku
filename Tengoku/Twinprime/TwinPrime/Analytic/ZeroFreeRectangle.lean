import Tengoku.Twinprime.TwinPrime.Analytic.SiegelZeroGapUnconditional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform zero-free rectangles from the actual Siegel gap

The width is the smaller of the logarithmic width at the largest height
and half the proved power gap. The positive constant is chosen before
the conductor, character, and height. Regularized zeta is treated separately
and retains its nonzero value at one.
-/

noncomputable section

namespace TwinPrime.Analytic

theorem primitiveLogZeroFreeWidth_antitone_abs (q : ℕ) {t H : ℝ}
    (ht : |t| ≤ |H|) :
    primitiveLogZeroFreeWidth q H ≤ primitiveLogZeroFreeWidth q t := by
  have hq := Real.log_natCast_nonneg q
  have htlog : 0 ≤ Real.log (|t| + 4) :=
    Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_pos
  unfold primitiveLogZeroFreeWidth
  apply one_div_le_one_div_of_le (by positivity)
  have hl : Real.log (|t| + 4) ≤ Real.log (|H| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem zetaLogZeroFreeWidth_antitone_abs {t H : ℝ} (ht : |t| ≤ |H|) :
    zetaLogZeroFreeWidth H ≤ zetaLogZeroFreeWidth t := by
  have htlog : 0 ≤ Real.log (|t| + 4) :=
    Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_pos
  unfold zetaLogZeroFreeWidth
  apply one_div_le_one_div_of_le (by positivity)
  have hl : Real.log (|t| + 4) ≤ Real.log (|H| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

def primitiveZeroFreeRectangleWidth (ε d : ℝ) (q : ℕ) (H : ℝ) : ℝ :=
  min (1 / 16) (min (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε))) / 2

theorem primitiveZeroFreeRectangleWidth_pos (ε d : ℝ) (hd : 0 < d)
    (q : ℕ) [NeZero q] (H : ℝ) :
    0 < primitiveZeroFreeRectangleWidth ε d q H := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hw := primitiveLogZeroFreeWidth_pos q H
  unfold primitiveZeroFreeRectangleWidth
  positivity

theorem primitiveZeroFreeRectangleWidth_le_one_thirtysecond
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    primitiveZeroFreeRectangleWidth ε d q H ≤ 1 / 32 := by
  unfold primitiveZeroFreeRectangleWidth
  have := min_le_left (1 / 16 : ℝ)
    (min (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

theorem twice_primitiveZeroFreeRectangleWidth_le_log_width
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    2 * primitiveZeroFreeRectangleWidth ε d q H ≤ primitiveLogZeroFreeWidth q H := by
  unfold primitiveZeroFreeRectangleWidth
  have h := (min_le_right (1 / 16 : ℝ) _).trans
    (min_le_left (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

theorem twice_primitiveZeroFreeRectangleWidth_le_power_gap
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    2 * primitiveZeroFreeRectangleWidth ε d q H ≤ d * (q : ℝ) ^ (-ε) := by
  unfold primitiveZeroFreeRectangleWidth
  have h := (min_le_right (1 / 16 : ℝ) _).trans
    (min_le_right (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

end TwinPrime.Analytic
