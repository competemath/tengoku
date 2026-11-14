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

/--
@isnad1 id=le.1h3v.s4.6b131b428674 from=translated src=- shape=fde9e779 vocab=324cf375
-/
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

/--
@isnad1 id=le.1h2v.s4.f620b0891c02 from=translated src=- shape=f37eb936 vocab=110aae35
-/
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

/--
@isnad1 id=lt.1h4v.s5.667e3b875544 from=translated src=- shape=e5ed497b vocab=119c9758
-/
theorem primitiveZeroFreeRectangleWidth_pos (ε d : ℝ) (hd : 0 < d)
    (q : ℕ) [NeZero q] (H : ℝ) :
    0 < primitiveZeroFreeRectangleWidth ε d q H := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hw := primitiveLogZeroFreeWidth_pos q H
  unfold primitiveZeroFreeRectangleWidth
  positivity

/--
@isnad1 id=le.0h4v.s5.1669e2d840ff from=translated src=- shape=c3f2a29a vocab=bc768647
-/
theorem primitiveZeroFreeRectangleWidth_le_one_thirtysecond
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    primitiveZeroFreeRectangleWidth ε d q H ≤ 1 / 32 := by
  unfold primitiveZeroFreeRectangleWidth
  have := min_le_left (1 / 16 : ℝ)
    (min (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

/--
@isnad1 id=le.0h4v.s5.6c05d5f92703 from=translated src=- shape=93845882 vocab=7ec340f5
-/
theorem twice_primitiveZeroFreeRectangleWidth_le_log_width
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    2 * primitiveZeroFreeRectangleWidth ε d q H ≤ primitiveLogZeroFreeWidth q H := by
  unfold primitiveZeroFreeRectangleWidth
  have h := (min_le_right (1 / 16 : ℝ) _).trans
    (min_le_left (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

/--
@isnad1 id=le.0h4v.s5.d386cb117027 from=translated src=- shape=222795b2 vocab=75789162
-/
theorem twice_primitiveZeroFreeRectangleWidth_le_power_gap
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    2 * primitiveZeroFreeRectangleWidth ε d q H ≤ d * (q : ℝ) ^ (-ε) := by
  unfold primitiveZeroFreeRectangleWidth
  have h := (min_le_right (1 / 16 : ℝ) _).trans
    (min_le_right (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

end TwinPrime.Analytic
