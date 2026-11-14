import Tengoku.Piirrationalitymeasure.Formalization.LogSeriesBounds
import Tengoku.Seed.Data.Rat.Cast.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The finite logarithm estimates (3.18), (3.20), (3.28), and (3.29). -/

namespace PiIrrationality

noncomputable def digammaLogApprox (x : ℝ) : ℝ := oddLogPartialSum (x / (200 + x)) 8

theorem digammaLogApprox_eq (x : ℝ) :
    digammaLogApprox x = 2 * ∑ q ∈ Finset.range 8,
      (x / (200 + x)) ^ (2 * q + 1) / (2 * (q : ℝ) + 1) :=
  oddLogPartialSum_eq _ _

theorem digammaLogApprox_error {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < Real.log (1 + x / 100) - digammaLogApprox x ∧
      Real.log (1 + x / 100) - digammaLogApprox x <
        2 / (17 * (1 - (201 : ℝ) ^ (-2 : ℤ)) * 201 ^ 17) := by
  have hz0 : 0 < x / (200 + x) := div_pos hx0 (by linarith)
  have hzw : x / (200 + x) < (1 : ℝ) / 201 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hz1 : x / (200 + x) < 1 := hzw.trans (by norm_num)
  have h := oddLogSeries_tail_bounds hz0 hz1 8
  have heq : (1 + x / (200 + x)) / (1 - x / (200 + x)) = 1 + x / 100 := by
    have hne : 200 + x ≠ 0 := by linarith
    field_simp
    ring
  rw [heq] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hb := oddLogTailBound_lt hz0 hzw (by norm_num) 8
  convert! hb using 1
  norm_num [oddLogTailBound]

def logTwoApproxRat : ℚ :=
  2 * ∑ q ∈ Finset.range 50, 1 / ((2 * (q : ℚ) + 1) * 3 ^ (2 * q + 1))

theorem logTwoApproxRat_cast :
    (logTwoApproxRat : ℝ) = oddLogPartialSum ((1 : ℝ) / 3) 50 := by
  rw [oddLogPartialSum_eq]
  unfold logTwoApproxRat
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [div_pow]
  simp only [one_pow]
  field_simp

theorem logTwoApproxRat_error :
    0 < Real.log 2 - (logTwoApproxRat : ℝ) ∧
      Real.log 2 - (logTwoApproxRat : ℝ) <
        2 / (101 * (3 : ℝ) ^ 101 * (1 - (3 : ℝ) ^ (-2 : ℤ))) := by
  rw [logTwoApproxRat_cast]
  have h := oddLogSeries_tail_bounds (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num) 50
  convert! h using 1 <;> norm_num [oddLogTailBound]

theorem logTwoApproxRat_error_decimal :
    Real.log 2 - (logTwoApproxRat : ℝ) < (15 : ℝ) / 10 ^ 51 := by
  apply logTwoApproxRat_error.2.trans
  norm_num

end PiIrrationality
