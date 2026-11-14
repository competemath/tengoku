import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform harmonic-sum errors for the cutoff in (6.26). -/

namespace PiIrrationality

theorem harmonic_floor_log_scale {r d : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hdr : d ≤ r) :
    |(harmonic ⌊r / d⌋₊ : ℝ) - Real.log (1 / d)| ≤ 1 + |Real.log r| := by
  have hrd : 1 ≤ r / d := (le_div_iff₀ hd).mpr (by simpa using hdr)
  have hlo := log_le_harmonic_floor (r / d) (by positivity)
  have hhi := harmonic_floor_le_one_add_log (r / d) hrd
  have hlog : Real.log (r / d) = Real.log r + Real.log (1 / d) := by
    rw [Real.log_div hr.ne' hd.ne', Real.log_div one_ne_zero hd.ne', Real.log_one]
    ring
  rw [hlog] at hlo hhi
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log r), le_abs_self (Real.log r)]

theorem harmonic_floor_weighted_log_scale {r d L : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hdr : d ≤ r) (hL : |L| ≤ d) :
    |L * (harmonic ⌊r / d⌋₊ : ℝ) - L * Real.log (1 / d)| ≤
      (1 + |Real.log r|) * d := by
  rw [← mul_sub, abs_mul]
  calc
    _ ≤ d * (1 + |Real.log r|) :=
      mul_le_mul hL (harmonic_floor_log_scale hr hd hdr) (abs_nonneg _)
        (by positivity)
    _ = _ := mul_comm _ _

end PiIrrationality
