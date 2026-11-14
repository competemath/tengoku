import Tengoku.Twinprime.TwinPrime.Analytic.DyadicNatPartition
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterVaughanBox

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical logarithm comparisons for the BV mean-value estimate

The explicit threshold `256` controls the dyadic depth and large-sieve
logarithmic factor in the range `R ≤ sqrt T`. The numerical constants
follow from `log 256 = 8 * log 2` and `1 / 2 ≤ log 2`.
-/

noncomputable section

namespace TwinPrime.Analytic

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h
  linarith

theorem eight_log_two_le_log_nat (T : ℕ) (hT : 256 ≤ T) :
    8 * Real.log 2 ≤ Real.log (T : ℝ) := by
  have heq : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    calc
      _ = Real.log ((2 : ℝ) ^ 8) := by norm_num
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [← heq]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hT)

theorem one_le_log_of_256_le (T : ℕ) (hT : 256 ≤ T) :
    1 ≤ Real.log (T : ℝ) := by
  linarith [eight_log_two_le_log_nat T hT, half_le_log_two]

theorem dyadicNatDepth_le_two_div_log_two_mul_log (T : ℕ) (hT : 256 ≤ T) :
    (dyadicNatDepth T : ℝ) ≤ (2 / Real.log 2) * Real.log (T : ℝ) := by
  have hD : dyadicNatDepth T ≤ Nat.log 2 T + 1 :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) T))
  have hlog := Real.natLog_le_logb T 2
  simp only [Real.logb, Nat.cast_ofNat] at hlog
  have hlog2 : 0 < Real.log 2 := by linarith [half_le_log_two]
  have hTlog : Real.log 2 ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ T by omega))
  have hone : 1 ≤ Real.log (T : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa using hTlog)
  calc
    _ ≤ (Nat.log 2 T : ℝ) + 1 := by exact_mod_cast hD
    _ ≤ Real.log (T : ℝ) / Real.log 2 + 1 := add_le_add hlog le_rfl
    _ ≤ 2 * (Real.log (T : ℝ) / Real.log 2) := by linarith
    _ = _ := by ring

theorem characterLargeSieveLogFactor_le_two_log (T R : ℕ) (hT : 256 ≤ T)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    characterLargeSieveLogFactor R ≤ 2 * Real.log (T : ℝ) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hs1 : 1 ≤ Real.sqrt (T : ℝ) := Real.one_le_sqrt.mpr
    (by exact_mod_cast (show 1 ≤ T by omega))
  have harg : (R : ℝ) + 1 ≤ 2 * Real.sqrt (T : ℝ) := by linarith
  have hlog := Real.log_le_log (show (0 : ℝ) < R + 1 by positivity) harg
  rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hT0).ne', Real.log_sqrt hT0.le] at hlog
  have hsize := eight_log_two_le_log_nat T hT
  unfold characterLargeSieveLogFactor
  linarith [half_le_log_two]

theorem one_add_log_modulus_le_log (T R : ℕ) (hT : 256 ≤ T) (hR1 : 1 ≤ R)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    1 + Real.log (R : ℝ) ≤ Real.log (T : ℝ) := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hlog := Real.log_le_log hR0 hR
  rw [Real.log_sqrt (Nat.cast_nonneg T)] at hlog
  linarith [eight_log_two_le_log_nat T hT, half_le_log_two]

end TwinPrime.Analytic
