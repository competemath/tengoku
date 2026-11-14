import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.Legendre
import Tengoku.Twinprime.TwinPrime.Brun
import Tengoku.Twinprime.TwinPrime.Conditional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Infinitely many twin rough numbers

With the sifting level `z(x) = ⌊log x / (2 log 3)⌋`, Legendre's sieve (`twinRough_count_ge`)
gives, for `x ≥ 2^24`,

  `#{n ≤ x : n(n+2) has no prime factor ≤ z(x)} ≥ x / (log x)²`

(`twinRough_count_ge_of_large`), hence (`twinRough_infinite`): **there are infinitely many `n`
such that every prime factor of `n (n + 2)` exceeds `log n / (2 log 3)`** — both `n` and `n + 2`
are simultaneously "rough".  This is the first lower-bound result of twin type in the library.
-/

noncomputable section

open Finset Real Filter Topology
open TwinPrime.Sieve

namespace TwinPrime

/-- The sifting level `z(x) = ⌊log x / (2 log 3)⌋`.-/
def zL (x : ℕ) : ℕ := ⌊Real.log x / (2 * Real.log 3)⌋₊

theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem zL_le {x : ℕ} : (zL x : ℝ) ≤ Real.log x / (2 * Real.log 3) := by
  unfold zL
  apply Nat.floor_le
  have h0 : 0 ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlog3 : 0 < Real.log 3 := by linarith [one_le_log_three]
  positivity

theorem three_le_zL {x : ℕ} (hx : 3 ^ 6 ≤ x) : 3 ≤ zL x := by
  unfold zL
  apply Nat.le_floor
  have hlog3 : 0 < Real.log 3 := by linarith [one_le_log_three]
  rw [le_div_iff₀ (by positivity)]
  have : Real.log ((3 : ℝ) ^ 6) ≤ Real.log x :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  rw [Real.log_pow] at this
  push_cast at this ⊢
  linarith

/-- `3^{z(x)+1} ≤ 3 √x`.-/
theorem three_pow_zL_le {x : ℕ} (hx : 1 ≤ x) : (3 : ℝ) ^ (zL x + 1) ≤ 3 * Real.sqrt x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog3 : 0 < Real.log 3 := by linarith [one_le_log_three]
  have h1 : (3 : ℝ) ^ (zL x) ≤ Real.sqrt x := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    calc Real.log 3 * (zL x : ℝ) ≤ Real.log 3 * (Real.log x / (2 * Real.log 3)) :=
          mul_le_mul_of_nonneg_left zL_le hlog3.le
      _ = Real.log x * (1 / 2) := by field_simp
  calc (3 : ℝ) ^ (zL x + 1) = 3 * 3 ^ (zL x) := by ring
    _ ≤ 3 * Real.sqrt x := by linarith

/-- `√x (log x)² ≤ x / 2` for `x ≥ 2^24`.-/
theorem sqrt_mul_log_sq_le {x : ℝ} (hx : 2 ^ 24 ≤ x) : Real.sqrt x * (Real.log x) ^ 2 ≤ x / 2 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog := log_sq_le hx1                      -- (log x)^2 ≤ 2^8 x^{1/8}
  have h58 : Real.sqrt x * x ^ (1 / 8 : ℝ) = x ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
    norm_num
  have h38 : (512 : ℝ) ≤ x ^ (3 / 8 : ℝ) := by
    have : ((2 : ℝ) ^ (24 : ℕ)) ^ (3 / 8 : ℝ) = 2 ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      norm_num
    calc (512 : ℝ) = ((2 : ℝ) ^ (24 : ℕ)) ^ (3 / 8 : ℝ) := by rw [this]; norm_num
      _ ≤ x ^ (3 / 8 : ℝ) := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)
  have hsplit : x = x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have h58pos : 0 ≤ x ^ (5 / 8 : ℝ) := by positivity
  calc Real.sqrt x * (Real.log x) ^ 2 ≤ Real.sqrt x * (2 ^ 8 * x ^ (1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)
    _ = 2 ^ 8 * x ^ (5 / 8 : ℝ) := by rw [← h58]; ring
    _ = 2 ^ 8 * x ^ (5 / 8 : ℝ) * 512 / 512 := by ring
    _ ≤ 2 ^ 8 * x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) / 512 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_left h38 (by positivity)
    _ = x / 2 := by rw [mul_assoc, ← hsplit]; ring

end TwinPrime
