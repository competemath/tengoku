import Tengoku.Piirrationalitymeasure.Formalization.ScaledLogApproximation
import Tengoku.Seed.Algebra.BigOperators.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Certified fixed-denominator evaluation of the finite logarithm sums. -/

namespace PiIrrationality

def roundedOddLogSum (u : ℚ) (N scale : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, ⌊(scale : ℚ) * (2 * u ^ (2 * j + 1) / (2 * (j : ℚ) + 1))⌋

/--
@isnad1 id=le.1h3v.s6.e948a80fdca4 from=translated src=- shape=013bbc0e vocab=18a8722b
-/
theorem roundedOddLogSum_error (u : ℚ) (N : ℕ) {scale : ℕ} (hs : 0 < scale) :
    |oddLogSumRat u N - (roundedOddLogSum u N scale : ℚ) / scale| ≤ (N : ℚ) / scale := by
  have hs' : (0 : ℚ) < scale := by exact_mod_cast hs
  have he : oddLogSumRat u N - (roundedOddLogSum u N scale : ℚ) / scale =
      ∑ j ∈ Finset.range N, (2 * u ^ (2 * j + 1) / (2 * (j : ℚ) + 1) -
        (⌊(scale : ℚ) * (2 * u ^ (2 * j + 1) / (2 * (j : ℚ) + 1))⌋ : ℚ) / scale) := by
    unfold oddLogSumRat roundedOddLogSum
    rw [Int.cast_sum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hb (a : ℚ) : 0 ≤ a - (⌊(scale : ℚ) * a⌋ : ℚ) / scale ∧
      a - (⌊(scale : ℚ) * a⌋ : ℚ) / scale ≤ 1 / scale := by
    have hl := Int.floor_le ((scale : ℚ) * a)
    have hu := Int.lt_floor_add_one ((scale : ℚ) * a)
    rw [mul_comm (scale : ℚ) a] at hl hu ⊢
    constructor
    · rw [sub_nonneg, div_le_iff₀ hs']
      nlinarith
    · apply (mul_le_mul_iff_left₀ hs').mp
      field_simp
      linarith
  rw [he, abs_of_nonneg (Finset.sum_nonneg (fun j _ => (hb _).1))]
  calc
    _ ≤ ∑ _j ∈ Finset.range N, (1 : ℚ) / scale :=
      Finset.sum_le_sum (fun j _ => (hb _).2)
    _ = _ := by simp [div_eq_mul_inv]

def roundedScaledLog (x : ℚ) (k : ℤ) (N scale : ℕ) : ℤ :=
  k * roundedOddLogSum (1 / 3) N scale +
    roundedOddLogSum ((x - 2 ^ k) / (x + 2 ^ k)) N scale

/--
@isnad1 id=le.1h4v.s6.beda2d91e16b from=translated src=- shape=38833639 vocab=9dfd8cd4
-/
theorem roundedScaledLog_error (x : ℚ) (k : ℤ) (N : ℕ)
    {scale : ℕ} (hs : 0 < scale) :
    |scaledLogApproxRat x k N - (roundedScaledLog x k N scale : ℚ) / scale| ≤
      (|(k : ℚ)| + 1) * ((N : ℚ) / scale) := by
  have h0 := roundedOddLogSum_error (1 / 3) N hs
  have hu := roundedOddLogSum_error ((x - 2 ^ k) / (x + 2 ^ k)) N hs
  calc
    _ = |(k : ℚ) * (oddLogSumRat (1 / 3) N - (roundedOddLogSum (1 / 3) N scale : ℚ) / scale) +
        (oddLogSumRat ((x - 2 ^ k) / (x + 2 ^ k)) N -
          (roundedOddLogSum ((x - 2 ^ k) / (x + 2 ^ k)) N scale : ℚ) / scale)| := by
      unfold scaledLogApproxRat roundedScaledLog
      push_cast
      congr 1
      ring
    _ ≤ |(k : ℚ) * (oddLogSumRat (1 / 3) N -
        (roundedOddLogSum (1 / 3) N scale : ℚ) / scale)| +
        |oddLogSumRat ((x - 2 ^ k) / (x + 2 ^ k)) N -
          (roundedOddLogSum ((x - 2 ^ k) / (x + 2 ^ k)) N scale : ℚ) / scale| := abs_add_le _ _
    _ ≤ |(k : ℚ)| * ((N : ℚ) / scale) + (N : ℚ) / scale := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _)) hu
    _ = _ := by ring

/--
@isnad1 id=lt.2h2v.s8.ab29bd1c2a08 from=translated src=- shape=717f2feb vocab=b692c891
-/
theorem roundedScaledLog_real_error {x : ℚ} (k : ℤ)
    (hxL : 2 ^ k ≤ x) (hxU : x ≤ 2 * 2 ^ k) :
    |Real.log (x : ℝ) - (roundedScaledLog x k 120 (10 ^ 60) : ℝ) / 10 ^ 60| <
      (|(k : ℝ)| + 1) * ((964 : ℝ) / 10 ^ 120 + 120 / 10 ^ 60) := by
  have ha := scaledLogApproxRat_error_120 k hxL hxU
  have hr : |(scaledLogApproxRat x k 120 : ℝ) -
      (roundedScaledLog x k 120 (10 ^ 60) : ℝ) / 10 ^ 60| ≤
      (|(k : ℝ)| + 1) * ((120 : ℝ) / 10 ^ 60) := by
    have h := (Rat.cast_le (K := ℝ)).mpr
      (roundedScaledLog_error x k 120 (by positivity : 0 < 10 ^ 60))
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_pow,
      Nat.cast_ofNat, Rat.cast_pow, Rat.cast_ofNat] using h
  calc
    _ ≤ |Real.log (x : ℝ) - (scaledLogApproxRat x k 120 : ℝ)| +
        |(scaledLogApproxRat x k 120 : ℝ) -
          (roundedScaledLog x k 120 (10 ^ 60) : ℝ) / 10 ^ 60| := abs_sub_le _ _ _
    _ < (|(k : ℝ)| + 1) * ((964 : ℝ) / 10 ^ 120) +
        (|(k : ℝ)| + 1) * ((120 : ℝ) / 10 ^ 60) := add_lt_add_of_lt_of_le ha hr
    _ = _ := by ring

end PiIrrationality
