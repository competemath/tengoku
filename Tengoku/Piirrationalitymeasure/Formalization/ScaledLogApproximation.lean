import Tengoku.Piirrationalitymeasure.Formalization.LogSeriesBounds
import Tengoku.Seed.Data.Rat.Cast.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The absolute logarithm remainder (A.6) and power-of-two scaling. -/

namespace PiIrrationality

/--
@isnad1 id=eq.0h2v.s4.b6d652dd58eb from=translated src=- shape=0c86bc61 vocab=24c095f5
-/
theorem oddLogPartialSum_neg (u : ℝ) (N : ℕ) :
    oddLogPartialSum (-u) N = -oddLogPartialSum u N := by
  unfold oddLogPartialSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [oddLogTerm, pow_add, pow_mul, neg_sq, pow_one]
  ring

/--
@isnad1 id=le.1h2v.s6.bb59e5901936 from=translated src=- shape=acb2bb94 vocab=d53fb0cd
-/
theorem oddLogSeries_abs_remainder {u : ℝ} (hu : |u| < 1) (N : ℕ) :
    |Real.log ((1 + u) / (1 - u)) - oddLogPartialSum u N| ≤
      oddLogTailBound |u| N := by
  rcases lt_trichotomy 0 u with hp | hz | hn
  · rw [abs_of_pos hp] at hu ⊢
    obtain ⟨he0, he1⟩ := oddLogSeries_tail_bounds hp hu N
    rw [abs_of_pos he0]
    exact he1.le
  · subst u
    simp [oddLogPartialSum, oddLogTerm, oddLogTailBound]
  · have hp : 0 < -u := by linarith
    have hu' : -u < 1 := by simpa only [abs_of_neg hn] using hu
    obtain ⟨he0, he1⟩ := oddLogSeries_tail_bounds hp hu' N
    have hid : Real.log ((1 + -u) / (1 - -u)) =
        -Real.log ((1 + u) / (1 - u)) := by
      rw [← Real.log_inv]
      congr 1
      simp only [inv_div, sub_eq_add_neg, neg_neg]
    rw [hid, oddLogPartialSum_neg] at he0 he1
    rw [abs_of_neg hn]
    have he : Real.log ((1 + u) / (1 - u)) - oddLogPartialSum u N < 0 := by linarith
    rw [abs_of_neg he]
    linarith

/--
@isnad1 id=le.2h2v.s5.90350e8797ff from=translated src=- shape=b67b8262 vocab=462ecbea
-/
theorem oddLogTailBound_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ) :
    0 ≤ oddLogTailBound u N := by
  unfold oddLogTailBound
  exact div_nonneg (by positivity) (mul_nonneg (by positivity) (by nlinarith))

/--
@isnad1 id=le.2h2v.s6.a9a276c4720a from=translated src=- shape=75bf01fb vocab=4c1d4e7d
-/
theorem oddLogTailBound_le_third {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 3) (N : ℕ) :
    oddLogTailBound u N ≤ oddLogTailBound (1 / 3) N := by
  rcases hu0.eq_or_lt with he | hp
  · rw [← he]
    simpa [oddLogTailBound] using oddLogTailBound_nonneg
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num) N
  · rcases hu1.lt_or_eq with hl | he
    · exact (oddLogTailBound_lt hp hl (by norm_num) N).le
    · rw [he]

/--
@isnad1 id=le.2h2v.s6.7bd93557aac3 from=translated src=- shape=7a460d98 vocab=1196a545
-/
theorem oddLogSeries_abs_remainder_le_third {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 3) (N : ℕ) :
    |Real.log ((1 + u) / (1 - u)) - oddLogPartialSum u N| ≤
      oddLogTailBound (1 / 3) N := by
  have h := oddLogSeries_abs_remainder
    (show |u| < 1 by rw [abs_of_nonneg hu0]; linarith) N
  rw [abs_of_nonneg hu0] at h
  exact h.trans (oddLogTailBound_le_third hu0 hu1 N)

def oddLogSumRat (u : ℚ) (N : ℕ) : ℚ :=
  2 * ∑ j ∈ Finset.range N, u ^ (2 * j + 1) / (2 * (j : ℚ) + 1)

/--
@isnad1 id=eq.0h2v.s4.8e9cfe04e650 from=translated src=- shape=e45b0399 vocab=176da757
-/
theorem oddLogSumRat_cast (u : ℚ) (N : ℕ) :
    (oddLogSumRat u N : ℝ) = oddLogPartialSum (u : ℝ) N := by
  rw [oddLogPartialSum_eq]
  unfold oddLogSumRat
  push_cast
  rfl

def scaledLogApproxRat (x : ℚ) (k : ℤ) (N : ℕ) : ℚ :=
  k * oddLogSumRat (1 / 3) N + oddLogSumRat ((x - 2 ^ k) / (x + 2 ^ k)) N

/--
@isnad1 id=le.2h3v.s7.aec5395574a1 from=translated src=- shape=111f8f4f vocab=49c91756
-/
theorem scaledLogApproxRat_error {x : ℚ} (k : ℤ) (N : ℕ)
    (hxL : 2 ^ k ≤ x) (hxU : x ≤ 2 * 2 ^ k) :
    |Real.log (x : ℝ) - (scaledLogApproxRat x k N : ℝ)| ≤
      (|(k : ℝ)| + 1) * oddLogTailBound (1 / 3) N := by
  have hpow : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) _
  have hL : (2 : ℝ) ^ k ≤ x := by
    simpa only [Rat.cast_zpow, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hxL
  have hU : (x : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hxU
  have hx : (0 : ℝ) < x := hpow.trans_le hL
  let u : ℝ := ((x : ℝ) - 2 ^ k) / ((x : ℝ) + 2 ^ k)
  have hden : 0 < (x : ℝ) + 2 ^ k := by linarith
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hL) hden.le
  have hu1 : u ≤ 1 / 3 := by
    apply (div_le_div_iff₀ hden (by norm_num)).mpr
    linarith
  have hid : (1 + u) / (1 - u) = (x : ℝ) / 2 ^ k := by
    dsimp [u]
    field_simp
    ring
  have hlog : Real.log (x : ℝ) = (k : ℝ) * Real.log 2 +
      Real.log ((1 + u) / (1 - u)) := by
    rw [hid, Real.log_div hx.ne' hpow.ne', Real.log_zpow]
    ring
  have htwo : |Real.log 2 - oddLogPartialSum (1 / 3) N| ≤
      oddLogTailBound (1 / 3) N := by
    convert! oddLogSeries_abs_remainder_le_third
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (le_refl _) N using 1 <;> norm_num
  have hu := oddLogSeries_abs_remainder_le_third hu0 hu1 N
  have ha : (scaledLogApproxRat x k N : ℝ) =
      (k : ℝ) * oddLogPartialSum (1 / 3) N + oddLogPartialSum u N := by
    unfold scaledLogApproxRat
    push_cast
    rw [oddLogSumRat_cast, oddLogSumRat_cast]
    push_cast
    rfl
  calc
    _ = |(k : ℝ) * (Real.log 2 - oddLogPartialSum (1 / 3) N) +
        (Real.log ((1 + u) / (1 - u)) - oddLogPartialSum u N)| := by
      rw [ha, hlog]
      congr 1
      ring
    _ ≤ |(k : ℝ) * (Real.log 2 - oddLogPartialSum (1 / 3) N)| +
        |Real.log ((1 + u) / (1 - u)) - oddLogPartialSum u N| := abs_add_le _ _
    _ ≤ |(k : ℝ)| * oddLogTailBound (1 / 3) N + oddLogTailBound (1 / 3) N := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left htwo (abs_nonneg _)) hu
    _ = _ := by ring

/--
@isnad1 id=lt.0h0v.s6.148854639213 from=translated src=- shape=7d7a685d vocab=907524ec
-/
theorem oddLogTailBound_120 :
    oddLogTailBound (1 / 3) 120 < (964 : ℝ) / 10 ^ 120 := by
  norm_num [oddLogTailBound]

/--
@isnad1 id=lt.2h2v.s7.e91488ca18cc from=translated src=- shape=3c4c43af vocab=c75e0afd
-/
theorem scaledLogApproxRat_error_120 {x : ℚ} (k : ℤ)
    (hxL : 2 ^ k ≤ x) (hxU : x ≤ 2 * 2 ^ k) :
    |Real.log (x : ℝ) - (scaledLogApproxRat x k 120 : ℝ)| <
      (|(k : ℝ)| + 1) * ((964 : ℝ) / 10 ^ 120) := by
  exact (scaledLogApproxRat_error k 120 hxL hxU).trans_lt
    (mul_lt_mul_of_pos_left oddLogTailBound_120 (by positivity))

end PiIrrationality
