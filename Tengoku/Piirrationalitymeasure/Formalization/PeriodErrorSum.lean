import Tengoku.Piirrationalitymeasure.Formalization.HarmonicLogScale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Summing the uniform inverse-square errors in (6.26). -/

namespace PiIrrationality

/--
@isnad1 id=le.1h1v.s6.ec932e29155f from=translated src=- shape=f3a9c139 vocab=075a0716
-/
theorem inverse_square_le_telescope {k : ℝ} (hk : 1 ≤ k) :
    1 / k ^ 2 ≤ 2 / k - 2 / (k + 1) := by
  have hk0 : 0 < k := by linarith
  have hkp : 0 < k + 1 := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hk0)).mpr
  apply (mul_le_mul_iff_left₀ hkp).mp
  field_simp
  nlinarith

/--
@isnad1 id=le.0h1v.s6.535620e69abb from=translated src=- shape=38c984e5 vocab=2c02d67e
-/
theorem sum_Icc_inverse_square_le (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ 2) ≤ 2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have h := inverse_square_le_telescope (k := (N : ℝ) + 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) N])
    push_cast
    linarith

/--
@isnad1 id=le.0h1v.s6.ea5d32f0580a from=translated src=- shape=151cdf33 vocab=7f95fb3f
-/
theorem sum_Icc_inverse_square_le_two (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ 2) ≤ 2 := by
  exact (sum_Icc_inverse_square_le N).trans (by
    have h : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
    linarith)

/--
@isnad1 id=le.2h4v.s7.22fd4be6aaf8 from=translated src=- shape=fdf655af vocab=c590483c
-/
theorem sum_Icc_inverse_square_error {f : ℕ → ℝ} {D C : ℝ} (N : ℕ)
    (hC : 0 ≤ C)
    (herr : ∀ k ∈ Finset.Icc 1 N, |f k - D / (k : ℝ)| ≤ C / (k : ℝ) ^ 2) :
    |(∑ k ∈ Finset.Icc 1 N, f k) - D * (harmonic N : ℝ)| ≤ 2 * C := by
  have hh : D * (harmonic N : ℝ) = ∑ k ∈ Finset.Icc 1 N, D / (k : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Finset.mul_sum, div_eq_mul_inv]
  rw [hh, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N, |f k - D / (k : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N, C / (k : ℝ) ^ 2 := Finset.sum_le_sum herr
    _ = C * ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ 2 := by
      simp only [Finset.mul_sum, mul_one_div]
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_Icc_inverse_square_le_two N) hC
    _ = _ := mul_comm _ _

end PiIrrationality
