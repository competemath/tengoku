import Tengoku.ErdosLean.ErdosLean.Erdos265.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #265 — Part L1: linearisation of `f1`, `f2` near `N` and `2N`

Cf. Kovač–Tao (arXiv:2406.17593 v4), Lemma 7.1 for `i = 1, 2`, with explicit constants and
the shifted `f2`.
For `N ≥ 64` and an integer `n` with `|n| ≤ N/8`:
* `|f1 N - f1 (N+n) - n/N²| ≤ 2n²/N³`,       `|f1 (2N) - f1 (2N+n) - n/(4N²)| ≤ 2n²/N³`;
* `|f2 N - f2 (N+n) - 2n/N³| ≤ 8n²/N⁴`,      `|f2 (2N) - f2 (2N+n) - n/(4N³)| ≤ 8n²/N⁴`.
(Numerically the optimal constants are ≈ 1.17, 0.14, 6.23, 0.39.)  For `f2` the integrality
of `n` is used to absorb the `O(|n|/N⁴)` term coming from the shift `x - 1` (`|n| ≤ n²`).
-/

open Filter Topology

namespace Erdos265

/--
@isnad1 id=le.2h2v.s7.638356441ff5 from=translated src=- shape=1b3055ce vocab=9cd39fe4
-/
lemma lin_f1_gen {M x : ℝ} (hM : 0 < M) (hx : |x| ≤ M / 8) :
    |f1 M - f1 (M + x) - x / M ^ 2| ≤ 2 * x ^ 2 / M ^ 3 := by
  have hx1 := abs_le.mp hx
  have hMx : 0 < M + x := by linarith
  have key : f1 M - f1 (M + x) - x / M ^ 2 = -(x ^ 2 / (M ^ 2 * (M + x))) := by
    unfold f1; field_simp; ring
  rw [key, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 0 ≤ x ^ 2 * M ^ 2 * (M + 2 * x) := by
    have : 0 ≤ M + 2 * x := by linarith
    positivity
  nlinarith [h2]

/--
@isnad1 id=le.3h2v.s7.dcf86f579f7f from=translated src=- shape=72949bb9 vocab=a14f827f
-/
lemma lin_f2_gen {M x : ℝ} (hM : 64 ≤ M) (hx : |x| ≤ M / 8) (hxx : |x| ≤ x ^ 2) :
    |f2 M - f2 (M + x) - 2 * x / M ^ 3| ≤ 8 * x ^ 2 / M ^ 4 := by
  have hx1 := abs_le.mp hx
  have hM0 : 0 < M := by linarith
  have hM1 : 0 < M - 1 := by linarith
  have hMx : 0 < M + x := by linarith
  have hMx1 : 0 < M - 1 + x := by linarith
  have hMx1' : M + x - 1 ≠ 0 := by linarith
  have key : f2 M - f2 (M + x) - 2 * x / M ^ 3 =
      x * (3 * M - 2) / (M ^ 3 * (M - 1) ^ 2) -
        x ^ 2 * (3 * M ^ 2 - 3 * M + 1 + x * (2 * M - 1)) /
          (M ^ 2 * (M + x) * (M - 1) ^ 2 * (M - 1 + x)) := by
    unfold f2
    have : M - 1 ≠ 0 := hM1.ne'
    field_simp
    ring
  rw [key]
  have hD : 0 < 3 * M ^ 2 - 3 * M + 1 + x * (2 * M - 1) := by nlinarith
  have hD' : 3 * M ^ 2 - 3 * M + 1 + x * (2 * M - 1) ≤ 13 / 4 * M ^ 2 := by nlinarith
  have hA : |x * (3 * M - 2) / (M ^ 3 * (M - 1) ^ 2)| ≤ 16 / 5 * x ^ 2 / M ^ 4 := by
    rw [abs_div, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 3 * M - 2),
      abs_of_pos (by positivity : (0:ℝ) < M ^ 3 * (M - 1) ^ 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |x| * (3 * M - 2) * M ^ 4 ≤ x ^ 2 * (3 * M ^ 5) := by
      have : |x| * (3 * M - 2) ≤ x ^ 2 * (3 * M) := by
        apply mul_le_mul hxx (by linarith) (by linarith) (sq_nonneg x)
      calc |x| * (3 * M - 2) * M ^ 4 ≤ x ^ 2 * (3 * M) * M ^ 4 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = x ^ 2 * (3 * M ^ 5) := by ring
    have h2 : 3 * M ^ 5 ≤ 16 / 5 * (M ^ 3 * (M - 1) ^ 2) := by
      have : 3 * M ^ 2 ≤ 16 / 5 * (M - 1) ^ 2 := by nlinarith
      have h3 : 0 ≤ M ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h3]
    calc |x| * (3 * M - 2) * M ^ 4 ≤ x ^ 2 * (3 * M ^ 5) := h1
      _ ≤ x ^ 2 * (16 / 5 * (M ^ 3 * (M - 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg x)
      _ = 16 / 5 * x ^ 2 * (M ^ 3 * (M - 1) ^ 2) := by ring
  have hB : |x ^ 2 * (3 * M ^ 2 - 3 * M + 1 + x * (2 * M - 1)) /
          (M ^ 2 * (M + x) * (M - 1) ^ 2 * (M - 1 + x))| ≤ 24 / 5 * x ^ 2 / M ^ 4 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hden : M ^ 2 * (7 / 8 * M) * ((63 / 64) ^ 2 * M ^ 2) * (55 / 64 * M) ≤
        M ^ 2 * (M + x) * (M - 1) ^ 2 * (M - 1 + x) := by
      have e1 : 7 / 8 * M ≤ M + x := by linarith
      have e2 : (63 / 64) ^ 2 * M ^ 2 ≤ (M - 1) ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      have e3 : 55 / 64 * M ≤ M - 1 + x := by linarith
      gcongr
    calc x ^ 2 * (3 * M ^ 2 - 3 * M + 1 + x * (2 * M - 1)) * M ^ 4
        ≤ x ^ 2 * (13 / 4 * M ^ 2) * M ^ 4 := by gcongr
      _ ≤ 24 / 5 * x ^ 2 * (M ^ 2 * (7 / 8 * M) * ((63 / 64) ^ 2 * M ^ 2) * (55 / 64 * M)) := by
          have : 0 ≤ x ^ 2 * M ^ 6 := by positivity
          nlinarith [this]
      _ ≤ 24 / 5 * x ^ 2 * (M ^ 2 * (M + x) * (M - 1) ^ 2 * (M - 1 + x)) := by gcongr
  calc _ ≤ |x * (3 * M - 2) / (M ^ 3 * (M - 1) ^ 2)| +
        |x ^ 2 * (3 * M ^ 2 - 3 * M + 1 + x * (2 * M - 1)) /
          (M ^ 2 * (M + x) * (M - 1) ^ 2 * (M - 1 + x))| := abs_sub _ _
    _ ≤ 16 / 5 * x ^ 2 / M ^ 4 + 24 / 5 * x ^ 2 / M ^ 4 := add_le_add hA hB
    _ = 8 * x ^ 2 / M ^ 4 := by ring

/--
@isnad1 id=le.0h1v.s5.b9d90101c98b from=translated src=- shape=362adc04 vocab=ced34e81
-/
lemma int_abs_le_sq (n : ℤ) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
  rcases eq_or_ne n 0 with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
    rw [← sq_abs]; nlinarith

/--
@isnad1 id=le.2h2v.s7.781f463ebe2d from=translated src=- shape=67907b1d vocab=ff17088d
-/
theorem lin_f1 {N : ℝ} (hN : 64 ≤ N) {n : ℤ} (hn : |(n : ℝ)| ≤ N / 8) :
    |f1 N - f1 (N + n) - n / N ^ 2| ≤ 2 * (n : ℝ) ^ 2 / N ^ 3 := by
  have := lin_f1_gen (M := N) (x := n) (by linarith) hn
  exact this

/--
@isnad1 id=le.2h2v.s7.0beb171e14f5 from=translated src=- shape=3fb76f4b vocab=ff17088d
-/
theorem lin_f1_two {N : ℝ} (hN : 64 ≤ N) {n : ℤ} (hn : |(n : ℝ)| ≤ N / 8) :
    |f1 (2 * N) - f1 (2 * N + n) - n / (4 * N ^ 2)| ≤ 2 * (n : ℝ) ^ 2 / N ^ 3 := by
  have hM : (0:ℝ) < 2 * N := by linarith
  have h := lin_f1_gen (M := 2 * N) (x := n) hM (by linarith)
  have e1 : (n : ℝ) / (2 * N) ^ 2 = n / (4 * N ^ 2) := by ring
  rw [e1] at h
  refine h.trans ?_
  have hN0 : 0 < N := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ (n : ℝ) ^ 2 * N ^ 3 := by positivity
  nlinarith

/--
@isnad1 id=le.2h2v.s7.2bb21f102c5c from=translated src=- shape=77d52882 vocab=27145df4
-/
theorem lin_f2 {N : ℝ} (hN : 64 ≤ N) {n : ℤ} (hn : |(n : ℝ)| ≤ N / 8) :
    |f2 N - f2 (N + n) - 2 * n / N ^ 3| ≤ 8 * (n : ℝ) ^ 2 / N ^ 4 := by
  have := lin_f2_gen (M := N) (x := n) hN hn (int_abs_le_sq n)
  exact this

/--
@isnad1 id=le.2h2v.s7.0c3c51da5ef3 from=translated src=- shape=3fb76f4b vocab=27145df4
-/
theorem lin_f2_two {N : ℝ} (hN : 64 ≤ N) {n : ℤ} (hn : |(n : ℝ)| ≤ N / 8) :
    |f2 (2 * N) - f2 (2 * N + n) - n / (4 * N ^ 3)| ≤ 8 * (n : ℝ) ^ 2 / N ^ 4 := by
  have h := lin_f2_gen (M := 2 * N) (x := n) (by linarith) (by linarith) (int_abs_le_sq n)
  have e1 : 2 * (n : ℝ) / (2 * N) ^ 3 = n / (4 * N ^ 3) := by
    have : N ≠ 0 := by linarith
    field_simp; ring
  rw [e1] at h
  refine h.trans ?_
  have hN0 : 0 < N := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ (n : ℝ) ^ 2 * N ^ 4 := by positivity
  nlinarith

end Erdos265
