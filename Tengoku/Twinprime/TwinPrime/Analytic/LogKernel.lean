import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGrowth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary sums of reciprocal logarithmic powers

A split at the primary fifth-root cutoff bounds the inverse fifth-power
logarithm kernel. The cutoff head is negligible and logarithms on the tail
are comparable to the logarithm of the full endpoint. All statements are
independent of arithmetic cancellation hypotheses.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

/-- Once the cutoff is at least two, its logarithm controls the original
scale logarithm without a successor inside the cutoff logarithm.
@isnad1 id=le.1h1v.s5.e8a97aa288ab from=translated src=- shape=930fdc4e vocab=03b5d0b4
-/
theorem log_nat_le_fourteen_log_primaryCutoff (N : ℕ)
    (hU : 2 ≤ primaryCutoff N) :
    Real.log (N : ℝ) ≤ 14 * Real.log (primaryCutoff N : ℝ) := by
  have hN0 : N ≠ 0 := by
    intro h
    subst N
    norm_num [primaryCutoff] at hU
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hUr : (2 : ℝ) ≤ primaryCutoff N := by exact_mod_cast hU
  have hlogU1 : Real.log ((primaryCutoff N : ℝ) + 1) ≤
      2 * Real.log (primaryCutoff N : ℝ) := by
    calc
      _ ≤ Real.log ((primaryCutoff N : ℝ) ^ (2 : ℕ)) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ((primaryCutoff N : ℝ) - 2)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 * N + 2) :=
    Real.log_le_log hNr (by linarith)
  have hdyadic := log_dyadic_le_seven_log_primaryCutoff N hN1
  linarith

/-- The cutoff head stays sublinear after every fixed logarithmic weight.
@isnad1 id=tendsto.0h1v.s6.93e17edddc61 from=translated src=- shape=d3c2e913 vocab=8398c40d
-/
theorem tendsto_primaryCutoff_mul_log_pow_div (k : ℕ) :
    Tendsto (fun N : ℕ => (primaryCutoff N : ℝ) * (Real.log N) ^ k / N)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_dispersion_log_pow_div_primaryCutoff k)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hlog k)) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hU : 1 ≤ primaryCutoff N := primaryCutoff_pos hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hUr : (0 : ℝ) < primaryCutoff N := by exact_mod_cast hU
    have hUsq : (primaryCutoff N : ℝ) ^ 2 ≤ N := by
      exact_mod_cast (pow_le_pow_right₀ hU (by decide : 2 ≤ 5)).trans
        (primaryCutoff_pow_five_le N)
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hlogle : Real.log (N : ℝ) ≤ Real.log (4 * N + 4) :=
      Real.log_le_log hNr (by linarith)
    have hratio : (primaryCutoff N : ℝ) / N ≤ 1 / (primaryCutoff N : ℝ) :=
      (div_le_div_iff₀ hNr hUr).mpr (by nlinarith)
    have hL : 0 ≤ (Real.log (4 * N + 4)) ^ k :=
      pow_nonneg (hlog.trans hlogle) k
    calc
      _ ≤ (primaryCutoff N : ℝ) * (Real.log (4 * N + 4)) ^ k / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hlogle k) hUr.le) hNr.le
      _ = (Real.log (4 * N + 4)) ^ k * ((primaryCutoff N : ℝ) / N) := by ring
      _ ≤ (Real.log (4 * N + 4)) ^ k * (1 / (primaryCutoff N : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hL
      _ = _ := by ring

/-- Explicit head and tail bounds for the reciprocal fifth-logarithm kernel.
@isnad1 id=le.1h1v.s7.ab63655ba716 from=translated src=- shape=68626146 vocab=0cfda3bb
-/
theorem sum_inverse_log_five_le_cutoff (N : ℕ) (hN : 32 ≤ N) :
    (∑ n ∈ Icc 2 N, 1 / (Real.log n) ^ 5) ≤
      (primaryCutoff N : ℝ) / (Real.log 2) ^ 5 +
        (14 : ℝ) ^ 5 * N / (Real.log N) ^ 5 := by
  let U := primaryCutoff N
  have hU : 2 ≤ U := primaryCutoff_two_le hN
  have hUN : U ≤ N := primaryCutoff_le (by omega)
  have hUr : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogU : 0 < Real.log (U : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hhead : (∑ n ∈ Ioc 1 U, 1 / (Real.log n) ^ 5) ≤
      (U : ℝ) / (Real.log 2) ^ 5 := by
    calc
      _ ≤ ∑ _n ∈ Ioc 1 U, 1 / (Real.log 2) ^ 5 := by
        apply sum_le_sum
        intro n hn
        have hn2 : 2 ≤ n := by have := (mem_Ioc.mp hn).1; omega
        exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hlog2 5)
          (pow_le_pow_left₀ hlog2.le
            (Real.log_le_log (by norm_num) (by exact_mod_cast hn2)) 5)
      _ = ((Ioc 1 U).card : ℝ) / (Real.log 2) ^ 5 := by simp [nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by
        exact_mod_cast (show (Ioc 1 U).card ≤ U by simp)) (by positivity)
  have hlogcomp : Real.log (N : ℝ) ≤ 14 * Real.log (U : ℝ) :=
    log_nat_le_fourteen_log_primaryCutoff N hU
  have hrecip : 1 / (Real.log (U : ℝ)) ^ 5 ≤ (14 : ℝ) ^ 5 / (Real.log N) ^ 5 := by
    apply (div_le_div_iff₀ (pow_pos hlogU 5) (pow_pos hlogN 5)).mpr
    have h := pow_le_pow_left₀ hlogN.le hlogcomp 5
    simpa only [one_mul, mul_pow] using h
  have htail : (∑ n ∈ Ioc U N, 1 / (Real.log n) ^ 5) ≤
      (14 : ℝ) ^ 5 * N / (Real.log N) ^ 5 := by
    calc
      _ ≤ ∑ _n ∈ Ioc U N, (14 : ℝ) ^ 5 / (Real.log N) ^ 5 := by
        apply sum_le_sum
        intro n hn
        have hlogle : Real.log (U : ℝ) ≤ Real.log n :=
          Real.log_le_log hUr (by exact_mod_cast (mem_Ioc.mp hn).1.le)
        exact (div_le_div_of_nonneg_left (by norm_num) (pow_pos hlogU 5)
          (pow_le_pow_left₀ hlogU.le hlogle 5)).trans hrecip
      _ = ((Ioc U N).card : ℝ) * ((14 : ℝ) ^ 5 / (Real.log N) ^ 5) := by simp
      _ ≤ (N : ℝ) * ((14 : ℝ) ^ 5 / (Real.log N) ^ 5) :=
        mul_le_mul_of_nonneg_right (by
          exact_mod_cast (show (Ioc U N).card ≤ N by simp)) (by positivity)
      _ = _ := by ring
  have hsplit := sum_Ioc_consecutive (fun n : ℕ => 1 / (Real.log n) ^ 5)
    (by omega : 1 ≤ U) hUN
  have hI : Icc 2 N = Ioc 1 N := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hI, ← hsplit]
  exact add_le_add hhead htail

/-- The full positive kernel sum has an eventual bound with an explicit constant.
@isnad1 id=eventual.0h0v.s7.0f50987cf072 from=translated src=- shape=8e988935 vocab=a1e5871d
-/
theorem eventually_sum_inverse_log_five_le :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Icc 2 N, 1 / (Real.log n) ^ 5) ≤
        (1 + (14 : ℝ) ^ 5) * N / (Real.log N) ^ 5 := by
  have hlim := (tendsto_primaryCutoff_mul_log_pow_div 5).const_mul
    (1 / (Real.log 2) ^ 5)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 32] with N hsmall hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hhead : (primaryCutoff N : ℝ) / (Real.log 2) ^ 5 ≤
      (N : ℝ) / (Real.log N) ^ 5 := by
    apply (le_div_iff₀ (pow_pos hlogN 5)).mpr
    have h := (div_lt_iff₀ hNr).mp (show
      ((primaryCutoff N : ℝ) / (Real.log 2) ^ 5 * (Real.log N) ^ 5) / N < 1 by
        have heq : ((primaryCutoff N : ℝ) / (Real.log 2) ^ 5 * (Real.log N) ^ 5) / N =
            (1 / (Real.log 2) ^ 5) * ((primaryCutoff N : ℝ) * (Real.log N) ^ 5 / N) := by ring
        rw [heq]
        exact hsmall)
    simpa only [one_mul] using h.le
  calc
    _ ≤ (primaryCutoff N : ℝ) / (Real.log 2) ^ 5 +
        (14 : ℝ) ^ 5 * N / (Real.log N) ^ 5 := sum_inverse_log_five_le_cutoff N hN
    _ ≤ (N : ℝ) / (Real.log N) ^ 5 + (14 : ℝ) ^ 5 * N / (Real.log N) ^ 5 :=
      add_le_add hhead le_rfl
    _ = _ := by ring

/-- An assumption-free existence form of the reciprocal logarithm kernel bound.
@isnad1 id=ex.0h0v.s6.45dae0d20b5a from=translated src=- shape=4b552720 vocab=b5b8869a
-/
theorem exists_sum_inverse_log_five_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Icc 2 N, 1 / (Real.log n) ^ 5) ≤ C * N / (Real.log N) ^ 5 :=
  ⟨1 + (14 : ℝ) ^ 5, by positivity, eventually_sum_inverse_log_five_le⟩

end TwinPrime.Analytic
