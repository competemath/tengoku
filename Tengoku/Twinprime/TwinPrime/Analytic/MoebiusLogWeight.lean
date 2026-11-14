import Tengoku.Twinprime.TwinPrime.Analytic.SelbergSummatory
import Tengoku.Twinprime.TwinPrime.Analytic.LogKernel
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocalReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unweighting the logarithm-squared Möbius sum

Discrete Abel summation bounds the difference between `M(N) log² N` and the
logarithm-squared Möbius sum. The small endpoint at one is explicit, and the
remaining increment error is bounded by the reciprocal fifth-logarithm kernel.
-/

noncomputable section

open Finset Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

theorem log_sq_succ_sub_bounds {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ (Real.log (x + 1)) ^ 2 - (Real.log x) ^ 2 ∧
      (Real.log (x + 1)) ^ 2 - (Real.log x) ^ 2 ≤ 4 * Real.log x / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hmono : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have htwo : Real.log (x + 1) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ (2 : ℕ)) :=
        Real.log_le_log hx1 (by nlinarith [sq_nonneg (x - 2)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hdiff : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx0)
    rw [Real.log_div hx1.ne' hx0.ne'] at h
    convert h using 1
    field_simp
    ring
  constructor
  · exact sub_nonneg.mpr (pow_le_pow_left₀ hlog.le hmono 2)
  · calc
      _ = (Real.log (x + 1) - Real.log x) * (Real.log (x + 1) + Real.log x) := by ring
      _ ≤ (1 / x) * (4 * Real.log x) :=
        mul_le_mul hdiff (by linarith) (by linarith) (by positivity)
      _ = _ := by ring

/-- Exact Abel identity, including the contribution at `t=1`.-/
theorem mertens_mul_log_sq_eq (N : ℕ) (hN : 2 ≤ N) :
    mertensSum N * (Real.log N) ^ 2 = moebiusLogSqSummatory (N : ℝ) +
      (Real.log 2) ^ 2 +
      ∑ t ∈ Ico 2 N, ((Real.log ((t : ℝ) + 1)) ^ 2 - (Real.log t) ^ 2) * mertensSum t := by
  let v : ℕ → ℝ := fun t =>
    ((Real.log ((t : ℝ) + 1)) ^ 2 - (Real.log t) ^ 2) * mertensSum t
  have hsmall : (∑ t ∈ Ico 0 2, v t) = (Real.log 2) ^ 2 := by
    norm_num [v, Nat.Ico_zero_eq_range, sum_range_succ, mertensSum, coefficientSum]
  have hsplit := sum_Ico_consecutive v (by norm_num : 0 ≤ 2) hN
  rw [hsmall] at hsplit
  have habel := abel_cumulative_Ioc 0 N (Nat.zero_le N)
    (fun n => (Real.log n) ^ 2) (fun n => (μ n : ℝ))
  push_cast at habel
  change (∑ n ∈ Ioc 0 N, (Real.log n) ^ 2 * (μ n : ℝ)) =
    (Real.log N) ^ 2 * mertensSum N - (Real.log (0 : ℝ)) ^ 2 * mertensSum 0 -
    ∑ t ∈ Ico 0 N, v t at habel
  have hsum : (∑ n ∈ Ioc 0 N, (Real.log n) ^ 2 * (μ n : ℝ)) =
      moebiusLogSqSummatory (N : ℝ) := by
    simp only [moebiusLogSqSummatory, Nat.floor_natCast]
    apply sum_congr rfl
    intro n _
    exact mul_comm _ _
  rw [hsum, Real.log_zero, zero_pow (by norm_num), zero_mul, sub_zero, ← hsplit] at habel
  dsimp only [v] at habel
  nlinarith

/-- A finite weighted supremum bound controls the Abel unweighting error.-/
theorem abs_mertens_mul_log_sq_le (N : ℕ) (hN : 2 ≤ N) (W : ℝ) (hW0 : 0 ≤ W)
    (hW : ∀ t ∈ Icc 2 N, |mertensSum t| * (Real.log t) ^ 6 / (t : ℝ) ≤ W) :
    |mertensSum N| * (Real.log N) ^ 2 ≤ |moebiusLogSqSummatory (N : ℝ)| +
      (Real.log 2) ^ 2 + 4 * W * (∑ t ∈ Icc 2 N, 1 / (Real.log t) ^ 5) := by
  let v : ℕ → ℝ := fun t =>
    ((Real.log ((t : ℝ) + 1)) ^ 2 - (Real.log t) ^ 2) * mertensSum t
  have htail : |∑ t ∈ Ico 2 N, v t| ≤
      4 * W * (∑ t ∈ Icc 2 N, 1 / (Real.log t) ^ 5) := by
    calc
      _ ≤ ∑ t ∈ Ico 2 N, |v t| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Ico 2 N, 4 * W * (1 / (Real.log t) ^ 5) := by
        apply sum_le_sum
        intro t ht
        have ht2 : 2 ≤ t := (mem_Ico.mp ht).1
        have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
        have ht0 : (0 : ℝ) < t := by linarith
        have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by linarith)
        have hstep := log_sq_succ_sub_bounds htR
        dsimp only [v]
        rw [abs_mul, abs_of_nonneg hstep.1]
        calc
          _ ≤ (4 * Real.log t / t) * |mertensSum t| :=
            mul_le_mul_of_nonneg_right hstep.2 (abs_nonneg _)
          _ = 4 * (|mertensSum t| * (Real.log t) ^ 6 / (t : ℝ)) /
              (Real.log t) ^ 5 := by field_simp
          _ ≤ 4 * W / (Real.log t) ^ 5 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hW t (mem_Icc.mpr
                ⟨ht2, (mem_Ico.mp ht).2.le⟩)) (by norm_num)) (by positivity)
          _ = _ := by ring
      _ = 4 * W * (∑ t ∈ Ico 2 N, 1 / (Real.log t) ^ 5) := by rw [mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro t ht
          exact mem_Icc.mpr ⟨(mem_Ico.mp ht).1, (mem_Ico.mp ht).2.le⟩
        · intro t ht _
          have hlog : 0 < Real.log (t : ℝ) :=
            Real.log_pos (by exact_mod_cast (show 1 < t by have := (mem_Icc.mp ht).1; omega))
          positivity
  have hmain := mertens_mul_log_sq_eq N hN
  have habs : |mertensSum N| * (Real.log N) ^ 2 = |mertensSum N * (Real.log N) ^ 2| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.log (N : ℝ)))]
  rw [habs, hmain]
  have h₁ := abs_add_le (moebiusLogSqSummatory (N : ℝ) + (Real.log 2) ^ 2)
    (∑ t ∈ Ico 2 N, v t)
  have h₂ := abs_add_le (moebiusLogSqSummatory (N : ℝ)) ((Real.log 2) ^ 2)
  rw [abs_of_nonneg (sq_nonneg (Real.log (2 : ℝ)))] at h₂
  dsimp only [v] at htail h₁
  linarith

/-- Normalized form of unweighting: the contribution of the finite supremum
has an additional inverse logarithm. The kernel bound is already proved.-/
theorem eventually_mertens_log_six_le_logSq_sum :
    ∀ᶠ N : ℕ in atTop, ∀ W : ℝ, 0 ≤ W →
      (∀ t ∈ Icc 2 N, |mertensSum t| * (Real.log t) ^ 6 / (t : ℝ) ≤ W) →
      |mertensSum N| * (Real.log N) ^ 6 / (N : ℝ) ≤
        (|moebiusLogSqSummatory (N : ℝ)| + (Real.log 2) ^ 2) *
          (Real.log N) ^ 4 / (N : ℝ) +
        (4 * (1 + (14 : ℝ) ^ 5)) * W / Real.log N := by
  filter_upwards [eventually_sum_inverse_log_five_le, eventually_ge_atTop 2] with N hkernel hN
  intro W hW0 hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hfinite := abs_mertens_mul_log_sq_le N hN W hW0 hW
  have hbound : |mertensSum N| * (Real.log N) ^ 2 ≤
      |moebiusLogSqSummatory (N : ℝ)| + (Real.log 2) ^ 2 +
        4 * W * ((1 + (14 : ℝ) ^ 5) * N / (Real.log N) ^ 5) := by
    have hscale := mul_le_mul_of_nonneg_left hkernel (by positivity : (0 : ℝ) ≤ 4 * W)
    exact hfinite.trans (add_le_add le_rfl hscale)
  calc
    _ = (|mertensSum N| * (Real.log N) ^ 2) * ((Real.log N) ^ 4 / (N : ℝ)) := by ring
    _ ≤ (|moebiusLogSqSummatory (N : ℝ)| + (Real.log 2) ^ 2 +
        4 * W * ((1 + (14 : ℝ) ^ 5) * N / (Real.log N) ^ 5)) *
        ((Real.log N) ^ 4 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = _ := by field_simp

/-- Real unweighting preserves the exact logarithm and bounds its final
fractional-interval increment separately.-/
theorem abs_mertensReal_mul_log_sq_le (x : ℝ) (hx : 4 ≤ x) (W : ℝ) (hW0 : 0 ≤ W)
    (hW : ∀ t : ℝ, 2 ≤ t → t ≤ x → |mertensReal t| * (Real.log t) ^ 6 / t ≤ W) :
    |mertensReal x| * (Real.log x) ^ 2 ≤ |moebiusLogSqSummatory x| +
      (Real.log 2) ^ 2 + 4 * W * (∑ t ∈ Icc 2 ⌊x⌋₊, 1 / (Real.log t) ^ 5) +
      4 * W / (Real.log x) ^ 5 := by
  have hx0 : 0 < x := by linarith
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hNr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have hNle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogle := Real.log_le_log hN0 hNle
  have hWnat : ∀ t ∈ Icc 2 ⌊x⌋₊,
      |mertensSum t| * (Real.log t) ^ 6 / (t : ℝ) ≤ W := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast (mem_Icc.mp ht).1
    have htx : (t : ℝ) ≤ x :=
      (show (t : ℝ) ≤ (⌊x⌋₊ : ℝ) by exact_mod_cast (mem_Icc.mp ht).2).trans hNle
    simpa only [mertensReal_eq, Nat.floor_natCast] using hW t ht2 htx
  have hfinite := abs_mertens_mul_log_sq_le ⌊x⌋₊ hN W hW0 hWnat
  have hS : moebiusLogSqSummatory (⌊x⌋₊ : ℝ) = moebiusLogSqSummatory x := by
    simp only [moebiusLogSqSummatory, Nat.floor_natCast]
  rw [hS, ← mertensReal_eq] at hfinite
  have hdiff : Real.log x - Real.log (⌊x⌋₊ : ℝ) ≤ 2 / x := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hlogle)] using abs_log_sub_log_natFloor_le hx
  have hsqdiff : (Real.log x) ^ 2 - (Real.log (⌊x⌋₊ : ℝ)) ^ 2 ≤ 4 * Real.log x / x := by
    calc
      _ = (Real.log x - Real.log (⌊x⌋₊ : ℝ)) *
          (Real.log x + Real.log (⌊x⌋₊ : ℝ)) := by ring
      _ ≤ (2 / x) * (2 * Real.log x) :=
        mul_le_mul hdiff (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  have hround : |mertensReal x| * ((Real.log x) ^ 2 - (Real.log (⌊x⌋₊ : ℝ)) ^ 2) ≤
      4 * W / (Real.log x) ^ 5 := by
    calc
      _ ≤ |mertensReal x| * (4 * Real.log x / x) :=
        mul_le_mul_of_nonneg_left hsqdiff (abs_nonneg _)
      _ = 4 * (|mertensReal x| * (Real.log x) ^ 6 / x) / (Real.log x) ^ 5 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hW x (by linarith) le_rfl) (by norm_num)) (by positivity)
  nlinarith

/-- The real normalized form feeds a supremum on a real initial interval.
Its main coefficient remains one, and the additional supremum coefficient
tends to zero as an inverse logarithm.-/
theorem eventually_mertensReal_log_six_le_logSq_sum :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 0 ≤ W →
      (∀ t : ℝ, 2 ≤ t → t ≤ x → |mertensReal t| * (Real.log t) ^ 6 / t ≤ W) →
      |mertensReal x| * (Real.log x) ^ 6 / x ≤
        (|moebiusLogSqSummatory x| + (Real.log 2) ^ 2) * (Real.log x) ^ 4 / x +
        (128 * (1 + (14 : ℝ) ^ 5) + 4) * W / Real.log x := by
  have hkernel := (tendsto_nat_floor_atTop (α := ℝ)).eventually eventually_sum_inverse_log_five_le
  filter_upwards [hkernel, eventually_ge_atTop (4 : ℝ)] with x hkernel hx
  intro W hW0 hW
  let C : ℝ := 1 + (14 : ℝ) ^ 5
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hx0 : 0 < x := by linarith
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hNr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have hNle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogs : (Real.log x) ^ 5 ≤ 32 * (Real.log (⌊x⌋₊ : ℝ)) ^ 5 := by
    have h := pow_le_pow_left₀ hlog.le (log_le_two_log_natFloor hx) 5
    nlinarith [h]
  have hrecip : 1 / (Real.log (⌊x⌋₊ : ℝ)) ^ 5 ≤ 32 / (Real.log x) ^ 5 := by
    exact (div_le_div_iff₀ (pow_pos hlogN _) (pow_pos hlog _)).mpr (by simpa only [one_mul] using hlogs)
  have hkernelReal : (∑ t ∈ Icc 2 ⌊x⌋₊, 1 / (Real.log t) ^ 5) ≤
      32 * C * x / (Real.log x) ^ 5 := by
    apply hkernel.trans
    change C * (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊ : ℝ)) ^ 5 ≤ _
    calc
      _ = (C * (⌊x⌋₊ : ℝ)) * (1 / (Real.log (⌊x⌋₊ : ℝ)) ^ 5) := by ring
      _ ≤ (C * x) * (32 / (Real.log x) ^ 5) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hNle hC) hrecip (by positivity) (by positivity)
      _ = _ := by ring
  have hfinite := abs_mertensReal_mul_log_sq_le x hx W hW0 hW
  have hround : 4 * W / (Real.log x) ^ 5 ≤ 4 * W * x / (Real.log x) ^ 5 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hmain : |mertensReal x| * (Real.log x) ^ 2 ≤
      |moebiusLogSqSummatory x| + (Real.log 2) ^ 2 + (128 * C + 4) * W * x / (Real.log x) ^ 5 := by
    have hh := mul_le_mul_of_nonneg_left hkernelReal (by positivity : (0 : ℝ) ≤ 4 * W)
    have heq : 4 * W * (32 * C * x / (Real.log x) ^ 5) +
        4 * W * x / (Real.log x) ^ 5 = (128 * C + 4) * W * x / (Real.log x) ^ 5 := by ring
    linarith
  calc
    _ = (|mertensReal x| * (Real.log x) ^ 2) * ((Real.log x) ^ 4 / x) := by ring
    _ ≤ (|moebiusLogSqSummatory x| + (Real.log 2) ^ 2 +
        (128 * C + 4) * W * x / (Real.log x) ^ 5) * ((Real.log x) ^ 4 / x) :=
      mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = _ := by dsimp [C]; field_simp

end TwinPrime.Analytic
