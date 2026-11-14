import Tengoku.Twinprime.TwinPrime.Analytic.SelbergSummatory
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocalReal
import Tengoku.Twinprime.TwinPrime.Analytic.LogFactorial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmically weighted prime sums

Discrete partial summation transfers the maximal ordinary prime error to
the logarithmically weighted sum. An elementary bound for the sum of logs
identifies its main term, including the linear term. The real-endpoint
rounding error is explicit. The distribution hypothesis remains an input.
-/

noncomputable section

open Finset Filter ArithmeticFunction

namespace TwinPrime.Analytic

theorem primeLogSummatory_nat (N : ℕ) :
    primeLogSummatory N = ∑ n ∈ Ioc 0 N, vonMangoldt n * Real.log n := by
  simp [primeLogSummatory, arithmeticSummatory]

theorem primeLogSummatory_sub_sum_log (N : ℕ) :
    primeLogSummatory N - (∑ n ∈ Ioc 0 N, Real.log n) =
      ∑ n ∈ Ioc 0 N, Real.log n * primeErrorCoefficient n := by
  rw [primeLogSummatory_nat, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  simp only [primeErrorCoefficient, ite_eq_right (Nat.ne_of_gt (mem_Ioc.mp hn).1)]
  ring

/-- A maximal unweighted error costs at most twice the final logarithm.-/
theorem abs_primeLogSummatory_sub_sum_log_le (N : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hψ : ∀ t ≤ N, |Chebyshev.psi (t : ℝ) - (t : ℝ)| ≤ M) :
    |primeLogSummatory N - (∑ n ∈ Ioc 0 N, Real.log n)| ≤
      2 * M * Real.log N := by
  rw [primeLogSummatory_sub_sum_log]
  apply abs_sum_Ioc_mul_le_of_partial_sums 0 N (Nat.zero_le N)
    (fun n => Real.log n) primeErrorCoefficient M hM (by simp)
  · intro i _ j _ hij
    by_cases hi : i = 0
    · simpa [hi] using Real.log_natCast_nonneg j
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hi)
        (by exact_mod_cast hij)
  · intro t ht
    change |coefficientSum primeErrorCoefficient t| ≤ M
    rw [coefficientSum_primeErrorCoefficient]
    exact hψ t (mem_Icc.mp ht).2

theorem MaximalBombieriVinogradov.primeLog_sub_sum_log
    (hBV : MaximalBombieriVinogradov) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      |primeLogSummatory N - (∑ n ∈ Ioc 0 N, Real.log n)| ≤
        K * N / (Real.log N) ^ 5 := by
  obtain ⟨K, hK, hψ⟩ := hBV.maximal_psi_error 6 (by norm_num)
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hψ, eventually_ge_atTop 2] with N hψ hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hψ' : ∀ t ≤ N, |Chebyshev.psi (t : ℝ) - (t : ℝ)| ≤
      K * N / (Real.log N) ^ 6 := by
    intro t ht
    simpa using hψ t (by omega)
  calc
    _ ≤ 2 * (K * N / (Real.log N) ^ 6) * Real.log N :=
      abs_primeLogSummatory_sub_sum_log_le N _ (by positivity) hψ'
    _ = _ := by field_simp

/-- The maximal BV hypothesis supplies the weighted prime main term at
integer endpoints with five logarithmic powers of saving.-/
theorem MaximalBombieriVinogradov.primeLog_nat_error
    (hBV : MaximalBombieriVinogradov) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      |primeLogSummatory N - ((N : ℝ) * Real.log N - N)| ≤
        K * N / (Real.log N) ^ 5 := by
  obtain ⟨K, hK, hP⟩ := hBV.primeLog_sub_sum_log
  refine ⟨K + 2, by positivity, ?_⟩
  have h5 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_log_pow_le_self 5)
  have h6 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_log_pow_le_self 6)
  filter_upwards [hP, h5, h6, eventually_ge_atTop 2] with N hP h5 h6 hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hround : 1 + Real.log N ≤ 2 * N / (Real.log N) ^ 5 := by
    apply (le_div_iff₀ (pow_pos hlog _)).mpr
    nlinarith [h5, h6]
  calc
    _ ≤ |primeLogSummatory N - (∑ n ∈ Ioc 0 N, Real.log n)| +
        |(∑ n ∈ Ioc 0 N, Real.log n) - ((N : ℝ) * Real.log N - N)| :=
      abs_sub_le _ _ _
    _ ≤ K * N / (Real.log N) ^ 5 + (1 + Real.log N) :=
      add_le_add hP (abs_sum_log_sub_main_le_one_add_log N)
    _ ≤ K * N / (Real.log N) ^ 5 + 2 * N / (Real.log N) ^ 5 :=
      add_le_add le_rfl hround
    _ = _ := by ring

/-- The main term changes by at most a logarithm plus an absolute constant
when its real argument is rounded down.-/
theorem abs_log_mainTerm_natFloor_sub_le (x : ℝ) (hx : 4 ≤ x) :
    |((⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - ⌊x⌋₊) -
      (x * Real.log x - x)| ≤ Real.log x + 3 := by
  have hx0 : 0 < x := by linarith
  have hnle := Nat.floor_le hx0.le
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hfloor := Nat.abs_floor_sub_le hx0.le
  have hlogdiff : |Real.log (⌊x⌋₊ : ℝ) - Real.log x| ≤ 2 / x := by
    rw [abs_sub_comm]
    exact abs_log_sub_log_natFloor_le hx
  calc
    _ = |(⌊x⌋₊ : ℝ) * (Real.log (⌊x⌋₊ : ℝ) - Real.log x) +
        ((⌊x⌋₊ : ℝ) - x) * Real.log x - ((⌊x⌋₊ : ℝ) - x)| := by congr 1; ring
    _ ≤ |(⌊x⌋₊ : ℝ) * (Real.log (⌊x⌋₊ : ℝ) - Real.log x)| +
        |((⌊x⌋₊ : ℝ) - x) * Real.log x| + |(⌊x⌋₊ : ℝ) - x| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (⌊x⌋₊ : ℝ) * (2 / x) + 1 * Real.log x + 1 := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ⌊x⌋₊ by positivity), abs_of_nonneg hlog]
      gcongr
    _ ≤ x * (2 / x) + 1 * Real.log x + 1 := by gcongr
    _ = _ := by field_simp; ring

/-- A fifth-power weighted prime error passes from integers to real inputs.-/
theorem primeLog_real_error_of_nat_error (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ᶠ N : ℕ in atTop,
      |primeLogSummatory N - ((N : ℝ) * Real.log N - N)| ≤
        K * N / (Real.log N) ^ 5) :
    ∀ᶠ x : ℝ in atTop,
      |primeLogSummatory x - (x * Real.log x - x)| ≤
        (32 * K + 4) * x / (Real.log x) ^ 5 := by
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).eventually hP
  filter_upwards [hfloor, eventually_ge_atTop (4 : ℝ), eventually_log_pow_le_self 5,
    eventually_log_pow_le_self 6] with x hP hx hpow5 hpow6
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hnr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hlogn : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hnle := Nat.floor_le hx0.le
  have hlogs : (Real.log x) ^ 5 ≤ 32 * (Real.log (⌊x⌋₊ : ℝ)) ^ 5 := by
    have h := pow_le_pow_left₀ hlogx.le (log_le_two_log_natFloor hx) 5
    nlinarith [h]
  have hmain : K * (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊ : ℝ)) ^ 5 ≤
      32 * K * x / (Real.log x) ^ 5 := by
    apply (div_le_div_iff₀ (pow_pos hlogn _) (pow_pos hlogx _)).mpr
    calc
      _ ≤ K * x * (32 * (Real.log (⌊x⌋₊ : ℝ)) ^ 5) := by gcongr
      _ = _ := by ring
  have hround : Real.log x + 3 ≤ 4 * x / (Real.log x) ^ 5 := by
    apply (le_div_iff₀ (pow_pos hlogx _)).mpr
    nlinarith [hpow5, hpow6]
  have hconst : primeLogSummatory x = primeLogSummatory (⌊x⌋₊ : ℝ) := by
    simp [primeLogSummatory, arithmeticSummatory]
  calc
    _ ≤ |primeLogSummatory (⌊x⌋₊ : ℝ) -
          ((⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - ⌊x⌋₊)| +
        |((⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - ⌊x⌋₊) -
          (x * Real.log x - x)| := by
      rw [hconst]
      exact abs_sub_le _ _ _
    _ ≤ K * (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊ : ℝ)) ^ 5 + (Real.log x + 3) :=
      add_le_add hP (abs_log_mainTerm_natFloor_sub_le x hx)
    _ ≤ 32 * K * x / (Real.log x) ^ 5 + 4 * x / (Real.log x) ^ 5 :=
      add_le_add hmain hround
    _ = _ := by ring

/-- Real weighted prime asymptotics, deduced from the named BV hypothesis.-/
theorem MaximalBombieriVinogradov.primeLog_real_error
    (hBV : MaximalBombieriVinogradov) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      |primeLogSummatory x - (x * Real.log x - x)| ≤
        K * x / (Real.log x) ^ 5 := by
  obtain ⟨K, hK, hP⟩ := hBV.primeLog_nat_error
  exact ⟨32 * K + 4, by positivity, primeLog_real_error_of_nat_error K hK hP⟩

end TwinPrime.Analytic
