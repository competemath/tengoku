import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocal
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The reciprocal prime estimate at real endpoints

The logarithm uses the actual real endpoint. The floor error in its argument
is bounded separately, so the centering constant and logarithmic rate pass
from the integer theorem without silently rounding a logarithm.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

def realPrimeReciprocalSum (x : ℝ) : ℝ := primeReciprocalSum ⌊x⌋₊

theorem abs_log_sub_log_natFloor_le {x : ℝ} (hx : 4 ≤ x) :
    |Real.log x - Real.log (⌊x⌋₊ : ℝ)| ≤ 2 / x := by
  have hx0 : 0 < x := by linarith
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hnr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < ⌊x⌋₊ := by linarith
  have hnle := Nat.floor_le hx0.le
  have hfloor := Nat.lt_floor_add_one x
  have hhalf : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 hnle))]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx0 hn0)
  rw [Real.log_div hx0.ne' hn0.ne'] at hlog
  calc
    _ ≤ x / (⌊x⌋₊ : ℝ) - 1 := hlog
    _ ≤ 1 / (⌊x⌋₊ : ℝ) := by
      have h := (div_le_div_iff_of_pos_right hn0).mpr hfloor.le
      have hid : ((⌊x⌋₊ : ℝ) + 1) / (⌊x⌋₊ : ℝ) = 1 + 1 / (⌊x⌋₊ : ℝ) := by field_simp
      rw [hid] at h
      linarith
    _ ≤ 2 / x := (div_le_div_iff₀ hn0 hx0).mpr (by simpa using hhalf)

/-- A centered reciprocal estimate extends to real arguments with no change
to its logarithmic exponent.-/
theorem primeReciprocal_real_center_bound_of_nat (c C : ℝ) (hC : 0 ≤ C)
    (hcenter : ∀ᶠ N : ℕ in atTop,
      |primeReciprocalSum N - Real.log N - c| ≤ C / (Real.log N) ^ 5) :
    ∀ᶠ x : ℝ in atTop,
      |realPrimeReciprocalSum x - Real.log x - c| ≤
        (32 * C + 2) / (Real.log x) ^ 5 := by
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).eventually hcenter
  filter_upwards [hfloor, eventually_ge_atTop (4 : ℝ), eventually_log_pow_le_self 5]
    with x hcenter hx hpow
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hnr : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hlogn : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogs : (Real.log x) ^ 5 ≤ 32 * (Real.log (⌊x⌋₊ : ℝ)) ^ 5 := by
    have h := pow_le_pow_left₀ hlogx.le (log_le_two_log_natFloor hx) 5
    nlinarith [h]
  have hmain : C / (Real.log (⌊x⌋₊ : ℝ)) ^ 5 ≤ 32 * C / (Real.log x) ^ 5 := by
    apply (div_le_div_iff₀ (pow_pos hlogn _) (pow_pos hlogx _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogs hC]
  have hround : 2 / x ≤ 2 / (Real.log x) ^ 5 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hlogx _) hpow
  calc
    _ = |(primeReciprocalSum ⌊x⌋₊ - Real.log (⌊x⌋₊ : ℝ) - c) +
        (Real.log (⌊x⌋₊ : ℝ) - Real.log x)| := by unfold realPrimeReciprocalSum; congr 1; ring
    _ ≤ |primeReciprocalSum ⌊x⌋₊ - Real.log (⌊x⌋₊ : ℝ) - c| +
        |Real.log (⌊x⌋₊ : ℝ) - Real.log x| := abs_add_le _ _
    _ ≤ C / (Real.log (⌊x⌋₊ : ℝ)) ^ 5 + 2 / x := by
      rw [abs_sub_comm (Real.log (⌊x⌋₊ : ℝ))]
      exact add_le_add hcenter (abs_log_sub_log_natFloor_le hx)
    _ ≤ 32 * C / (Real.log x) ^ 5 + 2 / (Real.log x) ^ 5 := add_le_add hmain hround
    _ = _ := by ring

theorem exists_realPrimeReciprocalSum_center_of_psi_log_six (K : ℝ) (hK : 0 ≤ K)
    (hψ : ∀ᶠ N : ℕ in atTop,
      |Chebyshev.psi N - (N : ℝ)| ≤ K * N / (Real.log N) ^ 6) :
    ∃ c C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |realPrimeReciprocalSum x - Real.log x - c| ≤ C / (Real.log x) ^ 5 := by
  obtain ⟨c, _, C, hC, hcenter⟩ := exists_primeReciprocalSum_center_of_psi_log_six K hK hψ
  exact ⟨c, 32 * C + 2, by positivity, primeReciprocal_real_center_bound_of_nat c C hC hcenter⟩

theorem MaximalBombieriVinogradov.real_primeReciprocal_center
    (hBV : MaximalBombieriVinogradov) :
    ∃ c C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |realPrimeReciprocalSum x - Real.log x - c| ≤ C / (Real.log x) ^ 5 := by
  obtain ⟨K, hK, hψ⟩ := hBV.psi_error 6 (by norm_num)
  exact exists_realPrimeReciprocalSum_center_of_psi_log_six K hK.le (by simpa using hψ)

end TwinPrime.Analytic
