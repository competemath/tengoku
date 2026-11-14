import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusAbel
import Tengoku.Twinprime.TwinPrime.Analytic.BombieriVinogradovPsi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A quantitative reciprocal prime sum from the ordinary prime error

The sixth-power logarithmic error for `ψ(N)` gives convergence of
`∑_{0<n≤N} Λ(n)/n - log N` and a fifth-power logarithmic remainder.
The constant is obtained from the generic Abel limit applied to `Λ(n)-1`
and the harmonic limit. Its numerical value is not assumed or identified.
-/

noncomputable section

open Finset Filter ArithmeticFunction

namespace TwinPrime.Analytic

/-- The positive-integer reciprocal von Mangoldt sum.-/
def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, vonMangoldt n / n

/-- Centering the prime coefficient by one on positive integers.-/
def primeErrorCoefficient (n : ℕ) : ℝ :=
  if n = 0 then 0 else vonMangoldt n - 1

/--
@isnad1 id=eq.0h1v.s4.72cd34c67333 from=translated src=- shape=90f40ee9 vocab=2078fb72
-/
theorem coefficientSum_primeErrorCoefficient (N : ℕ) :
    coefficientSum primeErrorCoefficient N = Chebyshev.psi (N : ℝ) - N := by
  have hsum : coefficientSum primeErrorCoefficient N =
      ∑ n ∈ Ioc 0 N, (vonMangoldt n - 1) := by
    apply sum_congr rfl
    intro n hn
    simp only [primeErrorCoefficient, ite_eq_right (Nat.ne_of_gt (mem_Ioc.mp hn).1)]
  rw [hsum, sum_sub_distrib]
  simp [Chebyshev.psi]

/--
@isnad1 id=eq.0h1v.s4.4e427a89128f from=translated src=- shape=6a12ad02 vocab=ad4ce2b8
-/
theorem reciprocalCoefficientSum_primeErrorCoefficient (N : ℕ) :
    reciprocalCoefficientSum primeErrorCoefficient N =
      primeReciprocalSum N - (harmonic N : ℝ) := by
  have hI : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  have hsum : reciprocalCoefficientSum primeErrorCoefficient N =
      ∑ n ∈ Ioc 0 N, (vonMangoldt n - 1) / n := by
    apply sum_congr rfl
    intro n hn
    simp only [primeErrorCoefficient, ite_eq_right (Nat.ne_of_gt (mem_Ioc.mp hn).1)]
  rw [hsum]
  simp_rw [sub_div]
  rw [sum_sub_distrib]
  congr 1
  simp [hI, harmonic_eq_sum_Icc, one_div]

/-- The harmonic remainder is at most one reciprocal input.
@isnad1 id=le.1h1v.s5.07fceb35213c from=translated src=- shape=d3d8b84a vocab=000cc0dc
-/
theorem abs_harmonic_sub_log_sub_eulerMascheroni_le (N : ℕ) (hN : 1 ≤ N) :
    |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hγlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have hγhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq',
    show N ≠ 0 by omega, ite_false] at hγlo hγhi
  have hinc : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by linarith : (0 : ℝ) < N + 1) hNr)
    rw [Real.log_div (by positivity : (N : ℝ) + 1 ≠ 0) hNr.ne'] at h
    convert h using 1
    field_simp
    ring
  rw [abs_of_nonneg (by linarith)]
  linarith

private theorem eventually_one_div_nat_le_log_five :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) / N ≤ 1 / (Real.log N) ^ 5 := by
  have hreal : Tendsto (fun x : ℝ => (Real.log x) ^ 5 / x) atTop (nhds 0) := by
    simpa only [Real.rpow_ofNat, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (5 : ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hnat.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 2] with N hsmall hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : (Real.log (N : ℝ)) ^ 5 ≤ N :=
    le_of_lt (by simpa only [one_mul] using (div_lt_iff₀ hNr).mp hsmall)
  exact (div_le_div_iff₀ hNr (pow_pos hlog 5)).mpr (by simpa using hpow)

/-- A sixth-power ordinary prime error gives a centered reciprocal limit
with an explicit fifth-power remainder constant.
@isnad1 id=ex.2h1v.s7.b76ede0dbdf1 from=translated src=- shape=f2b44031 vocab=2e6e07f0
-/
theorem exists_primeReciprocalSum_center_bound_of_psi_log_six
    (K : ℝ) (hK : 0 ≤ K)
    (hψ : ∀ᶠ N : ℕ in atTop,
      |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ K * N / (Real.log N) ^ 6) :
    ∃ c : ℝ,
      Tendsto (fun N : ℕ => primeReciprocalSum N - Real.log N) atTop (nhds c) ∧
      ∀ᶠ N : ℕ in atTop,
        |primeReciprocalSum N - Real.log N - c| ≤
          ((32 + 2 / Real.log 2) * K + 1) / (Real.log N) ^ 5 := by
  have hE : ∀ᶠ N : ℕ in atTop,
      |coefficientSum primeErrorCoefficient N| ≤ K * N / (Real.log N) ^ 6 := by
    simpa only [coefficientSum_primeErrorCoefficient] using hψ
  obtain ⟨L, hL, htail⟩ :=
    exists_reciprocalCoefficientSum_limit_of_log_six primeErrorCoefficient K hK hE
  refine ⟨L + Real.eulerMascheroniConstant, ?_, ?_⟩
  · have heq : (fun N : ℕ => primeReciprocalSum N - Real.log N) =
        fun N : ℕ => reciprocalCoefficientSum primeErrorCoefficient N +
          ((harmonic N : ℝ) - Real.log N) := by
      funext N
      rw [reciprocalCoefficientSum_primeErrorCoefficient]
      ring
    rw [heq]
    exact hL.add Real.tendsto_harmonic_sub_log
  · filter_upwards [htail, eventually_one_div_nat_le_log_five,
      eventually_ge_atTop 1] with N htailN hsmallN hN
    have heq : primeReciprocalSum N - Real.log N -
        (L + Real.eulerMascheroniConstant) =
        (reciprocalCoefficientSum primeErrorCoefficient N - L) +
          ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) := by
      rw [reciprocalCoefficientSum_primeErrorCoefficient]
      ring
    rw [heq]
    calc
      _ ≤ |reciprocalCoefficientSum primeErrorCoefficient N - L| +
          |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| := abs_add_le _ _
      _ ≤ (32 + 2 / Real.log 2) * K / (Real.log N) ^ 5 + 1 / N :=
        add_le_add htailN (abs_harmonic_sub_log_sub_eulerMascheroni_le N hN)
      _ ≤ (32 + 2 / Real.log 2) * K / (Real.log N) ^ 5 + 1 / (Real.log N) ^ 5 :=
        add_le_add le_rfl hsmallN
      _ = _ := by ring

/-- The quantitative prime-to-reciprocal bridge with an explicitly
nonnegative remainder constant.
@isnad1 id=ex.2h1v.s7.e7c201354976 from=translated src=- shape=7283e8ca vocab=227f4530
-/
theorem exists_primeReciprocalSum_center_of_psi_log_six
    (K : ℝ) (hK : 0 ≤ K)
    (hψ : ∀ᶠ N : ℕ in atTop,
      |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ K * N / (Real.log N) ^ 6) :
    ∃ c : ℝ,
      Tendsto (fun N : ℕ => primeReciprocalSum N - Real.log N) atTop (nhds c) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
        |primeReciprocalSum N - Real.log N - c| ≤ C / (Real.log N) ^ 5 := by
  obtain ⟨c, hc, hbound⟩ := exists_primeReciprocalSum_center_bound_of_psi_log_six K hK hψ
  refine ⟨c, hc, (32 + 2 / Real.log 2) * K + 1, ?_, hbound⟩
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

end TwinPrime.Analytic
