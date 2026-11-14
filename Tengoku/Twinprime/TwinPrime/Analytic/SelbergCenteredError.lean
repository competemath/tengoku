import Tengoku.Twinprime.TwinPrime.Analytic.SelbergSummatory
import Tengoku.Twinprime.TwinPrime.Analytic.SelbergCoefficientBounds
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocalReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The centered Selberg summatory error

The real prime error, reciprocal prime error and logarithmically weighted
prime error are combined through the exact square-root hyperbola identity.
Every floor correction and signed term is retained before taking bounds.
-/

noncomputable section

open Finset Filter ArithmeticFunction

namespace TwinPrime.Analytic

/-- The prime-error convolution in the symmetric square-root split.-/
def primeConvolutionError (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊,
    vonMangoldt n * (Chebyshev.psi (x / n) - x / n)

/-- Exact expansion into the three analytic errors and the floor correction.-/
theorem centeredSelbergSummatory_sqrt_error (c x : ℝ) (hx : 1 ≤ x) :
    centeredSelbergSummatory c x =
      2 * x * (realPrimeReciprocalSum (Real.sqrt x) - Real.log (Real.sqrt x) - c) +
      2 * primeConvolutionError x -
      2 * Real.sqrt x * (Chebyshev.psi (Real.sqrt x) - Real.sqrt x) -
      (Chebyshev.psi (Real.sqrt x) - Real.sqrt x) ^ 2 -
      (primeLogSummatory x - (x * Real.log x - x)) +
      2 * c * (x - (⌊x⌋₊ : ℝ)) := by
  have hsum : (∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, vonMangoldt n * Chebyshev.psi (x / n)) =
      x * realPrimeReciprocalSum (Real.sqrt x) + primeConvolutionError x := by
    unfold realPrimeReciprocalSum primeReciprocalSum primeConvolutionError
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [centeredSelbergSummatory_eq, vonMangoldt_convolution_sqrt x hx, hsum,
    Real.log_sqrt (by linarith : 0 ≤ x)]
  nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x)]

/-- An unconditional reciprocal prime mass bound at a real endpoint.-/
theorem realPrimeReciprocalSum_le_log (y : ℝ) (hy : 1 ≤ y) :
    realPrimeReciprocalSum y ≤ chebyshevLinearConstant * (2 + Real.log y) := by
  have hfloor : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hfloor0 : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast hfloor
  apply (primeReciprocalSum_le_log ⌊y⌋₊ hfloor).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (Real.log_le_log hfloor0 (Nat.floor_le (by linarith))))
    chebyshevLinearConstant_nonneg

/-- The convolution error loses exactly one logarithmic power.-/
theorem abs_primeConvolutionError_le (x K : ℝ) (hx : 1 ≤ x)
    (hlog : 2 ≤ Real.log x) (hK : 0 ≤ K)
    (hψ : ∀ t : ℝ, Real.sqrt x ≤ t →
      |Chebyshev.psi t - t| ≤ K * t / (Real.log t) ^ 6) :
    |primeConvolutionError x| ≤
      128 * chebyshevLinearConstant * K * x / (Real.log x) ^ 5 := by
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hy0 : 0 < Real.sqrt x := by linarith
  have hlogx : 0 < Real.log x := by linarith
  have hlogy : 0 < Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx0.le]; positivity
  have hsum : |primeConvolutionError x| ≤
      (K * x / (Real.log (Real.sqrt x)) ^ 6) * realPrimeReciprocalSum (Real.sqrt x) := by
    unfold primeConvolutionError realPrimeReciprocalSum primeReciprocalSum
    rw [mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    have hnle : (n : ℝ) ≤ Real.sqrt x :=
      (show (n : ℝ) ≤ ⌊Real.sqrt x⌋₊ by exact_mod_cast (mem_Ioc.mp hn).2).trans
        (Nat.floor_le hy0.le)
    have hquot : Real.sqrt x ≤ x / n := by
      apply (le_div_iff₀ hn0).mpr
      calc
        _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hnle hy0.le
        _ = x := Real.mul_self_sqrt hx0.le
    have hq0 : 0 < x / n := div_pos hx0 hn0
    have hlogle : Real.log (Real.sqrt x) ≤ Real.log (x / n) := Real.log_le_log hy0 hquot
    rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    calc
      _ ≤ vonMangoldt n * (K * (x / n) / (Real.log (x / n)) ^ 6) :=
        mul_le_mul_of_nonneg_left (hψ (x / n) hquot) vonMangoldt_nonneg
      _ ≤ vonMangoldt n * (K * (x / n) / (Real.log (Real.sqrt x)) ^ 6) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
          (mul_nonneg hK hq0.le) (pow_pos hlogy 6)
          (pow_le_pow_left₀ hlogy.le hlogle 6)) vonMangoldt_nonneg
      _ = _ := by ring
  have hmass : realPrimeReciprocalSum (Real.sqrt x) ≤
      2 * chebyshevLinearConstant * Real.log x := by
    apply (realPrimeReciprocalSum_le_log (Real.sqrt x) hy).trans
    rw [Real.log_sqrt hx0.le]
    have h := mul_le_mul_of_nonneg_left
      (show 2 + Real.log x / 2 ≤ 2 * Real.log x by linarith) chebyshevLinearConstant_nonneg
    nlinarith
  calc
    _ ≤ (K * x / (Real.log (Real.sqrt x)) ^ 6) * realPrimeReciprocalSum (Real.sqrt x) := hsum
    _ ≤ (K * x / (Real.log (Real.sqrt x)) ^ 6) *
        (2 * chebyshevLinearConstant * Real.log x) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by rw [Real.log_sqrt hx0.le]; field_simp; ring

private theorem abs_six_error_terms (a b c d e f : ℝ) :
    |a + b - c - d - e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h₁ := abs_add_le a b
  have h₂ := abs_sub (a + b) c
  have h₃ := abs_sub (a + b - c) d
  have h₄ := abs_sub (a + b - c - d) e
  have h₅ := abs_add_le (a + b - c - d - e) f
  linarith

/-- The complete finite bound for the centered error. The three analytic
premises occur only at their actual real arguments.-/
theorem abs_centeredSelbergSummatory_le_of_prime_errors
    (c x Kψ KL KP : ℝ) (hx : 1 ≤ x) (hlog : 2 ≤ Real.log x)
    (hpow : (Real.log x) ^ 5 ≤ x)
    (hKψ : 0 ≤ Kψ) (_hKL : 0 ≤ KL) (_hKP : 0 ≤ KP)
    (hψ : ∀ t : ℝ, Real.sqrt x ≤ t →
      |Chebyshev.psi t - t| ≤ Kψ * t / (Real.log t) ^ 6)
    (hL : |realPrimeReciprocalSum (Real.sqrt x) - Real.log (Real.sqrt x) - c| ≤
      KL / (Real.log (Real.sqrt x)) ^ 5)
    (hP : |primeLogSummatory x - (x * Real.log x - x)| ≤ KP * x / (Real.log x) ^ 5) :
    |centeredSelbergSummatory c x| ≤
      (64 * KL + 256 * chebyshevLinearConstant * Kψ + 128 * Kψ +
        4096 * Kψ ^ 2 + KP + 2 * |c|) * x / (Real.log x) ^ 5 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hy2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
  have hl0 : 0 < Real.log x := by linarith
  have hl1 : 1 ≤ Real.log x := by linarith
  have hR : |Chebyshev.psi (Real.sqrt x) - Real.sqrt x| ≤
      64 * Kψ * Real.sqrt x / (Real.log x) ^ 6 := by
    have h := hψ (Real.sqrt x) le_rfl
    rw [Real.log_sqrt hx0.le] at h
    calc
      _ ≤ Kψ * Real.sqrt x / (Real.log x / 2) ^ 6 := h
      _ = _ := by field_simp; ring
  have hfirst : |2 * x *
      (realPrimeReciprocalSum (Real.sqrt x) - Real.log (Real.sqrt x) - c)| ≤
      64 * KL * x / (Real.log x) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * x)]
    calc
      _ ≤ 2 * x * (KL / (Real.log (Real.sqrt x)) ^ 5) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by rw [Real.log_sqrt hx0.le]; field_simp; ring
  have hsecond : |2 * primeConvolutionError x| ≤
      256 * chebyshevLinearConstant * Kψ * x / (Real.log x) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mul_le_mul_of_nonneg_left (abs_primeConvolutionError_le x Kψ hx hlog hKψ hψ)
      (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ ≤ 2 * (128 * chebyshevLinearConstant * Kψ * x / (Real.log x) ^ 5) := h
      _ = _ := by ring
  have hthird : |2 * Real.sqrt x * (Chebyshev.psi (Real.sqrt x) - Real.sqrt x)| ≤
      128 * Kψ * x / (Real.log x) ^ 5 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt x)]
    calc
      _ ≤ 2 * Real.sqrt x * (64 * Kψ * Real.sqrt x / (Real.log x) ^ 6) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ = 128 * Kψ * (Real.sqrt x) ^ 2 / (Real.log x) ^ 6 := by ring
      _ = 128 * Kψ * x / (Real.log x) ^ 6 := by rw [hy2]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hl0 5)
        (pow_le_pow_right₀ hl1 (by decide : 5 ≤ 6))
  have hfourth : |(Chebyshev.psi (Real.sqrt x) - Real.sqrt x) ^ 2| ≤
      4096 * Kψ ^ 2 * x / (Real.log x) ^ 5 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hs : (Chebyshev.psi (Real.sqrt x) - Real.sqrt x) ^ 2 ≤
        (64 * Kψ * Real.sqrt x / (Real.log x) ^ 6) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hR 2
    calc
      _ ≤ (64 * Kψ * Real.sqrt x / (Real.log x) ^ 6) ^ 2 := hs
      _ = 4096 * Kψ ^ 2 * (Real.sqrt x) ^ 2 / (Real.log x) ^ 12 := by ring
      _ = 4096 * Kψ ^ 2 * x / (Real.log x) ^ 12 := by rw [hy2]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hl0 5)
        (pow_le_pow_right₀ hl1 (by decide : 5 ≤ 12))
  have hsixth : |2 * c * (x - (⌊x⌋₊ : ℝ))| ≤
      2 * |c| * x / (Real.log x) ^ 5 := by
    have hfloor : |x - (⌊x⌋₊ : ℝ)| ≤ 1 := by
      simpa only [abs_sub_comm] using Nat.abs_floor_sub_le hx0.le
    have hscale : (1 : ℝ) ≤ x / (Real.log x) ^ 5 :=
      (le_div_iff₀ (pow_pos hl0 5)).mpr (by simpa using hpow)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * |c| * 1 := mul_le_mul_of_nonneg_left hfloor (by positivity)
      _ ≤ 2 * |c| * (x / (Real.log x) ^ 5) := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  rw [centeredSelbergSummatory_sqrt_error c x hx]
  calc
    _ ≤ |2 * x * (realPrimeReciprocalSum (Real.sqrt x) - Real.log (Real.sqrt x) - c)| +
        |2 * primeConvolutionError x| +
        |2 * Real.sqrt x * (Chebyshev.psi (Real.sqrt x) - Real.sqrt x)| +
        |(Chebyshev.psi (Real.sqrt x) - Real.sqrt x) ^ 2| +
        |primeLogSummatory x - (x * Real.log x - x)| +
        |2 * c * (x - (⌊x⌋₊ : ℝ))| := abs_six_error_terms _ _ _ _ _ _
    _ ≤ 64 * KL * x / (Real.log x) ^ 5 +
        256 * chebyshevLinearConstant * Kψ * x / (Real.log x) ^ 5 +
        128 * Kψ * x / (Real.log x) ^ 5 +
        4096 * Kψ ^ 2 * x / (Real.log x) ^ 5 +
        KP * x / (Real.log x) ^ 5 + 2 * |c| * x / (Real.log x) ^ 5 := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hfirst hsecond)
        hthird) hfourth) hP) hsixth
    _ = _ := by ring

/-- The centered summatory error follows from the three real prime estimates;
no additional cancellation estimate for the centered coefficient is assumed.-/
theorem exists_centeredSelbergSummatory_bound_of_prime_errors
    (c Kψ KL KP : ℝ) (hKψ : 0 ≤ Kψ) (hKL : 0 ≤ KL) (hKP : 0 ≤ KP)
    (hψ : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ Kψ * x / (Real.log x) ^ 6)
    (hL : ∀ᶠ x : ℝ in atTop,
      |realPrimeReciprocalSum x - Real.log x - c| ≤ KL / (Real.log x) ^ 5)
    (hP : ∀ᶠ x : ℝ in atTop,
      |primeLogSummatory x - (x * Real.log x - x)| ≤ KP * x / (Real.log x) ^ 5) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ᶠ x : ℝ in atTop,
      |centeredSelbergSummatory c x| ≤ KA * x / (Real.log x) ^ 5 := by
  refine ⟨64 * KL + 256 * chebyshevLinearConstant * Kψ + 128 * Kψ +
    4096 * Kψ ^ 2 + KP + 2 * |c|, ?_, ?_⟩
  · have hC := chebyshevLinearConstant_nonneg
    positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp hψ
  have hsqrtT := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop T)
  have hsqrtL := Real.tendsto_sqrt_atTop.eventually hL
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hsqrtT, hsqrtL, hlog, hP, eventually_ge_atTop (1 : ℝ),
    eventually_log_pow_le_self 5] with x hxT hxL hxlog hxP hx hxpow
  exact abs_centeredSelbergSummatory_le_of_prime_errors c x Kψ KL KP hx hxlog hxpow
    hKψ hKL hKP (fun t ht => hT t (hxT.trans ht)) hxL hxP

end TwinPrime.Analytic
