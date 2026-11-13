import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Log.NegMulLog
import Tengoku.Seed.NumberTheory.Chebyshev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Explicit finite prime-sum estimates This file supplies the elementary prime-sum input for the finite Rankin bounds. -/

namespace RankAmplification

open Finset MeasureTheory
open scoped Nat.Prime

noncomputable section

/-- The reciprocal prime sum with a finite natural cutoff.-/
def primeReciprocalSum (R : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE R, (p : ℝ)⁻¹

/-- The logarithmically weighted reciprocal prime sum with a finite natural cutoff.-/
def primeLogReciprocalSum (R : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE R, Real.log p / p

/-- The finite prime sum with Rankin exponent `-1 + δ`.-/
def primeRankinSum (R : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE R, (p : ℝ) ^ (-1 + δ)

@[simp]
theorem primeReciprocalSum_zero : primeReciprocalSum 0 = 0 := by
  simp [primeReciprocalSum]

@[simp]
theorem primeLogReciprocalSum_zero : primeLogReciprocalSum 0 = 0 := by
  simp [primeLogReciprocalSum]

@[simp]
theorem primeRankinSum_zero (δ : ℝ) : primeRankinSum 0 δ = 0 := by
  simp [primeRankinSum]

theorem primeReciprocalSum_nonneg (R : ℕ) : 0 ≤ primeReciprocalSum R := by
  exact sum_nonneg fun p hp ↦ inv_nonneg.mpr (Nat.cast_nonneg p)

theorem primeLogReciprocalSum_nonneg (R : ℕ) : 0 ≤ primeLogReciprocalSum R := by
  refine sum_nonneg fun p hp ↦ div_nonneg ?_ (Nat.cast_nonneg p)
  exact Real.log_nonneg (mod_cast (Nat.one_le_iff_ne_zero.mpr
    (Nat.Prime.ne_zero (Nat.prime_of_mem_primesLE hp))))

theorem primeRankinSum_nonneg (R : ℕ) (δ : ℝ) : 0 ≤ primeRankinSum R δ := by
  exact sum_nonneg fun p _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- Derivative of the reciprocal-log kernel on its positive range.-/
theorem deriv_reciprocalLogKernel {x : ℝ} (hx : 1 < x) :
    deriv (fun t : ℝ ↦ (t * Real.log t)⁻¹) x =
      -((Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) := by
  have hx0 : x ≠ 0 := by linarith
  have hlog : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0) |>.inv
    (mul_ne_zero hx0 hlog)).deriv
  simp only [Pi.inv_def, Pi.mul_def, id_eq] at hd
  rw [show deriv (fun t : ℝ ↦ (t * Real.log t)⁻¹) x =
    -((1 * Real.log x + x * x⁻¹) / (x * Real.log x) ^ 2) by
      simpa only [neg_div] using hd]
  field_simp

/-- Local integrability of the theta kernel needed for logarithmic reciprocal sums.-/
theorem integrableOn_theta_div_sq (x : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Chebyshev.theta t / t ^ 2) (Set.Icc 2 x) volume := by
  conv => arg 1; ext t; rw [Chebyshev.theta, div_eq_mul_one_div, mul_comm, sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  fun_prop (disch := assumption)

/-- Local integrability of the theta kernel needed for reciprocal prime sums.-/
theorem integrableOn_theta_mul_reciprocalLogDerivative (x : ℝ) :
    IntegrableOn (fun t : ℝ ↦
      Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2))
      (Set.Icc 2 x) volume := by
  let c : ℕ → ℝ := Set.indicator {n : ℕ | n.Prime} (fun n ↦ Real.log n)
  have hg : IntegrableOn (fun t : ℝ ↦
      ((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) *
        ∑ k ∈ Icc 0 ⌊t⌋₊, c k) (Set.Icc 2 x) volume := by
    refine integrableOn_mul_sum_Icc c (by norm_num) <|
      ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have hden : t ^ 2 * Real.log t ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hlog)
    fun_prop (disch := assumption)
  convert hg using 1
  funext t
  simp [c, Set.indicator_apply, sum_filter, Chebyshev.theta_eq_sum_Icc]
  ring

/-- Exact Abel-summation identity for the logarithmically weighted reciprocal prime sum.-/
theorem primeLogReciprocalSum_eq_theta_integral {R : ℕ} (hR : 2 ≤ R) :
    primeLogReciprocalSum R =
      Chebyshev.theta R / R + ∫ t in (2 : ℝ)..R, Chebyshev.theta t / t ^ 2 := by
  let a : ℕ → ℝ := Set.indicator {n : ℕ | n.Prime} (fun n ↦ Real.log n)
  rw [primeLogReciprocalSum, Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  trans ∑ n ∈ Icc 0 R, (n : ℝ)⁻¹ * a n
  · apply sum_congr rfl
    intro n hn
    split_ifs with hp
    · simp [a, hp, div_eq_mul_inv, mul_comm]
    · simp [a, hp]
  nth_rewrite 1 [← Nat.floor_natCast (R := ℝ) R]
  rw [sum_mul_eq_sub_integral_mul₁ a (f := fun t : ℝ ↦ t⁻¹)
    (by simp [a, Nat.not_prime_zero]) (by simp [a, Nat.not_prime_one]) R,
    ← intervalIntegral.integral_of_le (mod_cast hR)]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ t in (2 : ℝ)..R, deriv (fun u : ℝ ↦ u⁻¹) t * f t =
          ∫ t in (2 : ℝ)..R, -(f t / t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        change deriv (fun u : ℝ ↦ u⁻¹) t * f t = -(f t / t ^ 2)
        rw [deriv_inv]
        ring
    rw [int_deriv]
    simp [a, Set.indicator_apply, sum_filter, Chebyshev.theta_eq_sum_Icc]
    ring
  · intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1])).differentiableAt
  · rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg.continuousWithinAt

/-- Exact Abel-summation identity for the reciprocal prime sum.-/
theorem primeReciprocalSum_eq_theta_integral {R : ℕ} (hR : 2 ≤ R) :
    primeReciprocalSum R = Chebyshev.theta R / (R * Real.log R) +
      ∫ t in (2 : ℝ)..R,
        Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
  let a : ℕ → ℝ := Set.indicator {n : ℕ | n.Prime} (fun n ↦ Real.log n)
  rw [primeReciprocalSum, Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  trans ∑ n ∈ Icc 0 R, ((n : ℝ) * Real.log n)⁻¹ * a n
  · apply sum_congr rfl
    intro n hn
    split_ifs with hp
    · have hn0 : (n : ℝ) ≠ 0 := mod_cast hp.ne_zero
      have hlog : Real.log (n : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (mod_cast hp.pos) (mod_cast hp.ne_one)
      rw [show a n = Real.log n by simp [a, hp]]
      field_simp
    · simp [a, hp]
  nth_rewrite 1 [← Nat.floor_natCast (R := ℝ) R]
  rw [sum_mul_eq_sub_integral_mul₁ a
    (f := fun t : ℝ ↦ (t * Real.log t)⁻¹)
    (by simp [a, Nat.not_prime_zero]) (by simp [a, Nat.not_prime_one]) R,
    ← intervalIntegral.integral_of_le (mod_cast hR)]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ t in (2 : ℝ)..R, deriv (fun u : ℝ ↦ (u * Real.log u)⁻¹) t * f t =
          ∫ t in (2 : ℝ)..R,
            -(f t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (mod_cast hR)] at ht
        change deriv (fun u : ℝ ↦ (u * Real.log u)⁻¹) t * f t =
          -(f t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2))
        rw [deriv_reciprocalLogKernel (by linarith [ht.1])]
        ring
    rw [int_deriv]
    simp [a, Set.indicator_apply, sum_filter, Chebyshev.theta_eq_sum_Icc]
    field_simp
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0) |>.inv
      (mul_ne_zero ht0 hlog)).differentiableAt
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousWithinAt.congr
      (f := fun u : ℝ ↦ -((Real.log u + 1) / (u ^ 2 * Real.log u ^ 2)))
      (g := deriv fun u : ℝ ↦ (u * Real.log u)⁻¹) ?_ (fun y hy ↦ ?_) ?_
    · have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlog : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
      have hden : t ^ 2 * Real.log t ^ 2 ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hlog)
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
    · exact deriv_reciprocalLogKernel (by linarith [hy.1])
    · exact deriv_reciprocalLogKernel (by linarith [ht.1])

/-- Chebyshev's bound after partial summation: an explicit estimate for `∑ log p / p`.-/
theorem primeLogReciprocalSum_le {R : ℕ} (hR : 2 ≤ R) :
    primeLogReciprocalSum R ≤ Real.log 4 * (1 + Real.log R) := by
  rw [primeLogReciprocalSum_eq_theta_integral hR]
  have hRpos : 0 < (R : ℝ) := by positivity
  have hRcast : (2 : ℝ) ≤ R := mod_cast hR
  have hboundary : Chebyshev.theta R / R ≤ Real.log 4 := by
    apply (div_le_iff₀ hRpos).2
    simpa [mul_comm] using Chebyshev.theta_le_log4_mul_x hRpos.le
  have hleft : IntervalIntegrable (fun t : ℝ ↦ Chebyshev.theta t / t ^ 2)
      volume 2 R := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hRcast]
    exact integrableOn_theta_div_sq R
  have hright : IntervalIntegrable (fun t : ℝ ↦ Real.log 4 * t⁻¹) volume 2 R := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht0 : t ≠ 0 := by
      rw [Set.uIcc_of_le hRcast] at ht
      linarith [ht.1]
    fun_prop
  have hintegral :
      (∫ t in (2 : ℝ)..R, Chebyshev.theta t / t ^ 2) ≤
        ∫ t in (2 : ℝ)..R, Real.log 4 * t⁻¹ := by
    apply intervalIntegral.integral_mono_on hRcast hleft hright
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have ht2pos : 0 < t ^ 2 := sq_pos_of_pos htpos
    apply (div_le_iff₀ ht2pos).2
    calc
      Chebyshev.theta t ≤ Real.log 4 * t :=
        Chebyshev.theta_le_log4_mul_x htpos.le
      _ = (Real.log 4 * t⁻¹) * t ^ 2 := by field_simp
  calc
    Chebyshev.theta R / R + ∫ t in (2 : ℝ)..R, Chebyshev.theta t / t ^ 2
        ≤ Real.log 4 + ∫ t in (2 : ℝ)..R, Real.log 4 * t⁻¹ :=
      add_le_add hboundary hintegral
    _ = Real.log 4 + Real.log 4 * Real.log ((R : ℝ) / 2) := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_of_pos (by norm_num) hRpos]
    _ ≤ Real.log 4 + Real.log 4 * Real.log R := by
      have hratio : 0 < (R : ℝ) / 2 := div_pos hRpos (by norm_num)
      have hratio_le : (R : ℝ) / 2 ≤ R := by nlinarith [hRpos]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.log_le_log hratio hratio_le)
        (Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)))
    _ = Real.log 4 * (1 + Real.log R) := by ring

/-- Explicit Mertens-type upper bound obtained solely from Chebyshev's theta estimate.-/
theorem primeReciprocalSum_le {R : ℕ} (hR : 2 ≤ R) :
    primeReciprocalSum R ≤ Real.log 4 *
      (Real.log (Real.log R) - Real.log (Real.log 2) + (Real.log 2)⁻¹) := by
  rw [primeReciprocalSum_eq_theta_integral hR]
  have hRpos : 0 < (R : ℝ) := by positivity
  have hRone : (1 : ℝ) < R := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR
  have hRlog : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hRcast : (2 : ℝ) ≤ R := mod_cast hR
  have hboundary : Chebyshev.theta R / (R * Real.log R) ≤
      Real.log 4 / Real.log R := by
    have hden : 0 < (R : ℝ) * Real.log R := mul_pos hRpos hRlog
    apply (div_le_iff₀ hden).2
    calc
      Chebyshev.theta R ≤ Real.log 4 * R :=
        Chebyshev.theta_le_log4_mul_x hRpos.le
      _ = (Real.log 4 / Real.log R) * (R * Real.log R) := by field_simp
  have hleft : IntervalIntegrable (fun t : ℝ ↦
      Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2))
      volume 2 R := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hRcast]
    exact integrableOn_theta_mul_reciprocalLogDerivative R
  let g : ℝ → ℝ := fun t ↦ Real.log 4 *
    (t⁻¹ / Real.log t + t⁻¹ / Real.log t ^ 2)
  have hright : IntervalIntegrable g volume 2 R := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hRcast] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    dsimp [g]
    fun_prop (disch := assumption)
  have hintegral :
      (∫ t in (2 : ℝ)..R,
        Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) ≤
        ∫ t in (2 : ℝ)..R, g t := by
    apply intervalIntegral.integral_mono_on hRcast hleft hright
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hcoef : 0 ≤ (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by positivity
    calc
      Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) =
          Chebyshev.theta t * ((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) := by ring
      _ ≤ (Real.log 4 * t) * ((Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) :=
        mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x htpos.le) hcoef
      _ = g t := by
        dsimp [g]
        field_simp
  have hfirst : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / Real.log t) volume 2 R := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hRcast] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    fun_prop (disch := assumption)
  have hsecond : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / Real.log t ^ 2)
      volume 2 R := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hRcast] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    fun_prop (disch := assumption)
  calc
    Chebyshev.theta R / (R * Real.log R) +
        ∫ t in (2 : ℝ)..R,
          Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)
        ≤ Real.log 4 / Real.log R + ∫ t in (2 : ℝ)..R, g t :=
      add_le_add hboundary hintegral
    _ = Real.log 4 / Real.log R + Real.log 4 *
        ((Real.log (Real.log R) - Real.log (Real.log 2)) +
          ((Real.log 2)⁻¹ - (Real.log R)⁻¹)) := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hfirst hsecond,
        integral_inv_div_log (by norm_num) hRone,
        integral_inv_div_log_sq (by norm_num) hRone]
    _ = Real.log 4 *
        (Real.log (Real.log R) - Real.log (Real.log 2) + (Real.log 2)⁻¹) := by
      field_simp
      ring

/-- A convenient linear upper bound for the exponential on the unit interval.-/
theorem exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have habs : |x| ≤ 1 := by simpa [abs_of_nonneg hx0] using hx1
  have h := Real.abs_exp_sub_one_le habs
  have h' : Real.exp x - 1 ≤ 2 * x :=
    (le_abs_self (Real.exp x - 1)).trans (by simpa [abs_of_nonneg hx0] using h)
  linarith

/-- Pointwise small-exponent Rankin estimate for a prime below the cutoff.-/
theorem prime_rpow_neg_one_add_le {p R : ℕ} {δ : ℝ} (hp : p.Prime) (hpR : p ≤ R)
    (hδ0 : 0 ≤ δ) (hδR : δ * Real.log R ≤ 1) :
    (p : ℝ) ^ (-1 + δ) ≤
      (p : ℝ)⁻¹ + 2 * δ * (Real.log p / p) := by
  have hppos : 0 < (p : ℝ) := mod_cast hp.pos
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (mod_cast hp.one_le)
  have hlog_le : Real.log (p : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log hppos (mod_cast hpR)
  have hx0 : 0 ≤ δ * Real.log (p : ℝ) := mul_nonneg hδ0 hlogp
  have hx1 : δ * Real.log (p : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlog_le hδ0).trans hδR
  have hexp := exp_le_one_add_two_mul hx0 hx1
  rw [Real.rpow_def_of_pos hppos]
  calc
    Real.exp (Real.log p * (-1 + δ)) =
        (p : ℝ)⁻¹ * Real.exp (δ * Real.log p) := by
      rw [show Real.log (p : ℝ) * (-1 + δ) =
        -Real.log p + δ * Real.log p by ring, Real.exp_add, Real.exp_neg,
        Real.exp_log hppos]
    _ ≤ (p : ℝ)⁻¹ * (1 + 2 * (δ * Real.log p)) :=
      mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hppos.le)
    _ = (p : ℝ)⁻¹ + 2 * δ * (Real.log p / p) := by
      field_simp

/-- Finite Rankin prime sum reduced to the two partial-summation inputs.-/
theorem primeRankinSum_le_aux {R : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδR : δ * Real.log R ≤ 1) :
    primeRankinSum R δ ≤
      primeReciprocalSum R + 2 * δ * primeLogReciprocalSum R := by
  calc
    primeRankinSum R δ = ∑ p ∈ Nat.primesLE R, (p : ℝ) ^ (-1 + δ) := rfl
    _ ≤ ∑ p ∈ Nat.primesLE R,
        ((p : ℝ)⁻¹ + 2 * δ * (Real.log p / p)) := by
      apply sum_le_sum
      intro p hp
      exact prime_rpow_neg_one_add_le (Nat.prime_of_mem_primesLE hp)
        (Nat.le_of_mem_primesLE hp) hδ0 hδR
    _ = primeReciprocalSum R + 2 * δ * primeLogReciprocalSum R := by
      rw [sum_add_distrib, primeReciprocalSum, primeLogReciprocalSum,
        ← Finset.mul_sum]

/-- Explicit small-exponent prime-sum bound of the form `O(log log R + δ log R)`, with every constant displayed.-/
theorem primeRankinSum_le {R : ℕ} {δ : ℝ} (hR : 2 ≤ R) (hδ0 : 0 ≤ δ)
    (hδR : δ * Real.log R ≤ 1) :
    primeRankinSum R δ ≤
      Real.log 4 *
        (Real.log (Real.log R) - Real.log (Real.log 2) + (Real.log 2)⁻¹) +
      2 * δ * (Real.log 4 * (1 + Real.log R)) := by
  calc
    primeRankinSum R δ ≤
        primeReciprocalSum R + 2 * δ * primeLogReciprocalSum R :=
      primeRankinSum_le_aux hδ0 hδR
    _ ≤ Real.log 4 *
          (Real.log (Real.log R) - Real.log (Real.log 2) + (Real.log 2)⁻¹) +
        2 * δ * (Real.log 4 * (1 + Real.log R)) := by
      exact add_le_add (primeReciprocalSum_le hR)
        (mul_le_mul_of_nonneg_left (primeLogReciprocalSum_le hR) (by positivity))

/-- The same estimate with the conventional harmless `3R` inside the double logarithm.-/
theorem primeRankinSum_le_loglog_three_mul {R : ℕ} {δ : ℝ} (hR : 2 ≤ R)
    (hδ0 : 0 ≤ δ) (hδR : δ * Real.log R ≤ 1) :
    primeRankinSum R δ ≤
      Real.log 4 *
        (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2) +
          (Real.log 2)⁻¹) +
      2 * δ * (Real.log 4 * (1 + Real.log R)) := by
  have hRpos : 0 < (R : ℝ) := by positivity
  have hRone : (1 : ℝ) < R := by exact_mod_cast lt_of_lt_of_le (by norm_num) hR
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hRle : (R : ℝ) ≤ 3 * R := by nlinarith [hRpos]
  have hlogle : Real.log (R : ℝ) ≤ Real.log (3 * R) :=
    Real.log_le_log hRpos hRle
  have hloglogle : Real.log (Real.log (R : ℝ)) ≤ Real.log (Real.log (3 * R)) :=
    Real.log_le_log hlogRpos hlogle
  calc
    primeRankinSum R δ ≤
        Real.log 4 *
          (Real.log (Real.log R) - Real.log (Real.log 2) + (Real.log 2)⁻¹) +
        2 * δ * (Real.log 4 * (1 + Real.log R)) :=
      primeRankinSum_le hR hδ0 hδR
    _ ≤ Real.log 4 *
          (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2) +
            (Real.log 2)⁻¹) +
        2 * δ * (Real.log 4 * (1 + Real.log R)) := by
      apply add_le_add
      apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
      linarith
      exact le_rfl

end

end RankAmplification
