import Tengoku.Twinprime.TwinPrime.Analytic.SelbergSummatory
import Tengoku.Twinprime.TwinPrime.Analytic.SelbergCoefficientBounds
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The remainder in the Möbius--Selberg hyperbola split

The short coefficient sum is retained, while the other strip and the overlap
are bounded using the signed centered-coefficient error and only the trivial
bound for the Möbius summatory function.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/--
@isnad1 id=le.1h1v.s4.5814f036688d from=translated src=- shape=e481bd26 vocab=a9fa9fc0
-/
theorem abs_mertensReal_le (x : ℝ) (hx : 0 ≤ x) : |mertensReal x| ≤ x := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, |(μ n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      exact_mod_cast (abs_moebius_le_one (n := n))
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

/--
@isnad1 id=le.5h5v.s7.f9cdbdb2f8e2 from=translated src=- shape=cf66fc94 vocab=1b83682f
-/
theorem abs_moebiusSelberg_tail_le (c x y z K : ℝ)
    (hy : 2 ≤ y) (hz : 1 ≤ z) (hyz : y * z = x) (hK : 0 ≤ K)
    (hA : ∀ t : ℝ, y ≤ t → |centeredSelbergSummatory c t| ≤ K * t / (Real.log t) ^ 5) :
    |∑ d ∈ Ioc 0 ⌊z⌋₊, (μ d : ℝ) * centeredSelbergSummatory c (x / d)| ≤
      K * x / (Real.log y) ^ 5 * (harmonic ⌊z⌋₊ : ℝ) := by
  have hx : 0 ≤ x := by rw [← hyz]; positivity
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ d ∈ Ioc 0 ⌊z⌋₊, |(μ d : ℝ) * centeredSelbergSummatory c (x / d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 ⌊z⌋₊, K * x / (Real.log y) ^ 5 * (1 / d) := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
      have hdz : (d : ℝ) ≤ z :=
        (by exact_mod_cast (mem_Ioc.mp hd).2 : (d : ℝ) ≤ ⌊z⌋₊).trans
          (Nat.floor_le (by linarith))
      have hyt : y ≤ x / d := (le_div_iff₀ hd0).mpr (by nlinarith)
      have hlt : 0 < Real.log (x / d) := hly.trans_le
        (Real.log_le_log (by linarith) hyt)
      have hden : (Real.log y) ^ 5 ≤ (Real.log (x / d)) ^ 5 :=
        pow_le_pow_left₀ hly.le (Real.log_le_log (by linarith) hyt) 5
      have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
      calc
        _ = |(μ d : ℝ)| * |centeredSelbergSummatory c (x / d)| := abs_mul _ _
        _ ≤ 1 * (K * (x / d) / (Real.log (x / d)) ^ 5) :=
          mul_le_mul hmu (hA _ hyt) (abs_nonneg _) (by norm_num)
        _ ≤ K * (x / d) / (Real.log y) ^ 5 := by
          rw [one_mul]
          exact div_le_div_of_nonneg_left (by positivity) (pow_pos hly _) hden
        _ = _ := by ring
    _ = _ := by rw [← mul_sum, sum_one_div_Ioc_eq_harmonic]

/-- The exact overlap costs no more than one additional harmonic unit.
@isnad1 id=le.5h5v.s7.77bdfedae035 from=translated src=- shape=0fc0575f vocab=ed51f502
-/
theorem abs_moebiusSelberg_boundary_le (c x y z K : ℝ)
    (hy : 2 ≤ y) (hz : 1 ≤ z) (hyz : y * z = x) (hK : 0 ≤ K)
    (hAy : |centeredSelbergSummatory c y| ≤ K * y / (Real.log y) ^ 5) :
    |centeredSelbergSummatory c y * mertensReal z| ≤ K * x / (Real.log y) ^ 5 := by
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  rw [abs_mul]
  calc
    _ ≤ (K * y / (Real.log y) ^ 5) * z :=
      mul_le_mul hAy (abs_mertensReal_le z (by linarith)) (abs_nonneg _) (by positivity)
    _ = _ := by rw [← hyz]; ring

/--
@isnad1 id=le.5h5v.s8.4a9fdf0aa04d from=translated src=- shape=3e5d9dca vocab=357ee165
-/
theorem abs_moebiusLogSqSummatory_le_hyperbola_head (c x y z K : ℝ)
    (hy : 2 ≤ y) (hz : 1 ≤ z) (hyz : y * z = x) (hK : 0 ≤ K)
    (hA : ∀ t : ℝ, y ≤ t → |centeredSelbergSummatory c t| ≤ K * t / (Real.log t) ^ 5) :
    |moebiusLogSqSummatory x| ≤
      (∑ k ∈ Ioc 0 ⌊y⌋₊, |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) +
      K * x / (Real.log y) ^ 5 * ((harmonic ⌊z⌋₊ : ℝ) + 1) + 2 * |c| := by
  have hx : 1 ≤ x := by nlinarith
  have hid := moebiusSelberg_hyperbola c x y z hx (by linarith) hz hyz
  have heq : moebiusLogSqSummatory x =
      ((∑ k ∈ Ioc 0 ⌊y⌋₊, centeredSelbergCoefficient c k * mertensReal (x / k)) +
        (∑ d ∈ Ioc 0 ⌊z⌋₊, (μ d : ℝ) * centeredSelbergSummatory c (x / d)) -
        centeredSelbergSummatory c y * mertensReal z) + 2 * c := by linarith
  have hhead : |∑ k ∈ Ioc 0 ⌊y⌋₊, centeredSelbergCoefficient c k * mertensReal (x / k)| ≤
      ∑ k ∈ Ioc 0 ⌊y⌋₊, |centeredSelbergCoefficient c k| * |mertensReal (x / k)| := by
    simpa only [abs_mul] using abs_sum_le_sum_abs
      (fun k => centeredSelbergCoefficient c k * mertensReal (x / k)) (Ioc 0 ⌊y⌋₊)
  calc
    _ ≤ (|∑ k ∈ Ioc 0 ⌊y⌋₊, centeredSelbergCoefficient c k * mertensReal (x / k)| +
          |∑ d ∈ Ioc 0 ⌊z⌋₊, (μ d : ℝ) * centeredSelbergSummatory c (x / d)|) +
        |centeredSelbergSummatory c y * mertensReal z| + 2 * |c| := by
      rw [heq]
      have hc : |2 * c| = 2 * |c| := by rw [abs_mul]; norm_num
      rw [← hc]
      exact (abs_add_le _ _).trans
        (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      have ht := abs_moebiusSelberg_tail_le c x y z K hy hz hyz hK hA
      have hb := abs_moebiusSelberg_boundary_le c x y z K hy hz hyz hK (hA y le_rfl)
      nlinarith [hhead, ht, hb]

/-- With a fixed power cutoff, the discarded strip and overlap have four
logarithmic powers of saving. No cancellation bound for Mertens is used.
@isnad1 id=ex.4h3v.s7.2b4a87c223ff from=translated src=- shape=a6dc957a vocab=3bd9612c
-/
theorem eventually_moebiusLogSqSummatory_le_power_head
    (c K δ : ℝ) (hK : 0 ≤ K) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hA : ∀ᶠ t : ℝ in atTop,
      |centeredSelbergSummatory c t| ≤ K * t / (Real.log t) ^ 5) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ x : ℝ in atTop,
      |moebiusLogSqSummatory x| ≤
        (∑ k ∈ Ioc 0 ⌊x ^ δ⌋₊,
          |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) +
        E * x / (Real.log x) ^ 4 := by
  refine ⟨3 * K / δ ^ 5 + 2 * |c|, by positivity, ?_⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hA
  have hcut := (tendsto_rpow_atTop hδ0).eventually (eventually_ge_atTop (max T 2))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hcut, hlog, eventually_ge_atTop (2 : ℝ), eventually_log_pow_le_self 4]
    with x hcut hlog hx hpow
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  have hy : 2 ≤ x ^ δ := (le_max_right T 2).trans hcut
  have hz : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow (by linarith) (by linarith)
  have hyz : x ^ δ * x ^ (1 - δ) = x := by
    rw [← Real.rpow_add hx0]
    simp
  have hAz : ∀ t : ℝ, x ^ δ ≤ t →
      |centeredSelbergSummatory c t| ≤ K * t / (Real.log t) ^ 5 :=
    fun t ht => hT t (((le_max_left T 2).trans hcut).trans ht)
  have hf := abs_moebiusLogSqSummatory_le_hyperbola_head c x (x ^ δ) (x ^ (1 - δ))
    K hy hz hyz hK hAz
  have hzle : x ^ (1 - δ) ≤ x := Real.rpow_le_self_of_one_le (by linarith) (by linarith)
  have hn1 : 1 ≤ ⌊x ^ (1 - δ)⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hn0 : (0 : ℝ) < ⌊x ^ (1 - δ)⌋₊ := by exact_mod_cast hn1
  have hnle : (⌊x ^ (1 - δ)⌋₊ : ℝ) ≤ x :=
    (Nat.floor_le (by linarith : 0 ≤ x ^ (1 - δ))).trans hzle
  have hH : (harmonic ⌊x ^ (1 - δ)⌋₊ : ℝ) + 1 ≤ 3 * Real.log x := by
    have h := harmonic_le_one_add_log ⌊x ^ (1 - δ)⌋₊
    have hl := Real.log_le_log hn0 hnle
    linarith
  have hscale : K * x / (Real.log (x ^ δ)) ^ 5 *
      ((harmonic ⌊x ^ (1 - δ)⌋₊ : ℝ) + 1) ≤
      (3 * K / δ ^ 5) * x / (Real.log x) ^ 4 := by
    rw [Real.log_rpow hx0, mul_pow]
    calc
      _ ≤ K * x / (δ ^ 5 * (Real.log x) ^ 5) * (3 * Real.log x) := by gcongr
      _ = _ := by field_simp
  have hc : 2 * |c| ≤ (2 * |c|) * x / (Real.log x) ^ 4 := by
    apply (le_div_iff₀ (pow_pos hlog0 _)).mpr
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  apply hf.trans
  rw [add_mul, add_div]
  linarith only [hscale, hc]

end TwinPrime.Analytic
