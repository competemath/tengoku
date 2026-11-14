import Tengoku.Twinprime.TwinPrime.Analytic.BilinearSign
import Tengoku.Twinprime.TwinPrime.Analytic.DivisorGrowth
import Tengoku.Twinprime.TwinPrime.Analytic.Decomposition
import Tengoku.Twinprime.TwinPrime.Analytic.EvenAsymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing proper prime powers from the bilinear term

The exceptional part has a uniform sublinear bound for all positive pairs of
cutoffs. The remaining signed sum is supported on integers which are not prime
powers and whose shifted partners are prime. No bound for that main signed
sum is asserted here.
-/

noncomputable section

open Finset ArithmeticFunction Filter

namespace TwinPrime.Analytic

def nonprimeMangoldt (n : ℕ) : ℝ := if ¬n.Prime then vonMangoldt n else 0

theorem nonprimeMangoldt_nonneg (n : ℕ) : 0 ≤ nonprimeMangoldt n := by
  unfold nonprimeMangoldt
  split_ifs <;> positivity

theorem sum_nonprimeMangoldt_eq (Y : ℕ) :
    (∑ n ∈ Ioc 0 Y, nonprimeMangoldt n) = Chebyshev.psi Y - Chebyshev.theta Y := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp [nonprimeMangoldt, sum_filter]

theorem nonprimeMangoldt_dyadic_le (X : ℕ) :
    (∑ n ∈ Ioc X (2 * X), nonprimeMangoldt n) ≤ evenProgressionBound X := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 (2 * X + 2), nonprimeMangoldt n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [mem_Ioc] at hn ⊢
        omega
      · exact fun n _ _ => nonprimeMangoldt_nonneg n
    _ = Chebyshev.psi (2 * X + 2) - Chebyshev.theta (2 * X + 2) := by
      simpa using sum_nonprimeMangoldt_eq (2 * X + 2)
    _ ≤ _ := by
      simpa [evenProgressionBound] using
        (Chebyshev.psi_sub_theta_le (x := ((2 * X + 2 : ℕ) : ℝ))
          (by exact_mod_cast (show 1 ≤ 2 * X + 2 by omega)))

theorem nonprimeMangoldt_shifted_dyadic_le (X : ℕ) :
    (∑ n ∈ Ioc X (2 * X), nonprimeMangoldt (n + 2)) ≤ evenProgressionBound X := by
  calc
    _ = ∑ n ∈ (Ioc X (2 * X)).image (fun n => n + 2), nonprimeMangoldt n := by
      rw [sum_image (fun a _ b _ h => Nat.add_right_cancel h)]
    _ ≤ ∑ n ∈ Ioc 0 (2 * X + 2), nonprimeMangoldt n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
        simp only [mem_Ioc] at hm ⊢
        omega
      · exact fun n _ _ => nonprimeMangoldt_nonneg n
    _ = Chebyshev.psi (2 * X + 2) - Chebyshev.theta (2 * X + 2) := by
      simpa using sum_nonprimeMangoldt_eq (2 * X + 2)
    _ ≤ _ := by
      simpa [evenProgressionBound] using
        (Chebyshev.psi_sub_theta_le (x := ((2 * X + 2 : ℕ) : ℝ))
          (by exact_mod_cast (show 1 ≤ 2 * X + 2 by omega)))

theorem log_two_le_vonMangoldt {n : ℕ} (hn : IsPrimePow n) :
    Real.log 2 ≤ vonMangoldt n := by
  rw [vonMangoldt_apply, ite_eq_left hn]
  exact Real.log_le_log (by norm_num)
    (by exact_mod_cast (Nat.minFac_prime hn.ne_one).two_le)

theorem abs_vaughanBilinear_of_prime_pow_le_log (U V n : ℕ) (hU : 1 ≤ U)
    (hn : IsPrimePow n) : |(moebiusHigh U * vaughanBeta V) n| ≤ Real.log n := by
  obtain ⟨p, a, hp, _, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  exact abs_vaughanBilinear_prime_pow_le_log U V p a hU hp

theorem abs_vaughanBilinear_le_cuberoot (U V n : ℕ) :
    |(moebiusHigh U * vaughanBeta V) n| ≤ 16 * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n := by
  by_cases hn : n = 0
  · subst n; simp
  apply (abs_vaughanBilinear_le_card_divisors_mul_log U V n).trans
  exact mul_le_mul_of_nonneg_right (card_divisors_le_sixteen_cuberoot n)
    (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))

/-- The signed main contribution after removing prime powers at either input.-/
def bilinearPrimeSupport (U V X : ℕ) : ℝ :=
  ∑ n ∈ Ioc X (2 * X) with ¬IsPrimePow n ∧ (n + 2).Prime,
    vonMangoldt (n + 2) * (moebiusHigh U * vaughanBeta V) n

def bilinearExceptionalBound (X : ℕ) : ℝ :=
  ((Real.log (2 * X + 2)) ^ 2 / Real.log 2 +
    16 * (2 * X + 2 : ℝ) ^ (1 / 3 : ℝ) * Real.log (2 * X + 2)) * evenProgressionBound X

theorem bilinearExceptionalBound_nonneg (X : ℕ) : 0 ≤ bilinearExceptionalBound X := by
  have hL : 0 ≤ Real.log (2 * X + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  unfold bilinearExceptionalBound
  exact mul_nonneg (add_nonneg (div_nonneg (sq_nonneg _) (Real.log_nonneg (by norm_num)))
    (mul_nonneg (by positivity) hL)) (evenProgressionBound_nonneg X)

/-- Explicit finite error for removing the entire prime-power exceptional range.-/
theorem abs_bilinearTerm_sub_primeSupport_le (U V X : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    |bilinearTerm U V X - bilinearPrimeSupport U V X| ≤ bilinearExceptionalBound X := by
  let Y : ℕ := 2 * X + 2
  let L : ℝ := Real.log Y
  let D : ℝ := 16 * (Y : ℝ) ^ (1 / 3 : ℝ) * L
  have hY : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by dsimp [Y]; omega)
  have hL : 0 ≤ L := Real.log_nonneg hY
  have hD : 0 ≤ D := mul_nonneg (by positivity) hL
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ L ^ 2 / Real.log 2 := div_nonneg (sq_nonneg _) hlog2.le
  have hp : |bilinearTerm U V X - bilinearPrimeSupport U V X| ≤
      (L ^ 2 / Real.log 2) * (∑ n ∈ Ioc X (2 * X), nonprimeMangoldt n) +
        D * ∑ n ∈ Ioc X (2 * X), nonprimeMangoldt (n + 2) := by
    unfold bilinearTerm bilinearPrimeSupport
    rw [sum_filter, ← sum_sub_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n hn
    have hnpos : 0 < n := by have := mem_Ioc.mp hn; omega
    have hnY : (n : ℝ) ≤ Y := by exact_mod_cast (show n ≤ Y by dsimp [Y]; have := mem_Ioc.mp hn; omega)
    have hnL : Real.log n ≤ L := Real.log_le_log (by exact_mod_cast hnpos) hnY
    have hqL : vonMangoldt (n + 2) ≤ L := vonMangoldt_le_log.trans
      (Real.log_le_log (by positivity)
        (by exact_mod_cast (show n + 2 ≤ Y by dsimp [Y]; have := mem_Ioc.mp hn; omega)))
    have hnΛ := vonMangoldt_nonneg (n := n)
    have hqΛ := vonMangoldt_nonneg (n := n + 2)
    have hbD : |(moebiusHigh U * vaughanBeta V) n| ≤ D := by
      apply (abs_vaughanBilinear_le_cuberoot U V n).trans
      apply mul_le_mul _ hnL (Real.log_nonneg (by exact_mod_cast hnpos)) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hnY (by norm_num)) (by norm_num)
    by_cases hpow : IsPrimePow n
    · simp only [hpow, not_true_eq_false, false_and, ite_false, sub_zero]
      by_cases hprime : n.Prime
      · rw [vaughanBilinear_eq_zero_of_prime U V n hU hV hprime, mul_zero, abs_zero]
        exact add_nonneg (mul_nonneg hA (nonprimeMangoldt_nonneg n))
          (mul_nonneg hD (nonprimeMangoldt_nonneg (n + 2)))
      · have hb := (abs_vaughanBilinear_of_prime_pow_le_log U V n hU hpow).trans hnL
        have hnp := log_two_le_vonMangoldt hpow
        have hfirst : L ^ 2 ≤ (L ^ 2 / Real.log 2) * nonprimeMangoldt n := by
          rw [nonprimeMangoldt, ite_eq_left hprime]
          have hh := mul_le_mul_of_nonneg_left hnp hA
          have heq : (L ^ 2 / Real.log 2) * Real.log 2 = L ^ 2 := by field_simp
          rwa [heq] at hh
        rw [abs_mul, abs_of_nonneg hqΛ]
        have hprod := mul_le_mul hqL hb (abs_nonneg _) hL
        exact (hprod.trans (by nlinarith [hfirst])).trans
          (le_add_of_nonneg_right (mul_nonneg hD (nonprimeMangoldt_nonneg (n + 2))))
    · by_cases hprime : (n + 2).Prime
      · simp only [hpow, not_false_eq_true, hprime, and_self, ite_true, sub_self, abs_zero]
        exact add_nonneg (mul_nonneg hA (nonprimeMangoldt_nonneg n))
          (mul_nonneg hD (nonprimeMangoldt_nonneg (n + 2)))
      · simp only [hpow, not_false_eq_true, hprime, and_false, ite_false, sub_zero]
        rw [abs_mul, abs_of_nonneg hqΛ]
        have hh := mul_le_mul_of_nonneg_left hbD hqΛ
        have heq : D * nonprimeMangoldt (n + 2) = vonMangoldt (n + 2) * D := by
          simp [nonprimeMangoldt, hprime, mul_comm]
        rw [← heq] at hh
        exact hh.trans (le_add_of_nonneg_left (mul_nonneg hA (nonprimeMangoldt_nonneg n)))
  have he := add_le_add
    (mul_le_mul_of_nonneg_left (nonprimeMangoldt_dyadic_le X) hA)
    (mul_le_mul_of_nonneg_left (nonprimeMangoldt_shifted_dyadic_le X) hD)
  apply hp.trans
  convert he using 1; simp [bilinearExceptionalBound, D, L, Y, add_mul]

theorem tendsto_dyadic_power_log_pow_div (k : ℕ) {a : ℝ} (ha : a < 1) :
    Tendsto (fun X : ℕ => (2 * X + 2 : ℝ) ^ a * (Real.log (2 * X + 2)) ^ k / X)
      atTop (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => (Real.log t) ^ k / t ^ (1 - a)) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := 1 - a) (by linarith)).tendsto_div_nhds_zero
  have harg : Tendsto (fun X : ℕ => (2 : ℝ) * X + 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with X
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hinv : Tendsto (fun X : ℕ => (X : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun X : ℕ => (2 : ℝ) + 2 * (X : ℝ)⁻¹) atTop (nhds 2) := by
    convert (tendsto_const_nhds.add (hinv.const_mul 2)) using 1
    norm_num
  have h := (hlog.comp harg).mul hratio
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hX)
  have hy : (0 : ℝ) < 2 * X + 2 := by positivity
  have hp : (2 * X + 2 : ℝ) ^ (1 - a) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  have heq : (2 * X + 2 : ℝ) ^ a * (2 * X + 2 : ℝ) ^ (1 - a) = 2 * X + 2 := by
    rw [← Real.rpow_add hy]
    simp
  dsimp only [Function.comp_def]
  field_simp
  have heq' : (2 * ((X : ℝ) + 1)) ^ a * (2 * ((X : ℝ) + 1)) ^ (1 - a) =
      2 * ((X : ℝ) + 1) := by simpa only [mul_add, mul_one] using heq
  nlinarith [congrArg (fun t : ℝ => t * (Real.log (2 * ((X : ℝ) + 1))) ^ k) heq']

theorem bilinearExceptionalBound_eq (X : ℕ) :
    bilinearExceptionalBound X =
      (2 / Real.log 2) * ((2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) * (Real.log (2 * X + 2)) ^ 3) +
        32 * ((2 * X + 2 : ℝ) ^ (5 / 6 : ℝ) * (Real.log (2 * X + 2)) ^ 2) := by
  have hy : (0 : ℝ) < 2 * X + 2 := by positivity
  have hp : (2 * X + 2 : ℝ) ^ (1 / 3 : ℝ) * (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) =
      (2 * X + 2 : ℝ) ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add hy]
    norm_num
  unfold bilinearExceptionalBound evenProgressionBound
  rw [Real.sqrt_eq_rpow]
  calc
    _ = (2 / Real.log 2) * ((2 * X + 2 : ℝ) ^ (1 / 2 : ℝ) * (Real.log (2 * X + 2)) ^ 3) +
      32 * (((2 * X + 2 : ℝ) ^ (1 / 3 : ℝ) * (2 * X + 2 : ℝ) ^ (1 / 2 : ℝ)) *
        (Real.log (2 * X + 2)) ^ 2) := by ring
    _ = _ := by rw [hp]

theorem tendsto_bilinearExceptionalBound_div :
    Tendsto (fun X : ℕ => bilinearExceptionalBound X / X) atTop (nhds 0) := by
  have h₁ := (tendsto_dyadic_power_log_pow_div 3 (a := 1 / 2) (by norm_num)).const_mul (2 / Real.log 2)
  have h₂ := (tendsto_dyadic_power_log_pow_div 2 (a := 5 / 6) (by norm_num)).const_mul 32
  simpa only [bilinearExceptionalBound_eq, add_div, mul_div_assoc, mul_zero, add_zero] using h₁.add h₂

/-- The removal cost is sublinear uniformly for any two eventually positive cutoffs.-/
theorem tendsto_bilinearTerm_sub_primeSupport_div (U V : ℕ → ℕ)
    (hU : ∀ᶠ X in atTop, 1 ≤ U X) (hV : ∀ᶠ X in atTop, 1 ≤ V X) :
    Tendsto (fun X : ℕ => (bilinearTerm (U X) (V X) X -
      bilinearPrimeSupport (U X) (V X) X) / X) atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_bilinearExceptionalBound_div
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [hU, hV] with X hUX hVX
    dsimp only [Function.comp_def]
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)]
    exact div_le_div_of_nonneg_right (abs_bilinearTerm_sub_primeSupport_le _ _ X hUX hVX)
      (Nat.cast_nonneg (α := ℝ) X)

end TwinPrime.Analytic
