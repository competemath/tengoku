import Tengoku.Twinprime.TwinPrime.Analytic.Vaughan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact sign information for Vaughan's bilinear coefficient

Prime inputs contribute zero. On inputs with no small nontrivial divisors,
the coefficient is exactly `Λ(n) - log n`. These finite facts do not estimate
their correlation with the shifted prime weight.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

theorem vaughanBilinear_eq_zero_of_prime (U V p : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hp : Nat.Prime p) : (moebiusHigh U * vaughanBeta V) p = 0 := by
  rw [mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d r => moebiusHigh U d * vaughanBeta V r),
    hp.divisors]
  simp [moebiusHigh, cutoffHigh_apply, Nat.not_lt.mpr hU, Nat.div_self hp.pos,
    vaughanBeta_eq_zero_of_le V 1 hV]

theorem vaughanBeta_eq_log_of_small_divisors (V n : ℕ)
    (hsmall : ∀ d ∈ n.divisors, d ≤ V → d = 1) :
    vaughanBeta V n = Real.log n := by
  rw [vaughanBeta_eq_log_sub]
  have hzero : (∑ d ∈ n.divisors, if d ≤ V then vonMangoldt d else 0) = 0 := by
    apply sum_eq_zero
    intro d hd
    by_cases h : d ≤ V
    · simp [hsmall d hd h]
    · simp [h]
  rw [hzero, sub_zero]

theorem moebiusLow_mul_eq_of_small_divisors (U n : ℕ) (hU : 1 ≤ U) (hn : n ≠ 0)
    (hsmall : ∀ d ∈ n.divisors, d ≤ U → d = 1) (g : ArithmeticFunction ℝ) :
    (moebiusLow U * g) n = g n := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d r => moebiusLow U d * g r)]
  rw [sum_eq_single 1]
  · simp [moebiusLow, cutoffLow_apply, hU]
  · intro d hd hd1
    have hnot : ¬d ≤ U := fun h => hd1 (hsmall d hd h)
    simp [moebiusLow, cutoffLow_apply, hnot]
  · simp [hn]

/-- The rough coefficient identity. The support condition rules out every
nontrivial divisor below either cutoff; no distribution assumption occurs.-/
theorem vaughanBilinear_eq_mangoldt_sub_log_of_small_divisors (U V n : ℕ)
    (hU : 1 ≤ U) (hn : n ≠ 0)
    (hsmall : ∀ d ∈ n.divisors, d ≤ max U V → d = 1) :
    (moebiusHigh U * vaughanBeta V) n = vonMangoldt n - Real.log n := by
  have hb : (moebiusHigh U * vaughanBeta V) n =
      (moebiusHigh U * ArithmeticFunction.log) n := by
    rw [mul_apply, mul_apply]
    apply sum_congr rfl
    intro dr hdr
    have hr := Nat.snd_mem_divisors_of_mem_antidiagonal hdr
    have hbeta : vaughanBeta V dr.2 = Real.log dr.2 := by
      apply vaughanBeta_eq_log_of_small_divisors
      intro d hd hdV
      apply hsmall d
      · exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.dvd_of_mem_divisors hr), hn⟩
      · exact hdV.trans (le_max_right U V)
    rw [hbeta, log_apply]
  have hl : (moebiusLow U * ArithmeticFunction.log) n = Real.log n := by
    simpa only [log_apply] using moebiusLow_mul_eq_of_small_divisors U n hU hn
      (fun d hd hdU => hsmall d hd (hdU.trans (le_max_left U V))) ArithmeticFunction.log
  have hsum := congrArg (fun f : ArithmeticFunction ℝ => (f * ArithmeticFunction.log) n)
    (cutoffLow_add_cutoffHigh (μ : ArithmeticFunction ℝ) U)
  change ((moebiusLow U + moebiusHigh U) * ArithmeticFunction.log) n =
    ((μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n at hsum
  rw [add_mul, ArithmeticFunction.add_apply, moebius_mul_log_eq_vonMangoldt, hl] at hsum
  rw [hb]
  linarith

theorem small_divisors_eq_one_of_prime_divisors_gt (z n : ℕ)
    (hrough : ∀ p, Nat.Prime p → p ∣ n → z < p) :
    ∀ d ∈ n.divisors, d ≤ z → d = 1 := by
  intro d hd hdz
  by_contra hd1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hpz := hrough p hp (hpd.trans (Nat.dvd_of_mem_divisors hd))
  have hpdle : p ≤ d := Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hpd
  omega

/-- The same identity with roughness stated through prime divisors.-/
theorem vaughanBilinear_eq_mangoldt_sub_log_of_rough (U V n : ℕ)
    (hU : 1 ≤ U) (hn : n ≠ 0)
    (hrough : ∀ p, Nat.Prime p → p ∣ n → max U V < p) :
    (moebiusHigh U * vaughanBeta V) n = vonMangoldt n - Real.log n :=
  vaughanBilinear_eq_mangoldt_sub_log_of_small_divisors U V n hU hn
    (small_divisors_eq_one_of_prime_divisors_gt (max U V) n hrough)

/-- Rough mixed composites have a negative logarithmic coefficient, regardless
of the number or multiplicity of their prime factors.-/
theorem vaughanBilinear_eq_neg_log_of_rough_not_prime_pow (U V n : ℕ)
    (hU : 1 ≤ U) (hn : n ≠ 0)
    (hrough : ∀ p, Nat.Prime p → p ∣ n → max U V < p)
    (hnpow : ¬IsPrimePow n) :
    (moebiusHigh U * vaughanBeta V) n = -Real.log n := by
  rw [vaughanBilinear_eq_mangoldt_sub_log_of_rough U V n hU hn hrough,
    vonMangoldt_eq_zero_iff.mpr hnpow, zero_sub]

theorem vaughanBeta_div_le_log (V n d : ℕ) (hd : d ∈ n.divisors) :
    vaughanBeta V (n / d) ≤ Real.log n := by
  calc
    _ ≤ Real.log (n / d : ℕ) := vaughanBeta_le_log V (n / d)
    _ ≤ Real.log n := Real.log_le_log
      (by exact_mod_cast Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd))
      (by exact_mod_cast Nat.div_le_self n d)

/-- A uniform divisor-count bound for the complete signed coefficient.-/
theorem abs_vaughanBilinear_le_card_divisors_mul_log (U V n : ℕ) :
    |(moebiusHigh U * vaughanBeta V) n| ≤ (n.divisors.card : ℝ) * Real.log n := by
  rw [mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d r => moebiusHigh U d * vaughanBeta V r)]
  calc
    _ ≤ ∑ d ∈ n.divisors, |moebiusHigh U d * vaughanBeta V (n / d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, Real.log n := by
      apply sum_le_sum
      intro d hd
      have hmu : |moebiusHigh U d| ≤ 1 := by
        by_cases h : U < d
        · simp only [moebiusHigh, cutoffHigh_apply, ite_eq_left h]
          change |(μ d : ℝ)| ≤ 1
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        · simp [moebiusHigh, cutoffHigh_apply, h]
      rw [abs_mul, abs_of_nonneg (vaughanBeta_nonneg V (n / d))]
      calc
        _ ≤ 1 * vaughanBeta V (n / d) :=
          mul_le_mul_of_nonneg_right hmu (vaughanBeta_nonneg V (n / d))
        _ ≤ Real.log n := by simpa only [one_mul] using vaughanBeta_div_le_log V n d hd
    _ = _ := by simp

/-- Only the squarefree divisor `p` can contribute on a positive prime power.
The quotient form retains the integer endpoint exactly.-/
theorem vaughanBilinear_prime_pow (U V p a : ℕ) (hU : 1 ≤ U)
    (hp : Nat.Prime p) (ha : 1 ≤ a) :
    (moebiusHigh U * vaughanBeta V) (p ^ a) =
      if U < p then -vaughanBeta V (p ^ a / p) else 0 := by
  rw [mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d r => moebiusHigh U d * vaughanBeta V r),
    Nat.sum_divisors_prime_pow hp]
  rw [sum_eq_single 1]
  · simp [moebiusHigh, cutoffHigh_apply, moebius_apply_prime hp]
  · intro k _ hk1
    by_cases hk0 : k = 0
    · simp [hk0, moebiusHigh, cutoffHigh_apply, Nat.not_lt.mpr hU]
    · have hm : μ (p ^ k) = 0 := by
        rw [moebius_apply_prime_pow hp hk0, ite_eq_right hk1]
      simp [moebiusHigh, cutoffHigh_apply, hm]
  · simp only [mem_range]
    omega

/-- Prime powers have a much smaller coefficient bound than the general
divisor-count estimate. This is uniform in both positive cutoffs.-/
theorem abs_vaughanBilinear_prime_pow_le_log (U V p a : ℕ) (hU : 1 ≤ U)
    (hp : Nat.Prime p) :
    |(moebiusHigh U * vaughanBeta V) (p ^ a)| ≤ Real.log (p ^ a : ℕ) := by
  by_cases ha : a = 0
  · simp [ha, moebiusHigh, cutoffHigh_apply, Nat.not_lt.mpr hU]
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [vaughanBilinear_prime_pow U V p a hU hp ha1]
    split_ifs
    · rw [abs_neg, abs_of_nonneg (vaughanBeta_nonneg V (p ^ a / p))]
      exact vaughanBeta_div_le_log V (p ^ a) p
        (Nat.mem_divisors.mpr ⟨dvd_pow_self p ha, pow_ne_zero a hp.ne_zero⟩)
    · simp only [abs_zero]
      exact Real.log_nonneg (by exact_mod_cast Nat.one_le_pow a p hp.one_le)

end TwinPrime.Analytic
