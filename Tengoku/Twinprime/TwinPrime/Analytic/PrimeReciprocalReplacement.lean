import Tengoku.Twinprime.TwinPrime.Analytic.NonprimeMangoldtTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite replacements in weighted reciprocal prime sums

The actual Mangoldt sum is separated from its prime terms with the full
proper-prime-power tail. The replacement of `φ(p)` by `p` has a telescoping
reciprocal error. Both estimates allow signed bounded weights.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology

namespace TwinPrime.Analytic

theorem sum_Ioc_reciprocal_pred_mul (U W : ℕ) (hU : 1 ≤ U) (hUW : U ≤ W) :
    (∑ n ∈ Ioc U W, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) =
      1 / (U : ℝ) - 1 / (W : ℝ) := by
  refine Nat.le_induction ?_ ?_ W hUW
  · simp
  intro n hn ih
  rw [sum_Ioc_succ_top hn, ih]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hU.trans hn
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  push_cast
  field_simp [hnpos.ne', hUpos.ne']
  ring

theorem sum_Ioc_reciprocal_pred_mul_le (U W : ℕ) (hU : 1 ≤ U) :
    (∑ n ∈ Ioc U W, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 / (U : ℝ) := by
  by_cases hUW : U ≤ W
  · rw [sum_Ioc_reciprocal_pred_mul U W hU hUW]
    exact sub_le_self _ (by positivity)
  · rw [Ioc_eq_empty_of_le (Nat.le_of_not_ge hUW), sum_empty]
    positivity

theorem abs_sum_prime_totient_sub_reciprocal_le (U W : ℕ) (hU : 1 ≤ U)
    (F : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ p ∈ Ioc U W, p.Prime → |F p| ≤ M) :
    |(∑ p ∈ (Ioc U W).filter Nat.Prime, F p / Nat.totient p) -
      ∑ p ∈ (Ioc U W).filter Nat.Prime, F p / p| ≤ M / U := by
  classical
  have heq : (∑ p ∈ (Ioc U W).filter Nat.Prime, F p / Nat.totient p) -
        (∑ p ∈ (Ioc U W).filter Nat.Prime, F p / p) =
      ∑ p ∈ (Ioc U W).filter Nat.Prime,
        F p * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    have hp := (mem_filter.mp hp).2
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hn0 (n : ℕ) (hn : n ∈ Ioc U W) :
      0 ≤ (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hn2 : 2 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    exact div_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
  rw [heq]
  calc
    _ ≤ ∑ p ∈ (Ioc U W).filter Nat.Prime,
        |F p * (1 / ((p : ℝ) * ((p : ℝ) - 1)))| := abs_sum_le_sum_abs _ _
    _ ≤ M * ∑ p ∈ (Ioc U W).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      rw [abs_mul, abs_of_nonneg (hn0 p hpI)]
      exact mul_le_mul_of_nonneg_right (hF p hpI hpp) (hn0 p hpI)
    _ ≤ M * ∑ n ∈ Ioc U W, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ => hn0 n hn)
    _ ≤ M * (1 / (U : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_reciprocal_pred_mul_le U W hU) hM
    _ = M / U := by ring

/-- The difference is exactly the weighted proper-prime-power sum.-/
theorem sum_mangoldt_reciprocal_sub_prime_eq (U W : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Ioc U W, vonMangoldt n / n * F n) -
      (∑ p ∈ (Ioc U W).filter Nat.Prime, Real.log p / p * F p) =
      ∑ n ∈ Ioc U W, nonprimeMangoldt n / n * F n := by
  classical
  rw [sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · simp [hn, nonprimeMangoldt, vonMangoldt_apply_prime hn]
  · simp [hn, nonprimeMangoldt]

theorem abs_sum_mangoldt_reciprocal_sub_prime_le (U W : ℕ) (F : ℕ → ℝ)
    (M : ℝ) (hF : ∀ n ∈ Ioc U W, |F n| ≤ M) :
    |(∑ n ∈ Ioc U W, vonMangoldt n / n * F n) -
      (∑ p ∈ (Ioc U W).filter Nat.Prime, Real.log p / p * F p)| ≤
      M * ∑ n ∈ Ioc U W, nonprimeMangoldt n / n := by
  rw [sum_mangoldt_reciprocal_sub_prime_eq]
  calc
    _ ≤ ∑ n ∈ Ioc U W, |nonprimeMangoldt n / n * F n| := abs_sum_le_sum_abs _ _
    _ ≤ M * ∑ n ∈ Ioc U W, nonprimeMangoldt n / n := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      have hn0 : 0 ≤ nonprimeMangoldt n / n :=
        div_nonneg (nonprimeMangoldt_nonneg n) (Nat.cast_nonneg n)
      rw [abs_mul, abs_of_nonneg hn0, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hF n hn) hn0

/-- A single positive constant controls every weighted prime-power
replacement, uniformly in both integer endpoints.-/
theorem exists_abs_sum_mangoldt_reciprocal_sub_prime_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ U W : ℕ, 1 ≤ U → ∀ F : ℕ → ℝ,
      ∀ M : ℝ, 0 ≤ M → (∀ n ∈ Ioc U W, |F n| ≤ M) →
      |(∑ n ∈ Ioc U W, vonMangoldt n / n * F n) -
        (∑ p ∈ (Ioc U W).filter Nat.Prime, Real.log p / p * F p)| ≤
        C * M * (U : ℝ) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := exists_nonprimeMangoldt_reciprocal_tail_bound
  refine ⟨C, hC, fun U W hU F M hM hF => ?_⟩
  calc
    _ ≤ M * ∑ n ∈ Ioc U W, nonprimeMangoldt n / n :=
      abs_sum_mangoldt_reciprocal_sub_prime_le U W F M hF
    _ ≤ M * (C * (U : ℝ) ^ (-1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (htail U hU W) hM
    _ = _ := by ring

/-- A growing lower endpoint makes the totient replacement negligible for
every uniformly bounded family of signed prime weights.-/
theorem tendsto_sum_prime_totient_sub_reciprocal
    (U W : ℕ → ℕ) (F : ℕ → ℕ → ℝ) (hU : Tendsto U atTop atTop)
    (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ᶠ X : ℕ in atTop, ∀ p ∈ Ioc (U X) (W X), p.Prime → |F X p| ≤ M) :
    Tendsto (fun X : ℕ =>
      (∑ p ∈ (Ioc (U X) (W X)).filter Nat.Prime, F X p / Nat.totient p) -
        ∑ p ∈ (Ioc (U X) (W X)).filter Nat.Prime, F X p / p)
      atTop (𝓝 0) := by
  have hUr : Tendsto (fun X : ℕ => (U X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hU
  have hlim : Tendsto (fun X : ℕ => M / (U X : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using hUr.inv_tendsto_atTop.const_mul M
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [hU.eventually (eventually_ge_atTop 1), hF] with X hUX hFX
    exact abs_sum_prime_totient_sub_reciprocal_le (U X) (W X) hUX (F X) M hM hFX

/-- The weighted Mangoldt-to-prime replacement is negligible at every
growing lower endpoint, with its actual prime-power error controlled.-/
theorem tendsto_sum_mangoldt_reciprocal_sub_prime
    (U W : ℕ → ℕ) (F : ℕ → ℕ → ℝ) (hU : Tendsto U atTop atTop)
    (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ᶠ X : ℕ in atTop, ∀ n ∈ Ioc (U X) (W X), |F X n| ≤ M) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Ioc (U X) (W X), vonMangoldt n / n * F X n) -
        ∑ p ∈ (Ioc (U X) (W X)).filter Nat.Prime, Real.log p / p * F X p)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := exists_abs_sum_mangoldt_reciprocal_sub_prime_bound
  have hUr : Tendsto (fun X : ℕ => (U X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hU
  have hpow : Tendsto (fun X : ℕ => (U X : ℝ) ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hUr
  have hlim := hpow.const_mul (C * M)
  simp only [mul_zero] at hlim
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [hU.eventually (eventually_ge_atTop 1), hF] with X hUX hFX
    exact hbound (U X) (W X) hUX (F X) M hM hFX

end TwinPrime.Analytic
