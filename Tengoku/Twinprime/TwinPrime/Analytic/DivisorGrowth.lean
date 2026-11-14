import Tengoku.Seed.NumberTheory.ArithmeticFunction.Misc
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An explicit sub-square-root divisor bound

The elementary estimate `τ(n) ≤ 16 n^(1/3)` is sufficient for removing
proper prime powers from the shifted bilinear sum. It has no distribution
or cancellation hypothesis.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

theorem succ_cube_le_eight_mul_two_pow (a : ℕ) : (a + 1) ^ 3 ≤ 8 * 2 ^ a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha : a < 5
    · interval_cases a <;> norm_num
    · have hb : 2 ≤ a - 3 := by omega
      have hstep : a + 1 ≤ 2 * (a - 3 + 1) := by omega
      have hp := Nat.pow_le_pow_left hstep 3
      have hprev := ih (a - 3) (by omega)
      have heq : a = (a - 3) + 3 := by omega
      calc
        (a + 1) ^ 3 ≤ (2 * (a - 3 + 1)) ^ 3 := hp
        _ = 8 * (a - 3 + 1) ^ 3 := by ring
        _ ≤ 8 * (8 * 2 ^ (a - 3)) := Nat.mul_le_mul_left 8 hprev
        _ = 8 * 2 ^ a := by nth_rw 2 [heq]; rw [pow_add]; norm_num; ring

theorem succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ]
    have : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
    omega

theorem prime_exponent_cube_le (p a : ℕ) (hp : p.Prime) :
    (a + 1) ^ 3 ≤ (if p < 8 then 8 else 1) * p ^ a := by
  by_cases hsmall : p < 8
  · rw [ite_eq_left hsmall]
    exact (succ_cube_le_eight_mul_two_pow a).trans
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hp.two_le a))
  · rw [ite_eq_right hsmall, one_mul]
    calc
      _ ≤ (2 ^ a) ^ 3 := Nat.pow_le_pow_left (succ_le_two_pow a) 3
      _ = 8 ^ a := by rw [← pow_mul, Nat.mul_comm a 3, pow_mul]; norm_num
      _ ≤ p ^ a := Nat.pow_le_pow_left (by omega) a

theorem card_divisors_cube_le (n : ℕ) : n.divisors.card ^ 3 ≤ 4096 * n := by
  by_cases hn : n = 0
  · subst n; simp
  have hs : (n.primeFactors.filter (fun p => p < 8)) ⊆ {2, 3, 5, 7} := by
    intro p hp
    obtain ⟨hpF, hp8⟩ := mem_filter.mp hp
    have hpprime := Nat.prime_of_mem_primeFactors hpF
    interval_cases p <;> norm_num at *
  have hc : (n.primeFactors.filter (fun p => p < 8)).card ≤ 4 := by
    simpa using card_le_card hs
  have hprod : (∏ p ∈ n.primeFactors, if p < 8 then 8 else 1) ≤ (4096 : ℕ) := by
    rw [← prod_filter]
    simp only [prod_const]
    exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 8) hc).trans (by norm_num)
  calc
    _ = ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 3 := by
      rw [Nat.card_divisors hn, prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors, (if p < 8 then 8 else 1) * p ^ n.factorization p :=
      prod_le_prod' (fun p hp => prime_exponent_cube_le p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, if p < 8 then 8 else 1) * n := by
      rw [prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ _ := Nat.mul_le_mul_right n hprod

theorem card_divisors_le_sixteen_cuberoot (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 16 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hc : (n.divisors.card : ℝ) ^ 3 ≤ 4096 * (n : ℝ) := by
    exact_mod_cast card_divisors_cube_le n
  have hr : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 3 : ℝ)
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg n.divisors.card)
    (mul_nonneg (by norm_num) hnonneg) (by decide : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow, hr]
  norm_num
  exact hc

end TwinPrime.Analytic
