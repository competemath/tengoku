/-
Corrected-budget support: the divisor bound and its exact real-log floor transfer.
New implementation source. Not compiled in the assistant environment.
The protected specification and the previously accepted components are unchanged.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- Each distinct prime factor contributes a factor at least two to the divisor count.-/
theorem two_pow_primeFactors_card_le_tau {m : ℕ} (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ tau m := by
  classical
  rw [tau, Nat.card_divisors hm]
  calc
    2 ^ m.primeFactors.card = ∏ p ∈ m.primeFactors, (2 : ℕ) := by simp
    _ ≤ ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
      gcongr with p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      have hfac : 1 ≤ m.factorization p :=
        (hprime.dvd_iff_one_le_factorization hm).mp hdvd
      omega

/-- Use the real logarithm and integer floor from the unchanged specification.-/
theorem primeFactors_card_le_log_floor {m k : ℕ} (hm : m ≠ 0)
    (htau : tau m ≤ k + 2) :
    (m.primeFactors.card : ℤ) ≤
      Int.floor (Real.log ((k : ℝ) + 2) / Real.log 2) := by
  have hnat : 2 ^ m.primeFactors.card ≤ k + 2 :=
    (two_pow_primeFactors_card_le_tau hm).trans htau
  have hreal : (2 : ℝ) ^ m.primeFactors.card ≤ (k : ℝ) + 2 := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log
    (pow_pos (by norm_num : (0 : ℝ) < 2) m.primeFactors.card) hreal
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  apply Int.le_floor.mpr
  simp only [Int.cast_natCast]
  apply (le_div_iff₀ htwo).mpr
  simpa only [Real.log_pow] using hlog

/-- Sum the exact individual integer bounds; no positivity is assumed at zero.-/
theorem prefix_primeFactor_sum_le_logBudget {H n : ℕ} (hprefix : Prefix H n) :
    ((∑ k ∈ Finset.Icc 1 H, (n - k).primeFactors.card : ℕ) : ℤ) ≤ logBudget H := by
  classical
  rw [Nat.cast_sum]
  unfold logBudget
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨hk1, hkH⟩ := Finset.mem_Icc.mp hk
  have hkn : k < n := lt_of_le_of_lt hkH hprefix.1
  exact primeFactors_card_le_log_floor (by omega : n - k ≠ 0)
    (hprefix.2 k hk1 hkH)

end Erdos647Sieve
end
