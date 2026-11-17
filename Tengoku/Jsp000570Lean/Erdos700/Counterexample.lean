import Tengoku.Jsp000570Lean.Erdos700.Minimum
import Tengoku.Jsp000570Lean.Erdos700.CounterexamplePrimes
import Tengoku.Jsp000570Lean.Erdos700.CounterexampleLucas
import Tengoku.Seed.Tactic.IntervalCases
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A counterexample at the zero high-digit boundary

The proposed replacement `c ≥ 3*b-a` for `c ≥ 3*b-a+1` is false, even
under the earlier, stronger size assumption `P ≥ 100*c^5`.
All arithmetic below is checked by the kernel; the enormous binomial
coefficient is handled through Lucas's theorem, never evaluated directly.
-/

namespace Erdos700.Counterexample

def P : ℕ := 25480409371
def N : ℕ := P * (P + 6) * (P + 18) * (P + 48)
def k : ℕ := 19 * P ^ 2 * (P + 18)

theorem four_primes :
    P.Prime ∧ (P + 6).Prime ∧ (P + 18).Prime ∧ (P + 48).Prime := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [P] using prime_P
  · simpa only [P, Nat.reduceAdd] using prime_PA
  · simpa only [P, Nat.reduceAdd] using prime_PB
  · simpa only [P, Nat.reduceAdd] using prime_PC

theorem index_in_range : 1 < k ∧ k ≤ N / 2 := by
  norm_num [k, N, P]

theorem not_dvd_choose_P : ¬ P ∣ N.choose k := by
  apply CounterexampleLucas.not_dvd_choose_of_digits_lt P N k 5 four_primes.1
  · norm_num [N, P]
  · norm_num [k, P]
  · intro i hi
    interval_cases i <;> norm_num [N, k, P]

theorem not_dvd_choose_PB : ¬ (P + 18) ∣ N.choose k := by
  apply CounterexampleLucas.not_dvd_choose_of_digits_lt (P + 18) N k 4
    four_primes.2.2.1
  · norm_num [N, P]
  · norm_num [k, P]
  · intro i hi
    interval_cases i <;> norm_num [N, k, P]

theorem dvd_choose_PA : (P + 6) ∣ N.choose k := by
  by_contra h
  have hd := mod_le_of_not_dvd_choose (P + 6) N k four_primes.2.1 h
  norm_num [N, k, P] at hd

theorem dvd_choose_PC : (P + 48) ∣ N.choose k := by
  by_contra h
  have hd := mod_le_of_not_dvd_choose (P + 48) N k four_primes.2.2.2 h
  norm_num [N, k, P] at hd

theorem gcd_at_index : Nat.gcd N (N.choose k) = (P + 6) * (P + 48) := by
  have hcoprime : (P * (P + 18)).Coprime (N.choose k) :=
    (four_primes.1.coprime_iff_not_dvd.mpr not_dvd_choose_P).mul_left
      (four_primes.2.2.1.coprime_iff_not_dvd.mpr not_dvd_choose_PB)
  have hdistinct : P + 6 ≠ P + 48 := by omega
  have hpair : (P + 6).Coprime (P + 48) :=
    (Nat.coprime_primes four_primes.2.1 four_primes.2.2.2).mpr hdistinct
  have hdvd : (P + 6) * (P + 48) ∣ N.choose k :=
    hpair.mul_dvd_of_dvd_of_dvd dvd_choose_PA dvd_choose_PC
  calc
    Nat.gcd N (N.choose k) =
        Nat.gcd ((P * (P + 18)) * ((P + 6) * (P + 48))) (N.choose k) := by
      congr 1
    _ = (P + 6) * (P + 48) := Nat.gcd_mul_of_coprime_of_dvd hcoprime hdvd

theorem f_strict_upper_bound : f N < P * (P + 6) * (P + 18) := by
  have hupper : f N ≤ (P + 6) * (P + 48) := by
    exact Nat.sInf_le ⟨k, index_in_range.1, index_in_range.2, gcd_at_index.symm⟩
  have hstrict : (P + 6) * (P + 48) < P * (P + 6) * (P + 18) := by
    norm_num [P]
  exact lt_of_le_of_lt hupper hstrict

/-- All hypotheses and the strict failure at one concrete index, bundled
without any unproved primality or digit assumptions.-/
theorem zero_gap_counterexample :
    1 ≤ (6 : ℕ) ∧ 3 * (6 : ℕ) ≤ 18 ∧ (48 : ℕ) = 3 * 18 - 6 ∧
      100 * (48 : ℕ) ^ 5 ≤ P ∧
      P.Prime ∧ (P + 6).Prime ∧ (P + 18).Prime ∧ (P + 48).Prime ∧
      1 < k ∧ k ≤ N / 2 ∧
      Nat.gcd N (N.choose k) = (P + 6) * (P + 48) ∧
      f N < P * (P + 6) * (P + 18) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num [P],
    four_primes.1, four_primes.2.1, four_primes.2.2.1, four_primes.2.2.2,
    index_in_range.1, index_in_range.2, gcd_at_index, f_strict_upper_bound⟩

/-- The zero-gap extension is false even with the original quintic size bound.-/
theorem zero_gap_extension_false :
    ¬ ∀ p a b c : ℕ, 1 ≤ a → 3 * a ≤ b → 3 * b - a ≤ c →
      100 * c ^ 5 ≤ p → p.Prime → (p + a).Prime → (p + b).Prime →
      (p + c).Prime →
      f (p * (p + a) * (p + b) * (p + c)) = p * (p + a) * (p + b) := by
  intro h
  have heq := h P 6 18 48 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [P]) four_primes.1 four_primes.2.1
    four_primes.2.2.1 four_primes.2.2.2
  change f N = P * (P + 6) * (P + 18) at heq
  exact (ne_of_lt f_strict_upper_bound) heq

end Erdos700.Counterexample
