import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.Fundamental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bonferroni inequalities and the truncated Möbius function as a lower-bound sieve

* `sum_neg_one_pow_choose` : `∑_{j ≤ m} (-1)^j C(t, j) = (-1)^m C(t-1, m)` for `t ≥ 1`.
* `card_divisors_cardDistinctFactors_eq` : a squarefree `g` has exactly `C(ω g, j)` divisors
  with `j` prime factors.
* `sum_truncMoebius_le` : for squarefree `g` and odd `m`,
  `∑_{d ∣ g, ω d ≤ m} μ d ≤ [g = 1]` (the truncated Möbius function is a lower-bound sieve).
* `sum_mul_multSum_le_siftedSum` : the lower-bound sieve inequality
  `∑_{d ∣ P} w d · A_d ≤ siftedSum` for any `w` with `∑_{d ∣ n} w d ≤ [n = 1]` on `n ∣ P`.

These are the ingredients of Brun's pure sieve.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### Alternating binomial sums -/

/-- `∑_{j ≤ m} (-1)^j C(t, j) = (-1)^m C(t-1, m)` for `t ≥ 1`.-/
theorem sum_neg_one_pow_choose (t m : ℕ) (ht : 1 ≤ t) :
    ∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * (t.choose j : ℤ) = (-1) ^ m * ((t - 1).choose m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.choose_succ_succ' t' m]
    push_cast
    ring

/-! ### Divisors of a squarefree number with a given number of prime factors -/

theorem card_primeFactors_eq (n : ℕ) : #n.primeFactors = ω n := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset]
  rfl

/-- The map `S ↦ ∏_{p ∈ S} p` is a bijection from `j`-subsets of the prime factors of a
squarefree `g` onto the divisors of `g` with `ω = j`.-/
theorem card_divisors_cardDistinctFactors_eq {g : ℕ} (hg : Squarefree g) (j : ℕ) :
    #{d ∈ g.divisors | ω d = j} = (ω g).choose j := by
  rw [← card_primeFactors_eq, ← Finset.card_powersetCard]
  symm
  apply Finset.card_bij (fun S _ => ∏ p ∈ S, p)
  · intro S hS
    rw [mem_powersetCard] at hS
    have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS.1 hp)
    rw [mem_filter, mem_divisors]
    refine ⟨⟨?_, hg.ne_zero⟩, ?_⟩
    · apply Finset.prod_primes_dvd
      · intro p hp; exact (hprime p hp).prime
      · intro p hp; exact Nat.dvd_of_mem_primeFactors (hS.1 hp)
    · rw [← card_primeFactors_eq, Nat.primeFactors_prod hprime, hS.2]
  · intro S hS S' hS' h
    rw [mem_powersetCard] at hS hS'
    have h1 := Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hS.1 hp))
    have h2 := Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hS'.1 hp))
    rw [← h1, ← h2, h]
  · intro d hd
    rw [mem_filter, mem_divisors] at hd
    have hdsq : Squarefree d := hg.squarefree_of_dvd hd.1.1
    refine ⟨d.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hdsq⟩
    rw [mem_powersetCard]
    exact ⟨Nat.primeFactors_mono hd.1.1 hg.ne_zero, by rw [card_primeFactors_eq]; exact hd.2⟩

/-! ### The truncated Möbius function -/

/-- `μ` restricted to numbers with at most `m` prime factors.-/
def truncMoebius (m : ℕ) (d : ℕ) : ℝ := if ω d ≤ m then (μ d : ℝ) else 0

theorem abs_truncMoebius_le (m d : ℕ) : |truncMoebius m d| ≤ 1 := by
  unfold truncMoebius
  split_ifs
  · rw [← Int.cast_abs, abs_moebius]
    split_ifs <;> norm_num
  · simp

/-- For squarefree `g`: `∑_{d ∣ g} truncMoebius m d = ∑_{j ≤ m} (-1)^j C(ω g, j)`.-/
theorem sum_divisors_truncMoebius {g : ℕ} (hg : Squarefree g) (m : ℕ) :
    ∑ d ∈ g.divisors, truncMoebius m d =
      ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * ((ω g).choose j : ℝ) := by
  unfold truncMoebius
  rw [← sum_filter]
  rw [← sum_fiberwise_of_maps_to (g := fun d => ω d) (t := range (m + 1))
    (fun d hd => by rw [mem_filter] at hd; rw [mem_range]; omega)]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [Finset.filter_filter]
  have hsum : ∀ d ∈ {d ∈ g.divisors | ω d ≤ m ∧ ω d = j}, (μ d : ℝ) = (-1 : ℝ) ^ j := by
    intro d hd
    rw [mem_filter] at hd
    have hdsq : Squarefree d := hg.squarefree_of_dvd (dvd_of_mem_divisors hd.1)
    rw [moebius_apply_of_squarefree hdsq,
      ← (cardDistinctFactors_eq_cardFactors_iff_squarefree hdsq.ne_zero).mpr hdsq, hd.2.2]
    push_cast
    ring
  rw [sum_congr rfl hsum, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [← card_divisors_cardDistinctFactors_eq hg j]
  congr 1
  apply congrArg Finset.card
  ext d
  simp only [mem_filter, mem_divisors]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨h1, ?_, h3⟩
    omega

/-- **Bonferroni**: for squarefree `g` and odd `m`, `∑_{d ∣ g} truncMoebius m d ≤ [g = 1]`.-/
theorem sum_truncMoebius_le {g : ℕ} (hg : Squarefree g) {m : ℕ} (hm : Odd m) :
    ∑ d ∈ g.divisors, truncMoebius m d ≤ if g = 1 then 1 else 0 := by
  rw [sum_divisors_truncMoebius hg]
  by_cases h1 : g = 1
  · subst h1
    rw [ite_eq_left rfl]
    simp only [cardDistinctFactors_one]
    rw [sum_range_succ', Nat.choose_zero_right]
    simp only [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, sum_const_zero, zero_add, pow_zero,
      Nat.cast_one, mul_one]
    exact le_rfl
  · rw [ite_eq_right h1]
    have hω : 1 ≤ ω g := by
      rw [← card_primeFactors_eq]
      apply Finset.card_pos.mpr
      rw [Nat.nonempty_primeFactors]
      have := hg.ne_zero
      omega
    have := sum_neg_one_pow_choose (ω g) m hω
    have hcast : ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * ((ω g).choose j : ℝ) =
        (((-1 : ℤ) ^ m * ((ω g - 1).choose m : ℤ) : ℤ) : ℝ) := by
      rw [← this]; push_cast; rfl
    rw [hcast]
    obtain ⟨k, rfl⟩ := hm
    push_cast
    rw [pow_succ, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul]
    have : (0 : ℝ) ≤ ((ω g - 1).choose (2 * k + 1) : ℝ) := by positivity
    linarith

/-! ### The lower-bound sieve inequality -/

/-- If `∑_{d ∣ n} w d ≤ [n = 1]` for every `n ∣ P`, then `∑_{d ∣ P} w d · A_d ≤ siftedSum`.-/
theorem sum_mul_multSum_le_siftedSum (s : BoundingSieve) (w : ℕ → ℝ)
    (hw : ∀ n, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, w d ≤ if n = 1 then 1 else 0) :
    ∑ d ∈ s.prodPrimes.divisors, w d * s.multSum d ≤ s.siftedSum := by
  calc ∑ d ∈ s.prodPrimes.divisors, w d * s.multSum d
      = ∑ n ∈ s.support, ∑ d ∈ s.prodPrimes.divisors, if d ∣ n then s.weights n * w d else 0 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        simp only [multSum]
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        split_ifs <;> ring
    _ = ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, w d := by
        apply sum_congr rfl
        intro n _
        rw [mul_sum, ← sum_filter,
          ← Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
        apply sum_congr
        · ext x
          simp +contextual [dvd_gcd_iff]
        · intros; rfl
    _ ≤ ∑ n ∈ s.support, s.weights n * if Nat.gcd s.prodPrimes n = 1 then 1 else 0 := by
        apply sum_le_sum
        intro n _
        apply mul_le_mul_of_nonneg_left _ (s.weights_nonneg n)
        exact hw _ (Nat.gcd_dvd_left _ _)
    _ = s.siftedSum := (siftedSum_eq_sum_support_mul_ite).symm

end TwinPrime.Sieve
