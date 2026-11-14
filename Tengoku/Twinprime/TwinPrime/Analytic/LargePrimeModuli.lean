import Tengoku.Twinprime.TwinPrime.Analytic.PrimeDistribution
import Tengoku.Seed.Data.Nat.Factorization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Counting large prime divisors in aggregated progression errors

Regrouping the products q*d counts a modulus once for each distinct admissible
prime divisor q. If D < (U+1)^(k+1), every positive modulus at most D has at
most k prime divisors above U. The resulting finite estimate uses no prime
distribution hypothesis and retains the integer endpoint D/q.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- A positive integer below the product threshold cannot have too many
distinct prime divisors above U. Prime powers are counted only once.-/
theorem card_large_prime_divisors_le (U D k m : ℕ) (hm : 0 < m) (hmD : m ≤ D)
    (hD : D < (U + 1) ^ (k + 1)) :
    (m.primeFactors.filter (fun p => U < p)).card ≤ k := by
  let s := m.primeFactors.filter (fun p => U < p)
  have hsprod : ∏ p ∈ s, p ∣ m :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd m)
  have hpow : (U + 1) ^ s.card ≤ ∏ p ∈ s, p := by
    apply Finset.pow_card_le_prod
    intro p hp
    exact (mem_filter.mp hp).2
  by_contra hcard
  have hcard' : k + 1 ≤ s.card := by change ¬s.card ≤ k at hcard; omega
  have hle := (pow_le_pow_right₀ (show 1 ≤ U + 1 by omega) hcard').trans
    (hpow.trans ((Nat.le_of_dvd hm hsprod).trans hmD))
  exact (not_le_of_gt hD) hle

/-- The natural quotient endpoint is exactly the positive multiples of q
through D, including a multiple at the upper endpoint.-/
theorem sum_Icc_div_eq_sum_dvd (q D : ℕ) (hq : 0 < q) (E : ℕ → ℝ) :
    (∑ d ∈ Icc 1 (D / q), E (q * d)) =
      ∑ m ∈ (Icc 1 D).filter (q ∣ ·), E m := by
  apply sum_bij (fun d _ => q * d)
  · intro d hd
    obtain ⟨hd1, hdD⟩ := mem_Icc.mp hd
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq hd1, ?_⟩, dvd_mul_right _ _⟩
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hdD
  · intro d _ e _ h
    exact Nat.eq_of_mul_eq_mul_left hq h
  · intro m hm
    obtain ⟨hmI, hqm⟩ := mem_filter.mp hm
    obtain ⟨hm1, hmD⟩ := mem_Icc.mp hmI
    refine ⟨m / q, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hmD⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hm1 hqm) hq
    · exact Nat.mul_div_cancel' hqm
  · intro d _
    rfl

/-- Exact aggregation: each modulus is weighted by the number of its
distinct prime divisors in the specified interval. No sign assumption on E
is needed for the identity.-/
theorem sum_large_prime_modulus_multiples_eq (U W D : ℕ) (E : ℕ → ℝ) :
    (∑ q ∈ (Ioc U W).filter Nat.Prime, ∑ d ∈ Icc 1 (D / q), E (q * d)) =
      ∑ m ∈ Icc 1 D,
        ((m.primeFactors.filter (fun q => U < q ∧ q ≤ W)).card : ℝ) * E m := by
  calc
    _ = ∑ q ∈ (Ioc U W).filter Nat.Prime,
        ∑ m ∈ Icc 1 D, if q ∣ m then E m else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [sum_Icc_div_eq_sum_dvd q D (mem_filter.mp hq).2.pos E, sum_filter]
    _ = ∑ m ∈ Icc 1 D,
        ∑ q ∈ ((Ioc U W).filter Nat.Prime).filter (· ∣ m), E m := by
      rw [sum_comm]
      simp only [sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
      have heq : ((Ioc U W).filter Nat.Prime).filter (· ∣ m) =
          m.primeFactors.filter (fun q => U < q ∧ q ≤ W) := by
        ext q
        simp only [mem_filter, mem_Ioc, Nat.mem_primeFactors_of_ne_zero hm0]
        tauto
      rw [heq]
      simp

/-- The exact modulus count gives an aggregate bound for arbitrary
nonnegative error weights.-/
theorem sum_large_prime_modulus_multiples_le (U W D k : ℕ) (E : ℕ → ℝ)
    (hE : ∀ m ∈ Icc 1 D, 0 ≤ E m) (hD : D < (U + 1) ^ (k + 1)) :
    (∑ q ∈ (Ioc U W).filter Nat.Prime, ∑ d ∈ Icc 1 (D / q), E (q * d)) ≤
      (k : ℝ) * ∑ m ∈ Icc 1 D, E m := by
  rw [sum_large_prime_modulus_multiples_eq, mul_sum]
  apply sum_le_sum
  intro m hm
  have hcard : (m.primeFactors.filter (fun q => U < q ∧ q ≤ W)).card ≤ k := by
    apply (card_le_card (show
      m.primeFactors.filter (fun q => U < q ∧ q ≤ W) ⊆
        m.primeFactors.filter (fun q => U < q) from fun q hq =>
          mem_filter.mpr ⟨(mem_filter.mp hq).1, (mem_filter.mp hq).2.1⟩)).trans
    exact card_large_prime_divisors_le U D k m (mem_Icc.mp hm).1 (mem_Icc.mp hm).2 hD
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hE m hm)

/-- In the cubic-threshold range, aggregation costs at most two copies of
the actual maximal progression-error sum.-/
theorem sum_large_prime_progressionMaxError_le_two (U W D Y : ℕ)
    (hD : D < (U + 1) ^ 3) :
    (∑ q ∈ (Ioc U W).filter Nat.Prime,
      ∑ d ∈ Icc 1 (D / q), progressionMaxError Y (q * d)) ≤
      2 * ∑ m ∈ Icc 1 D, progressionMaxError Y m := by
  simpa using sum_large_prime_modulus_multiples_le U W D 2 (progressionMaxError Y)
    (fun m _ => progressionMaxError_nonneg Y m) hD

/-- A prime larger than every prime factor of its complementary factor is
uniquely determined by the product. The complementary factors may have powers.-/
theorem prime_eq_of_mul_eq_mul_of_primeFactors_lt {q r d e : ℕ}
    (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hd : ∀ p, Nat.Prime p → p ∣ d → p < q)
    (he : ∀ p, Nat.Prime p → p ∣ e → p < r) (h : q * d = r * e) : q = r := by
  by_contra hne
  have hqe : q ∣ e := by
    apply (hq.dvd_mul.mp (h ▸ dvd_mul_right q d)).resolve_left
    exact fun hqr => hne ((Nat.prime_dvd_prime_iff_eq hq hr).mp hqr)
  have hrd : r ∣ d := by
    apply (hr.dvd_mul.mp (h.symm ▸ dvd_mul_right r e)).resolve_left
    exact fun hrq => hne ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrq).symm
  exact (not_lt_of_gt (hd r hr hrd)) (he q hq hqe)

/-- Restricting the complementary factor to primes strictly below q makes
the multiplication map injective. Thus aggregation costs only one copy of
the nonnegative modulus sum, with no power threshold on U or D.-/
theorem sum_largest_prime_modulus_multiples_le (U W D : ℕ) (E : ℕ → ℝ)
    (hE : ∀ m ∈ Icc 1 D, 0 ≤ E m) :
    (∑ q ∈ (Ioc U W).filter Nat.Prime,
      ∑ d ∈ (Icc 1 (D / q)).filter
        (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q), E (q * d)) ≤
      ∑ m ∈ Icc 1 D, E m := by
  let s := ((Ioc U W).filter Nat.Prime).sigma (fun q =>
    (Icc 1 (D / q)).filter (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q))
  let f : (Σ _ : ℕ, ℕ) → ℕ := fun qd => qd.1 * qd.2
  have hinj : Set.InjOn f (↑s) := by
    intro x hx y hy hxy
    obtain ⟨hxq, hxd⟩ := mem_sigma.mp hx
    obtain ⟨hyq, hyd⟩ := mem_sigma.mp hy
    have hq := prime_eq_of_mul_eq_mul_of_primeFactors_lt
      (mem_filter.mp hxq).2 (mem_filter.mp hyq).2
      (mem_filter.mp hxd).2 (mem_filter.mp hyd).2 hxy
    have hd : x.2 = y.2 := by
      apply Nat.eq_of_mul_eq_mul_left (mem_filter.mp hxq).2.pos
      simpa only [f, ← hq] using hxy
    exact Sigma.ext hq (heq_of_eq hd)
  have hsub : s.image f ⊆ Icc 1 D := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hm
    obtain ⟨hxq, hxd⟩ := mem_sigma.mp hx
    obtain ⟨hd1, hdD⟩ := mem_Icc.mp (mem_filter.mp hxd).1
    have hq := (mem_filter.mp hxq).2.pos
    refine mem_Icc.mpr ⟨Nat.mul_pos hq hd1, ?_⟩
    simpa only [f, mul_comm] using (Nat.le_div_iff_mul_le hq).mp hdD
  calc
    _ = ∑ x ∈ s, E (f x) := by simp only [s, f, sum_sigma']
    _ = ∑ m ∈ s.image f, E m := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => hE m hm)

/-- The unique-largest-prime restriction directly bounds the actual
maximal progression errors by their ordinary unweighted sum.-/
theorem sum_largest_prime_progressionMaxError_le (U W D Y : ℕ) :
    (∑ q ∈ (Ioc U W).filter Nat.Prime,
      ∑ d ∈ (Icc 1 (D / q)).filter
        (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q),
        progressionMaxError Y (q * d)) ≤
      ∑ m ∈ Icc 1 D, progressionMaxError Y m :=
  sum_largest_prime_modulus_multiples_le U W D (progressionMaxError Y)
    (fun m _ => progressionMaxError_nonneg Y m)

end TwinPrime.Analytic
