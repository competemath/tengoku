import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.Fundamental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lower bounds for the Selberg sum `S` via a completely multiplicative expansion

For a sieve with `0 < ν p < 1` on the sifting primes, the Selberg terms satisfy
`g(l) = ∏_{p ∣ l} ν p / (1 - ν p) = ∏_{p ∣ l} ∑_{k ≥ 1} ν(p)^k`.  Hence, if `f : ℕ →* ℝ` is a
completely multiplicative function agreeing with `ν` on the sifting primes, then for every finite
set `T` of integers `m` whose radical is `l` we have `∑_{m ∈ T} f m ≤ g l`
(`sum_le_selbergTerms_of_primeFactors_eq`), and summing over radicals,

  `∑_{m ∈ T} f m ≤ S = ∑_{l ∣ P, l² ≤ y} g(l)`

for any finite set `T` of integers `m ≤ √y` composed of sifting primes
(`SelbergSieve.selbergBoundingSum_ge_sum`).

This avoids Mertens' theorem entirely: for the twin sieve, `f(m) = 2^{Ω(m)}/m` and `T` the odd
integers up to `√y`, giving `S ≫ (log y)^2` from harmonic-sum bounds alone.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-- Truncated geometric series bound: `∑_{v=1}^{M} x^v ≤ x / (1 - x)` for `0 ≤ x < 1`.-/
theorem geom_sum_Icc_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (M : ℕ) :
    ∑ v ∈ Finset.Icc 1 M, x ^ v ≤ x / (1 - x) := by
  have h1' : 0 < 1 - x := by linarith
  have key : ∀ M : ℕ, (1 - x) * ∑ v ∈ Finset.Icc 1 M, x ^ v = x - x ^ (M + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  rw [le_div_iff₀ h1', mul_comm, key]
  have : 0 ≤ x ^ (M + 1) := pow_nonneg h0 _
  linarith

/-- The per-radical inequality: if every `m ∈ T` is nonzero with prime factors exactly those of
the squarefree `l ∣ P`, then `∑_{m ∈ T} f m ≤ g l`.-/
theorem sum_le_selbergTerms_of_primeFactors_eq (s : BoundingSieve) (f : ℕ →* ℝ)
    (hf_nonneg : ∀ n, 0 ≤ f n) (hfnu : ∀ p, p.Prime → p ∣ s.prodPrimes → f p = s.nu p)
    {l : ℕ} (hl : l ∣ s.prodPrimes) (T : Finset ℕ)
    (hT : ∀ m ∈ T, m ≠ 0 ∧ m.primeFactors = l.primeFactors) :
    ∑ m ∈ T, f m ≤ s.selbergTerms l := by
  classical
  -- `M` bounds all exponents occurring in `T`
  set M : ℕ := T.sup id with hM
  let expo : ℕ → (↥l.primeFactors → ℕ) := fun m p => m.factorization p
  have hexpo : ∀ m ∈ T, f m = ∏ p : ↥l.primeFactors, f p ^ (expo m p) := by
    intro m hm
    obtain ⟨hm0, hmP⟩ := hT m hm
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
    rw [Finsupp.prod, map_prod, Nat.support_factorization, hmP, ← Finset.prod_coe_sort]
    apply prod_congr rfl
    intro p _
    rw [map_pow]
  calc ∑ m ∈ T, f m = ∑ m ∈ T, ∏ p : ↥l.primeFactors, f p ^ (expo m p) := sum_congr rfl hexpo
    _ = ∑ e ∈ T.image expo, ∏ p : ↥l.primeFactors, f p ^ (e p) := by
        rw [sum_image]
        intro m₁ hm₁ m₂ hm₂ heq
        apply Nat.eq_of_factorization_eq (hT m₁ hm₁).1 (hT m₂ hm₂).1
        intro p
        by_cases hp : p ∈ l.primeFactors
        · exact congrFun heq ⟨p, hp⟩
        · have h1 : m₁.factorization p = 0 := by
            rw [← Finsupp.notMem_support_iff, Nat.support_factorization, (hT m₁ hm₁).2]
            exact hp
          have h2 : m₂.factorization p = 0 := by
            rw [← Finsupp.notMem_support_iff, Nat.support_factorization, (hT m₂ hm₂).2]
            exact hp
          rw [h1, h2]
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : ↥l.primeFactors => Finset.Icc 1 M),
          ∏ p : ↥l.primeFactors, f p ^ (e p) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [mem_image] at he
          obtain ⟨m, hm, rfl⟩ := he
          rw [Fintype.mem_piFinset]
          intro p
          rw [mem_Icc]
          obtain ⟨hm0, hmP⟩ := hT m hm
          constructor
          · have hpm : (p : ℕ) ∈ m.primeFactors := by rw [hmP]; exact p.2
            exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hpm) hm0
              (Nat.dvd_of_mem_primeFactors hpm)
          · exact le_trans (Nat.factorization_lt _ hm0).le (Finset.le_sup (f := id) hm)
        · intro e _ _
          exact prod_nonneg fun p _ => pow_nonneg (hf_nonneg p) _
    _ = ∏ p : ↥l.primeFactors, ∑ v ∈ Finset.Icc 1 M, f p ^ v := by rw [prod_univ_sum]
    _ ≤ ∏ p : ↥l.primeFactors, s.nu p / (1 - s.nu p) := by
        apply prod_le_prod
        · intro p _
          exact sum_nonneg fun v _ => pow_nonneg (hf_nonneg _) _
        · intro p _
          have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
          have hpP : (p : ℕ) ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors p.2).trans hl
          rw [hfnu p hp hpP]
          exact geom_sum_Icc_le (s.nu_pos_of_prime p hp hpP).le (s.nu_lt_one_of_prime p hp hpP) M
    _ = s.selbergTerms l := by
        rw [Finset.prod_coe_sort l.primeFactors (fun p => s.nu p / (1 - s.nu p)),
          selbergTerms_apply, ← prod_primeFactors_nu hl, ← prod_mul_distrib]
        apply prod_congr rfl
        intro p _
        rw [div_eq_mul_inv]

end TwinPrime.Sieve

namespace SelbergSieve

open TwinPrime.Sieve

/-- **Lower bound for the Selberg sum.**  If `f : ℕ →* ℝ` is nonnegative, completely
multiplicative, and agrees with `ν` on the sifting primes, then `∑_{m ∈ T} f m ≤ S` for every
finite set `T` of nonzero integers `m` with `m² ≤ y` all of whose prime factors divide `P`.-/
theorem selbergBoundingSum_ge_sum (s : SelbergSieve) (f : ℕ →* ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    (hfnu : ∀ p, p.Prime → p ∣ s.prodPrimes → f p = s.nu p)
    (T : Finset ℕ) (hT0 : ∀ m ∈ T, m ≠ 0)
    (hTP : ∀ m ∈ T, ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes)
    (hTy : ∀ m ∈ T, (m : ℝ) ^ 2 ≤ s.level) :
    ∑ m ∈ T, f m ≤ s.selbergBoundingSum := by
  classical
  let rad : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors, p
  have hrad_mem : ∀ m ∈ T, rad m ∈ s.prodPrimes.divisors := by
    intro m hm
    rw [mem_divisors]
    refine ⟨?_, prodPrimes_ne_zero⟩
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      exact hTP m hm p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hrad_le : ∀ m ∈ T, rad m ≤ m := fun m hm =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero (hT0 m hm)) (Nat.prod_primeFactors_dvd m)
  have hrad_pf : ∀ m ∈ T, (rad m).primeFactors = m.primeFactors := fun m _ =>
    Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp
  calc ∑ m ∈ T, f m
      = ∑ l ∈ s.prodPrimes.divisors, ∑ m ∈ T with rad m = l, f m :=
        (sum_fiberwise_of_maps_to hrad_mem _).symm
    _ ≤ ∑ l ∈ s.prodPrimes.divisors,
          if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
        apply sum_le_sum
        intro l hl
        by_cases hne : (T.filter (fun m => rad m = l)).Nonempty
        · obtain ⟨m₀, hm₀⟩ := hne
          rw [mem_filter] at hm₀
          rw [ite_eq_left]
          · apply sum_le_selbergTerms_of_primeFactors_eq s.toBoundingSieve f hf_nonneg hfnu
              (dvd_of_mem_divisors hl)
            intro m hm
            rw [mem_filter] at hm
            exact ⟨hT0 m hm.1, by rw [← hm.2, hrad_pf m hm.1]⟩
          · have h1 : (l : ℝ) ≤ m₀ := by
              have := hrad_le m₀ hm₀.1
              rw [hm₀.2] at this
              exact_mod_cast this
            calc (l : ℝ) ^ 2 ≤ (m₀ : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
              _ ≤ s.level := hTy m₀ hm₀.1
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne, sum_empty]
          split_ifs
          · exact (selbergTerms_pos (dvd_of_mem_divisors hl)).le
          · exact le_rfl
    _ = s.selbergBoundingSum := rfl

end SelbergSieve
