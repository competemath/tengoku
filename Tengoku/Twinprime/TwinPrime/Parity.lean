import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.Legendre

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The parity obstruction, as a theorem

Every lower-bound sieve is a choice of weights `μ⁻ : ℕ → ℝ` with `∑_{d ∣ n} μ⁻(d) ≤ 1[n = 1]`
(`IsLowerMoebius`, the mirror image of Mathlib's `IsUpperMoebius`).  For any non-negative
sequence `a` and any sifting modulus `P`,

  `∑_{d ∣ P} μ⁻(d) · A_d(a) ≤ ∑_{(f n, P) = 1} a n`,    `A_d(a) := ∑_{d ∣ f n} a n`

(`sum_lowerMoebius_le`).  The right-hand side is the sifted sum; the left-hand side depends on
`a` only through its *Type I data* `(A_d(a))_{d ∣ P}`.

**Selberg's example.**  Take `f n = n(n+2)`, `P = ∏_{p ≤ z} p` with `z² > x`, and compare
`a n = 1` with `a n = 1 + λ(n)` (`λ` = Liouville). To identify the constant sequence's
sifted sum with twin primes requires the stronger assumption `x + 2 < z²`. For
`z ≥ 3` and `x < z²`, every `n ≤ x` with `(n(n+2), P) = 1` is a prime, so `1 + λ(n) = 0` on
the sifted set: the sifted sum of `1 + λ` is *zero*.  The Type I data of the two sequences
differ by the Liouville sums `Λ_d := ∑_{n ≤ x, d ∣ n(n+2)} λ(n)`.  Hence
(`parity_obstruction`)

  `∑_{d ∣ P} μ⁻(d) · #{n ≤ x : d ∣ n(n+2)}  ≤  ∑_{d ∣ P} |μ⁻(d)| · |Λ_d|`

for **every** lower-bound sieve `μ⁻`, unconditionally. This inequality does not estimate its
right-hand side. An `o(x/log² x)` bound for that side would exclude a lower bound of the
expected order from these weights, but would not exclude every smaller positive or unbounded
lower bound. Fixed-modulus Liouville estimates do not supply the uniform rates and summation
losses needed for a growing level. No equidistribution estimate for `λ` is assumed here.

The general-level version (`parity_obstruction_general`, any `z`) bounds the sieve output by
twice the number of sifted `n` with `Ω(n)` even, plus the same discrepancy;
`card_sifted_eq_twin` records that for `z² > x + 2` the sifted set is exactly the set of twin
primes `p ∈ (z, x]`; and `parity_obstruction_upper` is the mirror image for upper-bound sieves
(`a = 1 - λ(n)`): twice the twin count is at most the upper sieve expression plus the
discrepancy. A factor-two asymptotic interpretation requires a negligible discrepancy.
-/

noncomputable section

open Finset ArithmeticFunction
open TwinPrime.Sieve
open scoped ArithmeticFunction.Omega

namespace TwinPrime

/-- Lower-bound sieve weights: `∑_{d ∣ n} μ⁻(d) ≤ 1[n = 1]` for all `n`.-/
def IsLowerMoebius (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

/--
@isnad1 id=eq.1h2v.s5.3ae2b2f0cfb9 from=translated src=- shape=1dd48aca vocab=53c94e14
-/
theorem divisors_gcd_eq_filter (P m : ℕ) (hP : 0 < P) :
    (Nat.gcd P m).divisors = P.divisors.filter (· ∣ m) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    exact ⟨⟨h1, hP.ne'⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left m hP).ne'⟩

/-- Interchange of summation: the sieve expression as a sum over `n`.
@isnad1 id=eq.1h5v.s6.aee10581cbf0 from=translated src=- shape=f68c07c2 vocab=bd94fe89
-/
theorem sum_mul_sum_filter_dvd (μ : ℕ → ℝ) (P : ℕ) (hP : 0 < P) (s : Finset ℕ) (f : ℕ → ℕ)
    (a : ℕ → ℝ) :
    ∑ d ∈ P.divisors, μ d * ∑ n ∈ s with d ∣ f n, a n
      = ∑ n ∈ s, a n * ∑ d ∈ (Nat.gcd P (f n)).divisors, μ d := by
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [divisors_gcd_eq_filter P (f n) hP, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> ring

/--
@isnad1 id=eq.0h4v.s6.0e38d8a0b982 from=translated src=- shape=00b97e48 vocab=f70bb469
-/
theorem sum_filter_coprime_eq (P : ℕ) (s : Finset ℕ) (f : ℕ → ℕ) (a : ℕ → ℝ) :
    ∑ n ∈ s with Nat.Coprime P (f n), a n
      = ∑ n ∈ s, a n * (if Nat.gcd P (f n) = 1 then 1 else 0) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : Nat.gcd P (f n) = 1
  · simp [h]
  · simp [h]

/-- **The lower-bound sieve inequality.**  For lower-bound weights `μ⁻`, a sifting modulus `P`
and a non-negative sequence `a` on a finite set `s`, the sieve expression
`∑_{d ∣ P} μ⁻(d) A_d` is at most the sifted sum.
@isnad1 id=le.3h5v.s7.70763317d360 from=translated src=- shape=2a1bf464 vocab=6aaebabb
-/
theorem sum_lowerMoebius_le (μ : ℕ → ℝ) (hμ : IsLowerMoebius μ) (P : ℕ) (hP : 0 < P)
    (s : Finset ℕ) (f : ℕ → ℕ) (a : ℕ → ℝ) (ha : ∀ n ∈ s, 0 ≤ a n) :
    ∑ d ∈ P.divisors, μ d * ∑ n ∈ s with d ∣ f n, a n
      ≤ ∑ n ∈ s with Nat.Coprime P (f n), a n := by
  rw [sum_mul_sum_filter_dvd μ P hP, sum_filter_coprime_eq]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left (hμ _) (ha n hn)

/-- **The upper-bound sieve inequality** (Mathlib's `BoundingSieve.IsUpperMoebius`, for an
arbitrary non-negative sequence).
@isnad1 id=le.3h5v.s7.8cbbeffc8f65 from=translated src=- shape=2fc307b0 vocab=322e42bd
-/
theorem le_sum_upperMoebius (μ : ℕ → ℝ) (hμ : BoundingSieve.IsUpperMoebius μ) (P : ℕ)
    (hP : 0 < P) (s : Finset ℕ) (f : ℕ → ℕ) (a : ℕ → ℝ) (ha : ∀ n ∈ s, 0 ≤ a n) :
    ∑ n ∈ s with Nat.Coprime P (f n), a n
      ≤ ∑ d ∈ P.divisors, μ d * ∑ n ∈ s with d ∣ f n, a n := by
  rw [sum_mul_sum_filter_dvd μ P hP, sum_filter_coprime_eq]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left (hμ _) (ha n hn)

/-- If `2 ≤ n < z²` and every prime factor of `n` exceeds `z`, then `n` is prime.
@isnad1 id=prime.3h2v.s5.b36f34cc47cc from=translated src=- shape=91e813ac vocab=11fca42f
-/
theorem prime_of_forall_prime_factor_gt {n z : ℕ} (hn : 2 ≤ n) (hnz : n < z * z)
    (h : ∀ p, p.Prime → p ∣ n → z < p) : n.Prime := by
  have hn1 : n ≠ 1 := by omega
  have hpp : n.minFac.Prime := Nat.minFac_prime hn1
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  have hzp : z < n.minFac := h _ hpp (Nat.minFac_dvd n)
  by_cases hm1 : m = 1
  · rw [hm, hm1, mul_one]
    exact hpp
  · exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      omega
    have hqq : m.minFac.Prime := Nat.minFac_prime hm1
    have hqn : m.minFac ∣ n := by
      rw [hm]
      exact Dvd.dvd.mul_left (Nat.minFac_dvd m) _
    have hzq : z < m.minFac := h _ hqq hqn
    have hqle : m.minFac ≤ m := Nat.minFac_le (Nat.pos_of_ne_zero hm0)
    have : z * z < n := by
      calc z * z ≤ z * m.minFac := Nat.mul_le_mul_left z hzq.le
        _ < n.minFac * m.minFac := Nat.mul_lt_mul_of_pos_right hzp hqq.pos
        _ ≤ n.minFac * m := Nat.mul_le_mul_left _ hqle
        _ = n := hm.symm
    omega

/-- For `z ≥ 3` and `n ≤ x < z²`: if `n(n+2)` is coprime to `∏_{p ≤ z} p`, then `n` is prime.
@isnad1 id=prime.4h3v.s5.27cdc6cdf008 from=translated src=- shape=3273049a vocab=fd645a2a
-/
theorem prime_of_coprime_primorial {x z n : ℕ} (hz : 3 ≤ z) (hxz : x < z * z) (hn : n ≤ x)
    (hcop : Nat.Coprime (primorial z) (n * (n + 2))) : n.Prime := by
  rw [coprime_primorial_iff] at hcop
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hcop 2 Nat.prime_two (by omega) (by simp)
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hcop 3 Nat.prime_three hz (by norm_num)
  refine prime_of_forall_prime_factor_gt (z := z) (by omega) (by omega) fun p hp hpn => ?_
  by_contra hle
  push Not at hle
  exact hcop p hp hle (dvd_mul_of_dvd_left hpn _)

/-- For `z ≥ 3` and `x + 2 < z²`, the sifted set `{n ≤ x : (n(n+2), P(z)) = 1}` is exactly the
set of twin primes `n ∈ (z, x]`.
@isnad1 id=iff.3h3v.s6.85824d49c943 from=translated src=- shape=b2206861 vocab=fd645a2a
-/
theorem coprime_primorial_iff_twin {x z n : ℕ} (hz : 3 ≤ z) (hxz : x + 2 < z * z) (hn : n ≤ x) :
    Nat.Coprime (primorial z) (n * (n + 2)) ↔ z < n ∧ n.Prime ∧ (n + 2).Prime := by
  constructor
  · intro hcop
    have hp : n.Prime := prime_of_coprime_primorial hz (by omega) hn hcop
    rw [coprime_primorial_iff] at hcop
    have hq : (n + 2).Prime := by
      refine prime_of_forall_prime_factor_gt (z := z) (by omega) (by omega) fun p hpr hpn => ?_
      by_contra hle
      push Not at hle
      exact hcop p hpr hle (dvd_mul_of_dvd_right hpn _)
    refine ⟨?_, hp, hq⟩
    by_contra hle
    push Not at hle
    exact hcop n hp hle (dvd_mul_right _ _)
  · rintro ⟨hzn, hp, hq⟩
    rw [coprime_primorial_iff]
    intro p hpr hpz hpd
    rcases (Nat.Prime.dvd_mul hpr).mp hpd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hpr hp).mp h
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hpr hq).mp h
      omega

/--
@isnad1 id=eq.2h2v.s7.f751f34a9fa4 from=translated src=- shape=52eabccd vocab=fe20c407
-/
theorem card_sifted_eq_twin (x z : ℕ) (hz : 3 ≤ z) (hxz : x + 2 < z * z) :
    #{n ∈ range (x + 1) | Nat.Coprime (primorial z) (n * (n + 2))}
      = #{n ∈ range (x + 1) | z < n ∧ n.Prime ∧ (n + 2).Prime} := by
  congr 1
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_range] at hn
  exact coprime_primorial_iff_twin hz hxz (by omega)

/--
@isnad1 id=le.0h1v.s5.19b624ebc4fb from=translated src=- shape=d0fb82f4 vocab=53128843
-/
theorem one_add_liouville_nonneg (n : ℕ) : 0 ≤ 1 + (liouville n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [liouville_apply hn.ne']
    rcases neg_one_pow_eq_or ℤ (Ω n) with h | h <;> rw [h] <;> norm_num

/--
@isnad1 id=le.0h1v.s5.7bac398ea219 from=translated src=- shape=d0fb82f4 vocab=9d4c6992
-/
theorem one_sub_liouville_nonneg (n : ℕ) : 0 ≤ 1 - (liouville n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [liouville_apply hn.ne']
    rcases neg_one_pow_eq_or ℤ (Ω n) with h | h <;> rw [h] <;> norm_num

/-- On the sifted set at a level `z ≥ 3` with `x < z²`, `1 + λ(n)` vanishes identically.
@isnad1 id=eq.2h2v.s7.418df1da6fe2 from=translated src=- shape=77463738 vocab=2da75a95
-/
theorem sum_one_add_liouville_sifted (x z : ℕ) (hz : 3 ≤ z) (hxz : x < z * z) :
    ∑ n ∈ range (x + 1) with Nat.Coprime (primorial z) (n * (n + 2)),
      (1 + (liouville n : ℝ)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  have hp : n.Prime := prime_of_coprime_primorial hz hxz (by omega) hn.2
  rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp]
  norm_num

/-- On the sifted set at a level `z ≥ 3` with `x < z²`, `1 - λ(n)` is identically `2`.
@isnad1 id=eq.2h2v.s7.573bbc5f5cb2 from=translated src=- shape=799fe63e vocab=56b22a35
-/
theorem sum_one_sub_liouville_sifted (x z : ℕ) (hz : 3 ≤ z) (hxz : x < z * z) :
    ∑ n ∈ range (x + 1) with Nat.Coprime (primorial z) (n * (n + 2)),
      (1 - (liouville n : ℝ))
      = 2 * #{n ∈ range (x + 1) | Nat.Coprime (primorial z) (n * (n + 2))} := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hn
  have hp : n.Prime := prime_of_coprime_primorial hz hxz (by omega) hn.2
  rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp]
  norm_num

/--
@isnad1 id=eq.0h1v.s6.b1cebb3cc924 from=translated src=- shape=23abffc5 vocab=15542e72
-/
theorem sum_filter_one_sub_liouville (s : Finset ℕ) :
    ∑ n ∈ s, (1 - (liouville n : ℝ)) = (#s : ℝ) - ∑ n ∈ s, (liouville n : ℝ) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h3v.s8.b4ccbfdec74a from=translated src=- shape=95d9dcec vocab=ddebe239
-/
theorem sieve_expr_split_sub (μ : ℕ → ℝ) (P x : ℕ) :
    ∑ d ∈ P.divisors, μ d * ∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (1 - (liouville n : ℝ))
      = ∑ d ∈ P.divisors, μ d * (#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℝ)
        - ∑ d ∈ P.divisors, μ d * ∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sum_filter_one_sub_liouville, mul_sub]

/--
@isnad1 id=eq.0h1v.s6.952fad7ee343 from=translated src=- shape=23abffc5 vocab=265bf2e0
-/
theorem sum_filter_one_add_liouville (s : Finset ℕ) :
    ∑ n ∈ s, (1 + (liouville n : ℝ)) = (#s : ℝ) + ∑ n ∈ s, (liouville n : ℝ) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The sieve expression for the constant sequence, in terms of that for `1 + λ`.
@isnad1 id=eq.0h3v.s8.2dfe9ffe1d23 from=translated src=- shape=e6cf7949 vocab=7cf7dea0
-/
theorem sieve_expr_split (μ : ℕ → ℝ) (P x : ℕ) :
    ∑ d ∈ P.divisors, μ d * ∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (1 + (liouville n : ℝ))
      = ∑ d ∈ P.divisors, μ d * (#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℝ)
        + ∑ d ∈ P.divisors, μ d * ∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sum_filter_one_add_liouville, mul_add]

/-- **Parity obstruction, general sifting level.**  For every lower-bound sieve `μ⁻`, the sieve
expression for the twin sequence is at most twice the number of sifted `n ≤ x` with `Ω(n)` even,
plus the Liouville discrepancy `∑_{d ∣ P} |μ⁻(d)| |Λ_d|`.
@isnad1 id=le.2h3v.s8.136ff3ea3655 from=translated src=- shape=7d1f609f vocab=35d87192
-/
theorem parity_obstruction_general (x z : ℕ) (hz : 2 ≤ z) (μ : ℕ → ℝ) (hμ : IsLowerMoebius μ) :
    ∑ d ∈ (primorial z).divisors, μ d * (#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℝ)
      ≤ 2 * #{n ∈ range (x + 1) | Nat.Coprime (primorial z) (n * (n + 2)) ∧ Even (Ω n)}
        + ∑ d ∈ (primorial z).divisors,
            |μ d| * |∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)| := by
  have hP : 0 < primorial z := primorial_pos z
  have h := sum_lowerMoebius_le μ hμ (primorial z) hP (range (x + 1)) (fun n => n * (n + 2))
    (fun n => 1 + (liouville n : ℝ)) (fun n _ => one_add_liouville_nonneg n)
  rw [sieve_expr_split] at h
  -- the sifted sum of `1 + λ` is twice the number of sifted `n` with `Ω n` even
  have hsift : ∑ n ∈ range (x + 1) with Nat.Coprime (primorial z) (n * (n + 2)),
      (1 + (liouville n : ℝ))
      = 2 * #{n ∈ range (x + 1) | Nat.Coprime (primorial z) (n * (n + 2)) ∧ Even (Ω n)} := by
    rw [Finset.sum_filter, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hc : Nat.Coprime (primorial z) (n * (n + 2))
    · rw [ite_eq_left hc]
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [coprime_primorial_iff] at hc
        exact hc 2 Nat.prime_two hz (by simp)
      rw [liouville_apply hn0]
      rcases Nat.even_or_odd (Ω n) with he | ho
      · rw [ite_eq_left ⟨hc, he⟩, Even.neg_one_pow he]
        push_cast
        ring
      · rw [ite_eq_right (fun h => (Nat.not_even_iff_odd.mpr ho) h.2), Odd.neg_one_pow ho]
        push_cast
        ring
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.1)]
      simp
  rw [hsift] at h
  have hdisc : -∑ d ∈ (primorial z).divisors,
        μ d * ∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)
      ≤ ∑ d ∈ (primorial z).divisors,
          |μ d| * |∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)| := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d _
    rw [← abs_mul]
    exact neg_le_abs _
  linarith

/-- **The parity obstruction.**  Let `z ≥ 3` with `z² > x`, so that sifting `n(n+2)` by all
primes `≤ z` leaves exactly the twin primes.  For **every** lower-bound sieve `μ⁻`, the sieve
expression `∑_{d ∣ P(z)} μ⁻(d) · #{n ≤ x : d ∣ n(n+2)}` — the only lower bound for the number of
twin primes that Type I information can produce — is bounded by the Liouville discrepancy
`∑_{d ∣ P(z)} |μ⁻(d)| · |∑_{n ≤ x, d ∣ n(n+2)} λ(n)|`.
@isnad1 id=le.3h3v.s7.82ee0c70fd32 from=translated src=- shape=fb4cd29e vocab=dfd44579
-/
theorem parity_obstruction (x z : ℕ) (hz : 3 ≤ z) (hxz : x < z * z)
    (μ : ℕ → ℝ) (hμ : IsLowerMoebius μ) :
    ∑ d ∈ (primorial z).divisors, μ d * (#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℝ)
      ≤ ∑ d ∈ (primorial z).divisors,
          |μ d| * |∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)| := by
  have hP : 0 < primorial z := primorial_pos z
  have h := sum_lowerMoebius_le μ hμ (primorial z) hP (range (x + 1)) (fun n => n * (n + 2))
    (fun n => 1 + (liouville n : ℝ)) (fun n _ => one_add_liouville_nonneg n)
  rw [sieve_expr_split, sum_one_add_liouville_sifted x z hz hxz] at h
  have hdisc : -∑ d ∈ (primorial z).divisors,
        μ d * ∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)
      ≤ ∑ d ∈ (primorial z).divisors,
          |μ d| * |∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)| := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d _
    rw [← abs_mul]
    exact neg_le_abs _
  linarith

/-- The parity obstruction for weights bounded by `1` and supported on `d ≤ D` (a sieve of
*level* `D`): the sieve expression is at most `∑_{d ∣ P(z), d ≤ D} |Λ_d|`.
@isnad1 id=le.5h4v.s8.2b20672f797f from=translated src=- shape=42915523 vocab=dfd44579
-/
theorem parity_obstruction_level (x z D : ℕ) (hz : 3 ≤ z) (hxz : x < z * z)
    (μ : ℕ → ℝ) (hμ : IsLowerMoebius μ) (hbdd : ∀ d, |μ d| ≤ 1)
    (hsupp : ∀ d, D < d → μ d = 0) :
    ∑ d ∈ (primorial z).divisors, μ d * (#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℝ)
      ≤ ∑ d ∈ (primorial z).divisors with d ≤ D,
          |∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)| := by
  refine (parity_obstruction x z hz hxz μ hμ).trans ?_
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro d _
  by_cases hd : d ≤ D
  · rw [ite_eq_left hd]
    exact mul_le_of_le_one_left (abs_nonneg _) (hbdd d)
  · rw [ite_eq_right hd, hsupp d (by omega), abs_zero, zero_mul]

/-- The same sieve expression is also a genuine lower bound for the number of twin primes in
`(z, x]`: the obstruction says that this lower bound is never better than the Liouville
discrepancy.
@isnad1 id=le.3h3v.s7.7b6a610826cb from=translated src=- shape=04f1fa96 vocab=b49c533b
-/
theorem sieve_expr_le_twin_count (x z : ℕ) (hz : 3 ≤ z) (hxz : x + 2 < z * z)
    (μ : ℕ → ℝ) (hμ : IsLowerMoebius μ) :
    ∑ d ∈ (primorial z).divisors, μ d * (#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℝ)
      ≤ #{n ∈ range (x + 1) | z < n ∧ n.Prime ∧ (n + 2).Prime} := by
  have hP : 0 < primorial z := primorial_pos z
  have h := sum_lowerMoebius_le μ hμ (primorial z) hP (range (x + 1)) (fun n => n * (n + 2))
    (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [card_sifted_eq_twin x z hz hxz] at h
  exact h

/-- **Parity obstruction, upper-bound side.**  For `z ≥ 3`, `z² > x + 2`, and every upper-bound
sieve `μ⁺` (Mathlib's `IsUpperMoebius`), twice the number of twin primes in `(z, x]` is at most
the sieve expression plus the Liouville discrepancy. A factor-two asymptotic conclusion
requires a separate negligible-discrepancy estimate. (Selberg's example with `a = 1 - λ(n)`.)
@isnad1 id=le.3h3v.s8.5e8eac9112db from=translated src=- shape=b8cc48b4 vocab=be77171f
-/
theorem parity_obstruction_upper (x z : ℕ) (hz : 3 ≤ z) (hxz : x + 2 < z * z)
    (μ : ℕ → ℝ) (hμ : BoundingSieve.IsUpperMoebius μ) :
    2 * (#{n ∈ range (x + 1) | z < n ∧ n.Prime ∧ (n + 2).Prime} : ℝ)
      ≤ ∑ d ∈ (primorial z).divisors, μ d * (#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℝ)
        + ∑ d ∈ (primorial z).divisors,
            |μ d| * |∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)| := by
  have hP : 0 < primorial z := primorial_pos z
  have h := le_sum_upperMoebius μ hμ (primorial z) hP (range (x + 1)) (fun n => n * (n + 2))
    (fun n => 1 - (liouville n : ℝ)) (fun n _ => one_sub_liouville_nonneg n)
  rw [sieve_expr_split_sub, sum_one_sub_liouville_sifted x z hz (by omega),
    card_sifted_eq_twin x z hz hxz] at h
  have hdisc : -∑ d ∈ (primorial z).divisors,
        μ d * ∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)
      ≤ ∑ d ∈ (primorial z).divisors,
          |μ d| * |∑ n ∈ range (x + 1) with d ∣ n * (n + 2), (liouville n : ℝ)| := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d _
    rw [← abs_mul]
    exact neg_le_abs _
  linarith

end TwinPrime
