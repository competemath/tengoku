/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Jsp000570Lean.Erdos700.DigitSupport
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An integer interface to Lucas digit support

The prime, row, and index remain natural numbers. Explicit row digits and
the resulting digit variables are integers, matching the pair-exclusion API.
There is no sign or size requirement on the fourth coefficient.
-/

namespace Erdos700

/-- Identify the lowest three integer Euclidean digits from an expansion.
@isnad1 id=and.8h6v.s7.90f4c3103c9b from=translated src=- shape=e0f1bb4a vocab=460170a1
-/
theorem int_first_three_digits_of_expansion (p x d3 d2 d1 d0 : ℤ)
    (hp : 0 < p)
    (h0 : 0 ≤ d0) (h0p : d0 < p)
    (h1 : 0 ≤ d1) (h1p : d1 < p)
    (h2 : 0 ≤ d2) (h2p : d2 < p)
    (hx : x = d3 * p ^ 3 + d2 * p ^ 2 + d1 * p + d0) :
    x % p = d0 ∧ x / p % p = d1 ∧ x / p / p % p = d2 := by
  have hnorm : x = d0 + p * (d1 + p * (d2 + p * d3)) := by
    rw [hx]
    ring
  have hdiv1 : x / p = d1 + p * (d2 + p * d3) := by
    rw [hnorm, Int.add_mul_ediv_left _ _ hp.ne',
      Int.ediv_eq_zero_of_lt h0 h0p, zero_add]
  have hdiv2 : x / p / p = d2 + p * d3 := by
    rw [hdiv1, Int.add_mul_ediv_left _ _ hp.ne',
      Int.ediv_eq_zero_of_lt h1 h1p, zero_add]
  constructor
  · rw [hnorm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h0p]
  constructor
  · rw [hdiv1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h1 h1p]
  · rw [hdiv2, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h2 h2p]

/-- Lucas support, expressed directly with integer Euclidean divisions.
This theorem does not require a bound on the number of digits of `k/p`.
@isnad1 id=and.9h7v.s8.a25db06b9a29 from=translated src=- shape=96a7208e vocab=ecc0b3ef
-/
theorem int_lucas_three_digit_bounds (p N k : ℕ) (d3 d2 d1 d0 : ℤ)
    (hp : p.Prime) (hmiss : ¬ p ∣ N.choose k)
    (h0 : 0 ≤ d0) (h0p : d0 < (p : ℤ))
    (h1 : 0 ≤ d1) (h1p : d1 < (p : ℤ))
    (h2 : 0 ≤ d2) (h2p : d2 < (p : ℤ))
    (hN : (N : ℤ) / (p : ℤ) =
      d3 * (p : ℤ) ^ 3 + d2 * (p : ℤ) ^ 2 + d1 * (p : ℤ) + d0) :
    (k : ℤ) / (p : ℤ) % (p : ℤ) ≤ d0 ∧
    (k : ℤ) / (p : ℤ) / (p : ℤ) % (p : ℤ) ≤ d1 ∧
    (k : ℤ) / (p : ℤ) / (p : ℤ) / (p : ℤ) % (p : ℤ) ≤ d2 := by
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  obtain ⟨hD0, hD1, hD2⟩ := int_first_three_digits_of_expansion
    (p : ℤ) ((N : ℤ) / (p : ℤ)) d3 d2 d1 d0 hpz h0 h0p h1 h1p h2 h2p hN
  have hn0 := not_dvd_choose_div p N k hp hmiss
  have hn1 := not_dvd_choose_div p (N / p) (k / p) hp hn0
  have hn2 := not_dvd_choose_div p (N / p / p) (k / p / p) hp hn1
  have hd0 := mod_le_of_not_dvd_choose p (N / p) (k / p) hp hn0
  have hd1 := mod_le_of_not_dvd_choose p (N / p / p) (k / p / p) hp hn1
  have hd2 := mod_le_of_not_dvd_choose p (N / p / p / p) (k / p / p / p) hp hn2
  constructor
  · rw [← hD0]
    exact_mod_cast hd0
  constructor
  · rw [← hD1]
    exact_mod_cast hd1
  · rw [← hD2]
    exact_mod_cast hd2

/-- The bounded integer digit variables required by all six pair exclusions.
@isnad1 id=ex.11h7v.s8.7ef9634ffddf from=translated src=- shape=e4954406 vocab=6655a915
-/
theorem exists_int_three_digits_of_not_dvd_choose
    (p N k : ℕ) (d3 d2 d1 d0 : ℤ)
    (hp : p.Prime) (hpN : p ∣ N) (hmiss : ¬ p ∣ N.choose k)
    (hk : (k : ℤ) / (p : ℤ) < (p : ℤ) ^ 3)
    (h0 : 0 ≤ d0) (h0p : d0 < (p : ℤ))
    (h1 : 0 ≤ d1) (h1p : d1 < (p : ℤ))
    (h2 : 0 ≤ d2) (h2p : d2 < (p : ℤ))
    (hN : (N : ℤ) / (p : ℤ) =
      d3 * (p : ℤ) ^ 3 + d2 * (p : ℤ) ^ 2 + d1 * (p : ℤ) + d0) :
    ∃ u v w : ℤ,
      (k : ℤ) = (p : ℤ) * (u * (p : ℤ) ^ 2 + v * (p : ℤ) + w) ∧
      0 ≤ u ∧ u ≤ d2 ∧ 0 ≤ v ∧ v ≤ d1 ∧ 0 ≤ w ∧ w ≤ d0 := by
  have hpk := dvd_of_not_dvd_choose p N k hp hpN hmiss
  have hkNat : k / p < p ^ 3 := by exact_mod_cast hk
  have hu : (k / p) / p ^ 2 < p := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos hp.pos 2)).mpr
    simpa only [pow_succ, mul_comm] using hkNat
  have huMod : (k / p / p / p) % p = (k / p) / p ^ 2 := by
    rw [Nat.div_div_eq_div_mul (k / p) p p, ← pow_two, Nat.mod_eq_of_lt hu]
  obtain ⟨hw_le, hv_le, hu_le⟩ := int_lucas_three_digit_bounds
    p N k d3 d2 d1 d0 hp hmiss h0 h0p h1 h1p h2 h2p hN
  have hu_le' : (((k / p) / p ^ 2 : ℕ) : ℤ) ≤ d2 := by
    have hcast : (((k / p / p / p) % p : ℕ) : ℤ) ≤ d2 := by
      simpa only [Int.natCast_emod, Int.natCast_ediv] using hu_le
    rwa [huMod] at hcast
  have hv_le' : (((k / p / p) % p : ℕ) : ℤ) ≤ d1 := by
    simpa only [Int.natCast_emod, Int.natCast_ediv] using hv_le
  have hw_le' : (((k / p) % p : ℕ) : ℤ) ≤ d0 := by
    simpa only [Int.natCast_emod, Int.natCast_ediv] using hw_le
  have hrep : k = p * ((k / p) / p ^ 2 * p ^ 2 + (k / p / p % p) * p + k / p % p) := by
    calc
      k = p * (k / p) := (Nat.mul_div_cancel' hpk).symm
      _ = p * ((k / p) / p ^ 2 * p ^ 2 + (k / p / p % p) * p + k / p % p) := by
        rw [← nat_three_digit_expansion p (k / p)]
  refine ⟨((k / p) / p ^ 2 : ℕ), ((k / p / p) % p : ℕ), ((k / p) % p : ℕ), ?_,
    Int.natCast_nonneg _, hu_le', Int.natCast_nonneg _, hv_le', Int.natCast_nonneg _, hw_le'⟩
  exact_mod_cast hrep

/-- If two distinct prime divisors are absent, the second divides the
quotient by the first. This is the divisibility input to the carry lemmas.
@isnad1 id=dvd.7h4v.s6.ac8b5cec40d5 from=translated src=- shape=37ce16aa vocab=c85c4750
-/
theorem int_prime_dvd_quotient_of_two_misses (p q N k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpN : p ∣ N) (hqN : q ∣ N)
    (hmissp : ¬ p ∣ N.choose k) (hmissq : ¬ q ∣ N.choose k) :
    (q : ℤ) ∣ (k : ℤ) / (p : ℤ) := by
  have hpk := dvd_of_not_dvd_choose p N k hp hpN hmissp
  have hqk := dvd_of_not_dvd_choose q N k hq hqN hmissq
  have hprod : q ∣ p * (k / p) := by rwa [Nat.mul_div_cancel' hpk]
  have hquot : q ∣ k / p := by
    rcases hq.dvd_mul.mp hprod with hqp | hquot
    · exact False.elim (hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).symm)
    · exact hquot
  exact_mod_cast hquot

end Erdos700
