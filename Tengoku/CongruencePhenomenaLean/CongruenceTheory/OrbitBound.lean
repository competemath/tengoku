import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Formalization of Lemma `lem:orbit-bound` ("Equipartition orbit bound") from
the manuscript, the sole numerical input to Theorem `thm:strong` (Strong
two-adic lifting). We give a shorter, self-contained derivation than the
manuscript's, using Mathlib's Kummer/Legendre `Nat.factorization` API
directly instead of re-deriving Lucas' theorem by hand; the final numeric
inequality proved is identical to the manuscript's `eq:factorial-bound`.
-/

namespace CongruenceTheory

open Nat

/-- The 2-adic valuation of a natural number, via `Nat.factorization`.-/
noncomputable def v2 (m : ℕ) : ℕ := m.factorization 2

/--
@isnad1 id=prime.0h0v.s2.5fb530e88d94 from=translated src=- shape=e590c3e1 vocab=1464e337
-/
lemma v2_two_prime : Nat.Prime 2 := by norm_num

/-- Auxiliary fact: for `t ≥ 1`, `v2(t) ≤ v2((t-1)!) + 1`. The single factor
`2^(v2(t)-1) ≤ t - 1` already present among `1, ..., t-1` accounts for it.
@isnad1 id=le.1h1v.s5.c510f423a7a2 from=translated src=- shape=5eb8a616 vocab=a139c2e7
-/
lemma v2_le_v2_pred_factorial_add_one (t : ℕ) (ht : 1 ≤ t) :
    v2 t ≤ v2 ((t - 1)!) + 1 := by
  rcases Nat.eq_zero_or_pos (v2 t) with hc0 | hcpos
  · omega
  · set c := v2 t with hcdef
    have htne : t ≠ 0 := by omega
    have hpow : (2:ℕ) ^ c ∣ t :=
      (Nat.Prime.pow_dvd_iff_le_factorization v2_two_prime htne).mpr le_rfl
    have ht2c : (2:ℕ) ^ c ≤ t := Nat.le_of_dvd (by omega) hpow
    have heq : (2:ℕ) ^ (c - 1) * 2 = 2 ^ c := by
      rw [← pow_succ]
      congr 1
      omega
    have hxpos : 1 ≤ (2:ℕ) ^ (c - 1) := Nat.one_le_two_pow
    have hle : (2:ℕ) ^ (c - 1) ≤ t - 1 := by omega
    have hdvd2 : (2:ℕ) ^ (c - 1) ∣ (t - 1)! :=
      Nat.dvd_factorial (by positivity) hle
    have hval : c - 1 ≤ v2 ((t - 1)!) :=
      (Nat.Prime.pow_dvd_iff_le_factorization v2_two_prime
        (Nat.factorial_ne_zero _)).mp hdvd2
    omega

/-- Factorial valuation is monotone.
@isnad1 id=le.1h2v.s4.33da91ea2232 from=translated src=- shape=e178799e vocab=9f9fc165
-/
lemma v2_factorial_mono {m n : ℕ} (h : m ≤ n) : v2 (m !) ≤ v2 (n !) :=
  Nat.factorization_le_factorization_of_dvd_right
    (Nat.factorial_dvd_factorial h) (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero n)

/-- The key elementary inequality behind the orbit bound, isolated from the
prime-power structure of `n = 2^s`: for `1 ≤ a, b`,
`max(v2(a!), v2(b!)) + 1 ≥ v2(a) + v2(b)`.
@isnad1 id=le.2h2v.s5.672fe1c81828 from=translated src=- shape=0dc11cb4 vocab=aa878f72
-/
lemma max_v2_factorial_add_one_ge (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    v2 a + v2 b ≤ max (v2 (a !)) (v2 (b !)) + 1 := by
  wlog hab : a ≤ b generalizing a b
  · have := this b a hb ha (by omega)
    rw [max_comm]
    omega
  have h1 : v2 a ≤ v2 ((a - 1)!) + 1 := v2_le_v2_pred_factorial_add_one a ha
  have h2 : v2 ((a - 1)!) ≤ v2 ((b - 1)!) := v2_factorial_mono (by omega)
  have h3 : v2 (b !) = v2 b + v2 ((b - 1)!) := by
    have heqb : b * (b - 1)! = b ! := Nat.mul_factorial_pred (by omega)
    simp only [v2, ← heqb,
      Nat.factorization_mul (show b ≠ 0 by omega) (Nat.factorial_ne_zero (b - 1)),
      Finsupp.add_apply]
  have h4 : v2 a + v2 b ≤ v2 (b !) + 1 := by omega
  have h5 : v2 (b !) ≤ max (v2 (a !)) (v2 (b !)) := le_max_right _ _
  omega

end CongruenceTheory
