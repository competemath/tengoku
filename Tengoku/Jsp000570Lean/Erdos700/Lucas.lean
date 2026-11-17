/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Seed.Data.Nat.Choose.Lucas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Lucas bridge for the four-prime criterion

Only the forward implication needed by the arithmetic argument is developed.
No bound on the number of digits is needed in this file.
-/

namespace Erdos700

/-- If a prime does not divide a binomial coefficient, it also does not divide
the binomial coefficient formed after removing the lowest base-`p` digit.-/
theorem not_dvd_choose_div (p n k : ℕ) (hp : p.Prime)
    (h : ¬ p ∣ n.choose k) : ¬ p ∣ (n / p).choose (k / p) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hd
  have hmod : n.choose k ≡
      (n % p).choose (k % p) * (n / p).choose (k / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  apply h
  exact (hmod.dvd_iff (dvd_refl p)).mpr (dvd_mul_of_dvd_right hd _)

/-- Nondivisibility forces the lowest base-`p` digit of `k` to be at most
the corresponding digit of `n`.-/
theorem mod_le_of_not_dvd_choose (p n k : ℕ) (hp : p.Prime)
    (h : ¬ p ∣ n.choose k) : k % p ≤ n % p := by
  let : Fact p.Prime := ⟨hp⟩
  apply le_of_not_gt
  intro hlt
  have hmod : n.choose k ≡
      (n % p).choose (k % p) * (n / p).choose (k / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  rw [Nat.choose_eq_zero_of_lt hlt, zero_mul] at hmod
  exact h ((Nat.modEq_zero_iff_dvd).mp hmod)

/-- Repeatedly removing the lowest base-`p` digit preserves nondivisibility.-/
theorem not_dvd_choose_div_pow (p n k : ℕ) (hp : p.Prime)
    (h : ¬ p ∣ n.choose k) (i : ℕ) :
    ¬ p ∣ (n / p ^ i).choose (k / p ^ i) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      simpa [pow_succ, Nat.div_div_eq_div_mul] using
        not_dvd_choose_div p (n / p ^ i) (k / p ^ i) hp ih

/-- Every digit is bounded when the prime does not divide the binomial.-/
theorem digit_le_of_not_dvd_choose (p n k : ℕ) (hp : p.Prime)
    (h : ¬ p ∣ n.choose k) (i : ℕ) :
    k / p ^ i % p ≤ n / p ^ i % p :=
  mod_le_of_not_dvd_choose p (n / p ^ i) (k / p ^ i) hp
    (not_dvd_choose_div_pow p n k hp h i)

/-- If the lowest digit of `n` is zero, so is that of `k`.-/
theorem dvd_of_not_dvd_choose (p n k : ℕ) (hp : p.Prime)
    (hpn : p ∣ n) (h : ¬ p ∣ n.choose k) : p ∣ k := by
  have hd := mod_le_of_not_dvd_choose p n k hp h
  rw [Nat.mod_eq_zero_of_dvd hpn] at hd
  exact Nat.dvd_of_mod_eq_zero (Nat.le_zero.mp hd)

/-- The precise forward Lucas criterion used in the four-prime argument.-/
theorem lucas_quotient_digits (p n k : ℕ) (hp : p.Prime)
    (hpn : p ∣ n) (h : ¬ p ∣ n.choose k) :
    p ∣ k ∧ ∀ i : ℕ, (k / p) / p ^ i % p ≤ (n / p) / p ^ i % p := by
  refine ⟨dvd_of_not_dvd_choose p n k hp hpn h, ?_⟩
  intro i
  exact digit_le_of_not_dvd_choose p (n / p) (k / p) hp
    (not_dvd_choose_div p n k hp h) i

/-- The special index used to attain the proposed lower bound.-/
theorem choose_prime_modEq_div (p n : ℕ) (hp : p.Prime) :
    n.choose p ≡ n / p [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  have hmod : n.choose p ≡
      (n % p).choose (p % p) * (n / p).choose (p / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  simpa only [Nat.mod_self, Nat.choose_zero_right, Nat.div_self hp.pos,
    Nat.choose_one_right, one_mul] using hmod

/-- The largest prime is absent from the gcd at its own index when its
square does not divide `n`, expressed without a squarefree API.-/
theorem not_dvd_choose_prime (p n : ℕ) (hp : p.Prime)
    (h : ¬ p ∣ n / p) : ¬ p ∣ n.choose p := by
  intro hd
  exact h (((choose_prime_modEq_div p n hp).dvd_iff (dvd_refl p)).mp hd)

end Erdos700
