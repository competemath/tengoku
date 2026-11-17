/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Seed.Data.Nat.Choose.Lucas
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Converse Lucas digit support

These general lemmas certify nondivisibility without evaluating a binomial
coefficient. A finite list of digit comparisons suffices once both integers
are below the corresponding power of the prime base.
-/

namespace Erdos700.CounterexampleLucas

/-- Every positive factor in this factorial is below the prime.-/
theorem not_dvd_factorial_of_lt (p n : ℕ) (hp : p.Prime) (hn : n < p) :
    ¬ p ∣ n.factorial := by
  induction n with
  | zero => simpa using hp.not_dvd_one
  | succ n ih =>
      rw [Nat.factorial_succ]
      apply hp.not_dvd_mul
      · intro h
        exact (not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) h)
      · exact ih (Nat.lt_of_succ_lt hn)

/-- A binomial formed from two legal digits, in their natural order, is
nonzero modulo the prime base.-/
theorem not_dvd_choose_small (p n k : ℕ) (hp : p.Prime)
    (hn : n < p) (hk : k ≤ n) : ¬ p ∣ n.choose k := by
  intro hd
  have hfact : p ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  exact not_dvd_factorial_of_lt p n hp hn hfact

/-- Reattach one legal lowest digit to a quotient whose binomial is already
known to be nonzero modulo the base.-/
theorem not_dvd_choose_of_mod_le_of_div (p n k : ℕ) (hp : p.Prime)
    (hd : k % p ≤ n % p)
    (hdiv : ¬ p ∣ (n / p).choose (k / p)) : ¬ p ∣ n.choose k := by
  let : Fact p.Prime := ⟨hp⟩
  have hmod : n.choose k ≡
      (n % p).choose (k % p) * (n / p).choose (k / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hlow := not_dvd_choose_small p (n % p) (k % p) hp (Nat.mod_lt _ hp.pos) hd
  intro h
  exact (hp.not_dvd_mul hlow hdiv) ((hmod.dvd_iff (dvd_refl p)).mp h)

/-- Finite converse Lucas criterion. Only the first `d` digit comparisons
are needed; the strict power bounds prove that all higher digits vanish.-/
theorem not_dvd_choose_of_digits_lt (p n k d : ℕ) (hp : p.Prime)
    (hn : n < p ^ d) (hk : k < p ^ d)
    (hd : ∀ i : ℕ, i < d → k / p ^ i % p ≤ n / p ^ i % p) :
    ¬ p ∣ n.choose k := by
  induction d generalizing n k with
  | zero =>
      have hn0 : n = 0 := by simpa using hn
      have hk0 : k = 0 := by simpa using hk
      subst n
      subst k
      simpa using hp.not_dvd_one
  | succ d ih =>
      apply not_dvd_choose_of_mod_le_of_div p n k hp
      · simpa using hd 0 (Nat.zero_lt_succ d)
      · apply ih (n := n / p) (k := k / p)
        · apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
          simpa only [pow_succ] using hn
        · apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
          simpa only [pow_succ] using hk
        · intro i hi
          simpa only [Nat.div_div_eq_div_mul, pow_succ'] using
            hd (i + 1) (Nat.succ_lt_succ hi)

end Erdos700.CounterexampleLucas
