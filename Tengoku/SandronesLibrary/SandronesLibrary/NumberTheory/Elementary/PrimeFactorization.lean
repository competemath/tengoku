/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.Divisibility
import Tengoku.Seed.Data.Nat.Factorization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 算术基本定理

自然数 `n` 的 `factorization` 记录每个素数在 `n` 中的指数。本文件给出算术基本定理的
两个教材式接口：素因子幂的乘积重构原数，以及非零自然数由全部素因子指数唯一决定。
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- The multiplicity of `p` in a natural number `n` is the greatest exponent `k ≤ n` for which
`p ^ k` divides `n`.  At `n = 0` this bounded definition has value zero.

> **Entry**: number-theory.elementary.prime-factorization-/
def primeMultiplicity (n p : ℕ) : ℕ :=
  Nat.findGreatest (fun k ↦ p ^ k ∣ n) n

/-- The bounded-power definition agrees with Mathlib's factorization exponent for a prime and a
nonzero natural number.
@isnad1 id=eq.2h2v.s5.5638f4c9b39d from=translated src=- shape=1e4a390c vocab=a93c4c4d
-/
theorem primeMultiplicity_eq_factorization {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    primeMultiplicity n p = n.factorization p := by
  unfold primeMultiplicity
  apply Nat.le_antisymm
  · rw [← hp.pow_dvd_iff_le_factorization hn]
    exact Nat.findGreatest_spec (P := fun k ↦ p ^ k ∣ n) (Nat.zero_le n)
      (show p ^ 0 ∣ n by simp)
  · exact Nat.le_findGreatest (Nat.le_of_lt (Nat.factorization_lt p hn))
      ((hp.pow_dvd_iff_le_factorization hn).2 le_rfl)

/-- The multiplicity convention at zero is explicitly zero.
@isnad1 id=eq.0h1v.s4.bbefc6df2c52 from=translated src=- shape=fe2c2146 vocab=ba851ba2
-/
theorem primeMultiplicity_zero (p : ℕ) : primeMultiplicity 0 p = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.findGreatest_le 0)

/-- **素因子分解的存在性（重构形式）**：非零自然数等于其所有素因子幂之积。
> **Entry**: number-theory.elementary.prime-factorization
@isnad1 id=eq.1h1v.s5.4d064af60daa from=translated src=- shape=53a06fd7 vocab=765844e7
-/
theorem prime_factorization_reconstructs {n : ℕ} (hn : n ≠ 0) :
    n.factorization.prod (fun p e ↦ p ^ e) = n := by
  exact Nat.prod_factorization_pow_eq_self hn

/-- **素因子分解的唯一性**：两个非零自然数若每个素因子的指数都相同，则两数相等。
> **Entry**: number-theory.elementary.prime-factorization-/
theorem eq_of_prime_factorization_eq {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, m.factorization p = n.factorization p) : m = n := by
  exact Nat.eq_of_factorization_eq hm hn h

/-- Two nonzero natural numbers are equal when all their textbook prime multiplicities agree.-/
theorem eq_of_primeMultiplicity_eq {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → primeMultiplicity m p = primeMultiplicity n p) : m = n := by
  apply eq_of_prime_factorization_eq hm hn
  intro p
  by_cases hp : p.Prime
  · simpa [primeMultiplicity_eq_factorization hp hm,
      primeMultiplicity_eq_factorization hp hn] using h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end SandronesLibrary.NumberTheory.Elementary
