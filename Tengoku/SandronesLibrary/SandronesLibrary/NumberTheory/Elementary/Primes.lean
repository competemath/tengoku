/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.Nat.Prime.Factorial
import Tengoku.Seed.Data.Set.Finite.Lattice
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 素数判定与 Euclid 素数无穷定理

本文件当前条目：

- `number-theory.elementary.prime-tests`：试除判据、可执行判定及合数证书；
- `number-theory.elementary.infinite-primes`：阶乘加一版本的 Euclid 论证与素数无穷。

公开判定谓词只说“从 `2` 试除到平方根”，而不是直接把 `Nat.Prime` 当作定义。
布尔函数提供可执行入口，证明则说明其结果对应哪一种数学证书。
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- **试除判据**：`n ≥ 2`，并且从 `2` 到 `√n` 没有 `n` 的因子。

这是初等数论中有限试除算法的教材陈述；平方根界保证只需检查有限范围。
> **Entry**: number-theory.elementary.prime-tests-/
def PassesTrialDivision (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ d : ℕ, 2 ≤ d → d ≤ n.sqrt → ¬ d ∣ n

/-- 可执行的素数布尔测试。它的逻辑规格由 `primeTest_eq_true_iff` 和
`primeTest_eq_false_iff` 给出，而不应把布尔值本身误当作数学证明。
> **Entry**: number-theory.elementary.prime-tests-/
def primeTest (n : ℕ) : Bool :=
  decide n.Prime

/-- 一个自然数为素数，当且仅当它通过平方根以内的全部试除。
> **Entry**: number-theory.elementary.prime-tests
@isnad1 id=iff.0h1v.s2.438712c08073 from=translated src=- shape=fc2c1e2b vocab=525c4148
-/
theorem prime_iff_passesTrialDivision (n : ℕ) :
    n.Prime ↔ PassesTrialDivision n := by
  exact Nat.prime_def_le_sqrt

/-- 布尔测试返回 `true` 当且仅当平方根试除判据成立。
> **Entry**: number-theory.elementary.prime-tests
@isnad1 id=iff.0h1v.s3.e6fac8880f41 from=translated src=- shape=29662511 vocab=d7ebf867
-/
theorem primeTest_eq_true_iff (n : ℕ) :
    primeTest n = true ↔ PassesTrialDivision n := by
  rw [← prime_iff_passesTrialDivision]
  simp [primeTest]

/-- 对 `n ≥ 2`，布尔测试返回 `false` 当且仅当存在一个非平凡真因子。
右侧的 `d` 是可以独立核验的合数证书，不只是一次失败的计算。
> **Entry**: number-theory.elementary.prime-tests
@isnad1 id=iff.1h1v.s5.d6640d88d258 from=translated src=- shape=148e4b98 vocab=ec3eae7c
-/
theorem primeTest_eq_false_iff {n : ℕ} (hn : 2 ≤ n) :
    primeTest n = false ↔ ∃ d : ℕ, d ∣ n ∧ 2 ≤ d ∧ d < n := by
  rw [show primeTest n = false ↔ ¬n.Prime by simp [primeTest]]
  exact Nat.not_prime_iff_exists_dvd_lt hn

/-- 实际素性判定：`97` 通过素数测试。
> **Entry**: number-theory.elementary.prime-tests
@isnad1 id=eq.0h0v.s3.aed57f954907 from=translated src=- shape=d3a93718 vocab=1722f812
-/
theorem primeTest_97 : primeTest 97 = true := by
  norm_num [primeTest]

/-- 实际合数判定：`221` 未通过测试，并由因子 `13` 给出显式证书。
> **Entry**: number-theory.elementary.prime-tests
@isnad1 id=and.0h0v.s4.772d8a81b37d from=translated src=- shape=26d13105 vocab=d8a2aae3
-/
theorem primeTest_221 : primeTest 221 = false ∧ 13 ∣ 221 := by
  norm_num [primeTest]

/-- **Euclid 的阶乘论证**：`n! + 1` 有一个严格大于 `n` 的素因子。

若该素因子不大于 `n`，它也整除 `n!`；于是同时整除 `n!` 与 `n!+1`，从而整除 `1`，
与素数不整除 `1` 矛盾。
> **Entry**: number-theory.elementary.infinite-primes
@isnad1 id=ex.0h1v.s5.f2ccd44f543b from=translated src=- shape=250d7ea5 vocab=6cc7ff63
-/
theorem euclid_prime_above (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p ∣ n.factorial + 1 := by
  let p := (n.factorial + 1).minFac
  have hfactorial : n.factorial + 1 ≠ 1 := by
    exact ne_of_gt (Nat.succ_lt_succ (Nat.factorial_pos n))
  have hp : p.Prime := Nat.minFac_prime hfactorial
  have hpdiv : p ∣ n.factorial + 1 := Nat.minFac_dvd _
  have hnp : n < p := by
    by_contra h
    have hp_factorial : p ∣ n.factorial := hp.dvd_factorial.mpr (Nat.le_of_not_gt h)
    have hp_one : p ∣ 1 := (Nat.dvd_add_iff_right hp_factorial).mpr hpdiv
    exact hp.not_dvd_one hp_one
  exact ⟨p, hnp, hp, hpdiv⟩

/-- Euclid's factorial construction, with primality stated by the textbook trial-division
criterion.
@isnad1 id=ex.0h1v.s5.7c98c5373f59 from=translated src=- shape=250d7ea5 vocab=7d6c456f
-/
theorem euclid_trialDivision_above (n : ℕ) :
    ∃ p : ℕ, n < p ∧ PassesTrialDivision p ∧ p ∣ n.factorial + 1 := by
  obtain ⟨p, hnp, hp, hpdiv⟩ := euclid_prime_above n
  exact ⟨p, hnp, (prime_iff_passesTrialDivision p).1 hp, hpdiv⟩

/-- **素数有无穷多个**。若素数集合有上界 `n`，`euclid_prime_above n` 会产生一个
严格超过该上界的新素数。
> **Entry**: number-theory.elementary.infinite-primes
@isnad1 id=infinite.0h0v.s3.be446de1cb9c from=translated src=- shape=66b19da4 vocab=040ecd32
-/
theorem infinitely_many_primes : Set.Infinite {p : ℕ | p.Prime} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨n, hn⟩
  obtain ⟨p, hnp, hp, -⟩ := euclid_prime_above n
  exact (not_le_of_gt hnp) (hn hp)

/-- Infinitely many natural numbers pass the textbook trial-division criterion.
@isnad1 id=infinite.0h0v.s3.a60338dd9c44 from=translated src=- shape=66b19da4 vocab=aa512baa
-/
theorem infinitely_many_trialDivision_primes :
    Set.Infinite {p : ℕ | PassesTrialDivision p} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨n, hn⟩
  obtain ⟨p, hnp, hp, -⟩ := euclid_trialDivision_above n
  exact (not_le_of_gt hnp) (hn hp)

end SandronesLibrary.NumberTheory.Elementary
