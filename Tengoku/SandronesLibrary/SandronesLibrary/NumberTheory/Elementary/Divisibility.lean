/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.Int.GCD
import Tengoku.Seed.Data.Nat.GCD.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 整除、最大公因数与 Bézout 等式

本文件建立初等数论的第一条主线：从自然数带余除法出发，以最大公因数刻画公因子，
再用扩展 Euclidean 算法得到 Bézout 等式及互素的整数线性组合判别。最后给出 Euclid
引理和大于一的自然数必有素因子。
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- **带余除法**：正整数 `n` 除任意自然数 `m`，所得余数严格小于 `n`。
> **Entry**: number-theory.elementary.divisibility-/
theorem euclidean_division (m n : ℕ) (hn : 0 < n) :
    ∃ q r : ℕ, m = q * n + r ∧ r < n := by
  refine ⟨m / n, m % n, ?_, Nat.mod_lt m hn⟩
  simpa [mul_comm, add_comm] using (Nat.mod_add_div m n).symm

/-- 一个自然数整除 `gcd(m,n)`，当且仅当它同时整除 `m` 和 `n`。
> **Entry**: number-theory.elementary.divisibility-/
theorem dvd_gcd_iff {d m n : ℕ} : d ∣ Nat.gcd m n ↔ d ∣ m ∧ d ∣ n := by
  exact Nat.dvd_gcd_iff

/-- **Bézout 等式**：`gcd(m,n)` 是 `m,n` 的一个整数线性组合。

公开结论只断言系数存在；证明内部使用扩展 Euclidean 算法计算的系数。
> **Entry**: number-theory.elementary.divisibility-/
theorem bezout_identity (m n : ℕ) :
    ∃ a b : ℤ, (Nat.gcd m n : ℤ) = (m : ℤ) * a + (n : ℤ) * b := by
  exact ⟨m.gcdA n, m.gcdB n, Nat.gcd_eq_gcd_ab m n⟩

/-- 两个自然数互素，当且仅当 `1` 是它们的一个整数线性组合。
> **Entry**: number-theory.elementary.divisibility-/
theorem coprime_iff_exists_int_linear_combination (m n : ℕ) :
    Nat.Coprime m n ↔ ∃ a b : ℤ, (m : ℤ) * a + (n : ℤ) * b = 1 := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := bezout_identity m n
    exact ⟨a, b, by simpa [Nat.coprime_iff_gcd_eq_one.mp h] using hab.symm⟩
  · rintro ⟨a, b, hab⟩
    rw [Nat.coprime_iff_gcd_eq_one]
    have hdiv : Int.gcd (m : ℤ) (n : ℤ) ∣ 1 :=
      Int.gcd_dvd_iff.mpr ⟨a, b, hab.symm⟩
    simpa [Int.gcd_natCast_natCast] using Nat.dvd_one.mp hdiv

/-- **Euclid 引理**：素数整除乘积，当且仅当它整除至少一个因子。
> **Entry**: number-theory.elementary.divisibility-/
theorem prime_dvd_mul_iff {p m n : ℕ} (hp : Nat.Prime p) :
    p ∣ m * n ↔ p ∣ m ∨ p ∣ n := by
  exact hp.dvd_mul

/-- 每个大于 `1` 的自然数都至少有一个素因子。
> **Entry**: number-theory.elementary.divisibility-/
theorem exists_prime_dvd_of_one_lt {n : ℕ} (hn : 1 < n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n := by
  exact Nat.exists_prime_and_dvd hn.ne'

end SandronesLibrary.NumberTheory.Elementary
