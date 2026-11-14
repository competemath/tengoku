/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.QuadraticResidues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二次互反律

本文件以 Legendre 符号的乘积形式作为二次互反律的核心入口，然后在本库内推导常用的
等式形式、模 `4` 的两个特化，以及对应的二次剩余陈述。最后把同一符号规律推广到
Jacobi 符号，从而覆盖奇合数之间的互反计算。
-/

namespace SandronesLibrary.NumberTheory.Elementary

open Nat ZMod

/-- **二次互反律（乘积形式）**：不同奇素数 `p,q` 满足
`(p/q)(q/p) = (-1)^((p/2)(q/2))`。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem legendre_quadratic_reciprocity_product {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1 : ℤ) ^ (p / 2 * (q / 2)) := by
  exact legendreSym.quadratic_reciprocity hp hq hpq

/-- 二次互反律的等式形式。它不是再次包装底层定理：证明将乘积形式乘上
`(q/p)`，再用非零 Legendre 符号的平方等于 `1` 消去该因子。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem legendre_quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p = (-1 : ℤ) ^ (p / 2 * (q / 2)) * legendreSym p q := by
  have hqmod : ((q : ℤ) : ZMod p) ≠ 0 := by
    norm_cast
    exact prime_ne_zero p q hpq
  have hsq : legendreSym p q ^ 2 = 1 := legendreSym.sq_one p hqmod
  calc
    legendreSym q p = legendreSym q p * 1 := (mul_one _).symm
    _ = legendreSym q p * legendreSym p q ^ 2 := by rw [hsq]
    _ = (legendreSym q p * legendreSym p q) * legendreSym p q := by ring
    _ = (-1 : ℤ) ^ (p / 2 * (q / 2)) * legendreSym p q := by
      rw [legendre_quadratic_reciprocity_product hp hq hpq]

/-- 若一个素数模 `4` 余 `1`，交换两个奇素数时 Legendre 符号不变。
相等素数单独由自反性处理；不同情形由本库互反律等式形式和符号指数化简推出。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem legendre_reciprocity_one_mod_four {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p % 4 = 1) (hq : q ≠ 2) :
    legendreSym q p = legendreSym p q := by
  by_cases hpq : p = q
  · subst q
    rfl
  · have hp2 : p ≠ 2 := by
      intro h
      subst p
      norm_num at hp
    rw [legendre_quadratic_reciprocity hp2 hq hpq, pow_mul,
      neg_one_pow_div_two_of_one_mod_four hp, one_pow, one_mul]

/-- 若两个素数都模 `4` 余 `3`，交换它们时 Legendre 符号变号。
素数相等时两边都为零；不同时互反律中的符号指数为奇数。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem legendre_reciprocity_three_mod_four {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = -legendreSym p q := by
  by_cases hpq : p = q
  · subst q
    rw [(legendreSym.eq_zero_iff p p).2 (by simp)]
    simp
  · have hp2 : p ≠ 2 := by
      intro h
      subst p
      norm_num at hp
    have hq2 : q ≠ 2 := by
      intro h
      subst q
      norm_num at hq
    rw [legendre_quadratic_reciprocity hp2 hq2 hpq, pow_mul,
      neg_one_pow_div_two_of_three_mod_four hp,
      neg_one_pow_div_two_of_three_mod_four hq, neg_one_mul]

/-- 二次互反律的剩余形式之一：若 `p ≡ 1 (mod 4)`，则 `q` 模 `p` 为平方
当且仅当 `p` 模 `q` 为平方。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem quadraticResidue_reciprocity_one_mod_four {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : p % 4 = 1) (hq : q ≠ 2) :
    IsQuadraticResidue p q ↔ IsQuadraticResidue q p := by
  by_cases hpq : p = q
  · subst q
    rfl
  · have hqp : (((q : ℕ) : ℤ) : ZMod p) ≠ 0 := by
      norm_cast
      exact prime_ne_zero p q hpq
    have hpq' : (((p : ℕ) : ℤ) : ZMod q) ≠ 0 := by
      norm_cast
      exact prime_ne_zero q p (Ne.symm hpq)
    rw [← legendre_eq_one_iff_quadraticResidue hqp,
      ← legendre_eq_one_iff_quadraticResidue hpq',
      legendre_reciprocity_one_mod_four hp hq]

/-- 二次互反律的剩余形式之二：不同素数 `p,q` 都模 `4` 余 `3` 时，`q` 模 `p`
为二次剩余，当且仅当 `p` 模 `q` 为二次非剩余。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem quadraticResidue_reciprocity_three_mod_four {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : p % 4 = 3) (hq : q % 4 = 3) (hpq : p ≠ q) :
    IsQuadraticResidue p q ↔ IsQuadraticNonresidue q p := by
  have hqp : (((q : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    norm_cast
    exact prime_ne_zero p q hpq
  rw [← legendre_eq_one_iff_quadraticResidue hqp,
    ← legendre_eq_neg_one_iff_quadraticNonresidue,
    legendre_reciprocity_three_mod_four hp hq]
  simp

/-- **Jacobi 二次互反律**：对任意奇自然数 `a,b`，互换分子分母时出现同一个
`(-1)^((a/2)(b/2))` 符号。它将素数互反律乘法地推广到奇合数。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem jacobi_quadratic_reciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    jacobiSym a b = (-1 : ℤ) ^ (a / 2 * (b / 2)) * jacobiSym b a := by
  exact jacobiSym.quadratic_reciprocity ha hb

/-- Jacobi 互反律的模 `4` 余 `1` 特化：此时交换参数不变号。该结论由上一条一般式
化简符号指数得到。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem jacobi_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    jacobiSym a b = jacobiSym b a := by
  rw [jacobi_quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb,
    pow_mul, neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]

/-- Jacobi 互反律的模 `4` 余 `3` 特化：两个参数均属此类时，交换参数恰好变号。
> **Entry**: number-theory.elementary.quadratic-reciprocity-/
theorem jacobi_reciprocity_three_mod_four {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
    jacobiSym a b = -jacobiSym b a := by
  rw [jacobi_quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_three ha))
      (odd_iff.mpr (odd_of_mod_four_eq_three hb)),
    pow_mul, neg_one_pow_div_two_of_three_mod_four ha,
    neg_one_pow_div_two_of_three_mod_four hb, neg_one_mul]

end SandronesLibrary.NumberTheory.Elementary
