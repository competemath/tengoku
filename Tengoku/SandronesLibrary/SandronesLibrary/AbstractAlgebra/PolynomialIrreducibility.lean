/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.PolynomialDivision
import Tengoku.Seed.RingTheory.Polynomial.GaussLemma
import Tengoku.Seed.RingTheory.Polynomial.RationalRoot
import Tengoku.Seed.RingTheory.Polynomial.Eisenstein.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 抽象代数 / 多项式不可约性、Gauss 引理与判别法

本模块以 Mathlib `Polynomial R` 作为 A3.3 的正式多项式承载，发展不可约多项式的教材判据、
低次数基本例子、本原多项式与 content 分解、整数到有理数的 Gauss 引理、有理根定理，以及
Eisenstein 不可约判别法。所有公开结论均直接陈述在正式多项式承载上，不经过额外包装类型。

证明复用 Mathlib 已验证的多项式整除、分式域、Gauss lemma 和 Eisenstein 基础设施。整数素数版
Eisenstein 通过单生成主理想的成员关系、平方和素性三个私有桥组装，避免重新证明分式约分或商环理论。

> **Entry**: abstract-algebra.poly.irreducible
-/

namespace SandronesLibrary.AbstractAlgebra.PolynomialIrreducibility

open Polynomial

/-! ## 不可约的教材展开与低次数例子 -/

/-- **不可约元的因子判据**：若不可约多项式 `p` 分解为 `p = a * b`，则两个因子中至少一个是单位。
这是教材中“不可约不能作非平凡分解”的直接展开。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem irreducible_factor_isUnit {R : Type*} [CommRing R]
    {p a b : Polynomial R} (hp : Irreducible p) (hab : p = a * b) :
    IsUnit a ∨ IsUnit b := by
  exact hp.isUnit_or_isUnit hab

/-- **一次因式不可约**：在交换整环上，对任意 `a`，一次多项式 `X - C a` 不可约。
该结论是因式定理与根理论中最基本的不可约例子。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem irreducible_X_sub_C {R : Type*} [CommRing R] [IsDomain R] (a : R) :
    Irreducible (X - C a : Polynomial R) := by
  exact Polynomial.irreducible_X_sub_C a

/-- **不定元不可约**：交换整环上的不定元 `X` 是不可约多项式；它是 `X - C 0` 的基本特例。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem irreducible_X {R : Type*} [CommRing R] [IsDomain R] :
    Irreducible (X : Polynomial R) := by
  exact Polynomial.irreducible_X

/-- **域上一次多项式不可约**：域上的任意次数恰为一的多项式都是不可约的，不要求预先首一化。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem field_irreducible_of_degree_eq_one {K : Type*} [Field K]
    {p : Polynomial K} (hp : p.degree = 1) : Irreducible p := by
  exact Polynomial.irreducible_of_degree_eq_one hp

/-! ## 本原多项式 -/

/-- **本原多项式的教材判据**：多项式本原，当且仅当每个整除它的常数多项式 `C a` 都来自单位系数 `a`。
这把本原性直接表述为“系数没有共同的非单位因子”。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem primitive_iff_constant_dvd_isUnit {R : Type*} [CommSemiring R]
    {p : Polynomial R} :
    p.IsPrimitive ↔ ∀ a : R, C a ∣ p → IsUnit a := by
  exact Polynomial.isPrimitive_iff_isUnit_of_C_dvd

/-- **首一蕴含本原**：首一多项式的首项系数为一，因此任何整除全部系数的常数因子必为单位。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem monic_isPrimitive {R : Type*} [CommSemiring R]
    {p : Polynomial R} (hp : p.Monic) : p.IsPrimitive := by
  exact hp.isPrimitive

/-- **本原多项式乘法封闭**：在规范化 GCD 环上，两个本原多项式的乘积仍然本原，这是 Gauss 引理的 content 形式。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem primitive_mul {R : Type*} [CommRing R] [NormalizedGCDMonoid R]
    {p q : Polynomial R} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  exact hp.mul hq

/-! ## Content 与本原部分 -/

/-- **本原性与 content**：在规范化 GCD 环上，多项式本原当且仅当其规范化 content 等于一。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem primitive_iff_content_eq_one {R : Type*} [CommRing R] [NormalizedGCDMonoid R]
    {p : Polynomial R} : p.IsPrimitive ↔ p.content = 1 := by
  exact Polynomial.isPrimitive_iff_content_eq_one

/-- **content 与本原部分分解**：每个多项式都等于其 content 对应的常数多项式乘以本原部分 `primPart`。
零多项式沿用 Mathlib 对本原部分的统一约定。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem eq_C_content_mul_primPart {R : Type*} [CommRing R] [NormalizedGCDMonoid R]
    (p : Polynomial R) : p = C p.content * p.primPart := by
  exact Polynomial.eq_C_content_mul_primPart p

/-- **Gauss content 乘法公式**：在强规范化 GCD 环上，乘积的 content 等于两个因子 content 的乘积。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem content_mul {R : Type*} [CommRing R] [StrongNormalizedGCDMonoid R]
    {p q : Polynomial R} : (p * q).content = p.content * q.content := by
  exact Polynomial.content_mul

/-! ## 整系数 Gauss 引理 -/

/-- **整数 Gauss 引理**：本原整系数多项式在 `ℤ[X]` 中不可约，当且仅当逐系数映到 `ℚ[X]` 后不可约。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem integer_gauss_irreducible_iff_rational_irreducible
    {p : Polynomial ℤ} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) := by
  exact Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp

/-! ## 整系数多项式的有理根 -/

/-- **首一多项式的整根定理**：首一整系数多项式的每个有理根实际上来自某个整数。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem monic_rational_root_is_integer
    {p : Polynomial ℤ} (hp : p.Monic) {r : ℚ}
    (hr : Polynomial.aeval r p = 0) :
    ∃ z : ℤ, r = (z : ℚ) := by
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hp hr
  exact ⟨z, by simpa using hz⟩

/-! ## Eisenstein 判别 -/

/-- **一般 Eisenstein 判别**：整环上的多项式若在素理想 `P` 处满足 Eisenstein 条件、是本原多项式且次数为正，
则该多项式不可约。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem irreducible_of_isEisensteinAt
    {R : Type*} [CommRing R] [IsDomain R]
    {P : Ideal R} {p : Polynomial R}
    (hE : p.IsEisensteinAt P) (hP : P.IsPrime)
    (hprim : p.IsPrimitive) (hpos : 0 < p.natDegree) :
    Irreducible p := by
  exact hE.irreducible hP hprim hpos

/-- 私有桥：整数素元生成的主理想是素理想。-/
private theorem integer_prime_span_isPrime {q : ℤ} (hq : Prime q) :
    (Ideal.span ({q} : Set ℤ)).IsPrime := by
  exact (Ideal.span_singleton_prime hq.ne_zero).mpr hq

/-- 私有桥：整数属于 `q` 生成的主理想，当且仅当 `q` 整除该整数。-/
private theorem integer_mem_prime_span_iff {q x : ℤ} :
    x ∈ Ideal.span ({q} : Set ℤ) ↔ q ∣ x := by
  exact Ideal.mem_span_singleton

/-- 私有桥：整数属于主理想 `(q)` 的平方，当且仅当它被 `q²` 整除。-/
private theorem integer_mem_prime_span_sq_iff {q x : ℤ} :
    x ∈ (Ideal.span ({q} : Set ℤ)) ^ 2 ↔ q ^ 2 ∣ x := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- 私有组装引理：把整数整除条件转换为主理想上的 `IsEisensteinAt` 条件。-/
private theorem integer_eisensteinAt_of_prime_divisibility
    {p : Polynomial ℤ} {q : ℤ}
    (hlc : ¬q ∣ p.leadingCoeff)
    (hcoeff : ∀ n : ℕ, n < p.natDegree → q ∣ p.coeff n)
    (hconst : ¬q ^ 2 ∣ p.coeff 0) :
    p.IsEisensteinAt (Ideal.span ({q} : Set ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun hmem => hlc (integer_mem_prime_span_iff.mp hmem)
  · intro n hn
    exact integer_mem_prime_span_iff.mpr (hcoeff n hn)
  · exact fun hmem => hconst (integer_mem_prime_span_sq_iff.mp hmem)

/-- **整数素数版 Eisenstein 判别**：设 `q` 是整数素元。若 `q` 不整除首项系数、整除所有低次系数、
`q²` 不整除常数项，并且多项式本原且次数为正，则该整系数多项式不可约。
> **Entry**: abstract-algebra.poly.irreducible-/
theorem integer_prime_eisenstein_irreducible
    {p : Polynomial ℤ} {q : ℤ}
    (hq : Prime q)
    (hlc : ¬q ∣ p.leadingCoeff)
    (hcoeff : ∀ n : ℕ, n < p.natDegree → q ∣ p.coeff n)
    (hconst : ¬q ^ 2 ∣ p.coeff 0)
    (hprim : p.IsPrimitive) (hpos : 0 < p.natDegree) :
    Irreducible p := by
  exact irreducible_of_isEisensteinAt
    (integer_eisensteinAt_of_prime_divisibility hlc hcoeff hconst)
    (integer_prime_span_isPrime hq) hprim hpos

end SandronesLibrary.AbstractAlgebra.PolynomialIrreducibility
