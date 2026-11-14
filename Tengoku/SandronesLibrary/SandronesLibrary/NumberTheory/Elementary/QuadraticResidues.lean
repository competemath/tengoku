/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Tengoku.Seed.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二次剩余、Legendre/Jacobi 符号与 Gauss 引理

本文件从教材定义出发：整数 `a` 模 `n` 是二次剩余，意即存在剩余类 `x` 满足
`x² = a`。在素数模下，Legendre 符号把非零剩余与非剩余分别编码为 `1` 和 `-1`；
Euler 判别将这个分类改写成幂同余，Gauss 引理则将它改写成一个有限集合基数的奇偶性。

Jacobi 符号把 Legendre 符号乘法地推广到合数分母。本文件特别给出模 `15` 的反例，
说明 Jacobi 符号等于 `1` 对合数模而言只是必要的筛选信息，并不保证二次剩余。
-/

namespace SandronesLibrary.NumberTheory.Elementary

open Finset Nat ZMod

/-- **二次剩余**：整数 `a` 的模 `n` 剩余类是某个剩余类的平方。
这里允许 `a ≡ 0 (mod n)`；“非零”条件只在 Legendre 分类中另行加入。
> **Entry**: number-theory.elementary.quadratic-residues-/
def IsQuadraticResidue (n : ℕ) (a : ℤ) : Prop :=
  ∃ x : ZMod n, x ^ 2 = a

/-- **二次非剩余**：`a` 模 `n` 非零，并且不是二次剩余。显式包含非零条件可使
Legendre 符号的 `0`、`1`、`-1` 三种取值与三种情形逐一对应。
> **Entry**: number-theory.elementary.quadratic-residues-/
def IsQuadraticNonresidue (n : ℕ) (a : ℤ) : Prop :=
  (a : ZMod n) ≠ 0 ∧ ¬IsQuadraticResidue n a

/-- 本库的二次剩余定义等价于 Mathlib 的环论谓词 `IsSquare`。公开课程接口使用前者，
后者只作为进入有限域理论的实现桥。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=iff.0h2v.s5.795a04bbc173 from=translated src=- shape=86475482 vocab=da680955
-/
theorem quadraticResidue_iff_isSquare (n : ℕ) (a : ℤ) :
    IsQuadraticResidue n a ↔ IsSquare (a : ZMod n) := by
  simp only [IsQuadraticResidue, isSquare_iff_exists_sq, eq_comm]

/-- 零总是二次剩余，因为 `0² = 0`。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=isquadra.0h1v.s3.19d262a20bb5 from=translated src=- shape=8ba9e24c vocab=060f90e9
-/
theorem quadraticResidue_zero (n : ℕ) : IsQuadraticResidue n 0 := by
  exact ⟨0, by simp⟩

/-- 两个二次剩余的乘积仍是二次剩余：若 `x² = a`、`y² = b`，则
`(xy)² = ab`。这个结论直接从见证元构造，而不是调用平方闭包的包装定理。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=isquadra.2h3v.s4.c8a992fdf319 from=translated src=- shape=d203bb48 vocab=c80e173f
-/
theorem quadraticResidue_mul {n : ℕ} {a b : ℤ}
    (ha : IsQuadraticResidue n a) (hb : IsQuadraticResidue n b) :
    IsQuadraticResidue n (a * b) := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  rw [mul_pow, hx, hy]
  norm_cast

/-- 对素数模 `p` 和非零剩余类，Legendre 符号等于 `1` 当且仅当它是二次剩余。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=iff.1h2v.s6.a2cb483c2ccc from=translated src=- shape=4d72b590 vocab=67fe1746
-/
theorem legendre_eq_one_iff_quadraticResidue {p : ℕ} [Fact p.Prime] {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = 1 ↔ IsQuadraticResidue p a := by
  rw [quadraticResidue_iff_isSquare]
  exact legendreSym.eq_one_iff p ha

/-- 对素数模 `p`，Legendre 符号等于 `-1` 当且仅当 `a` 是非零二次非剩余。
非零性在正向证明中由“零本身是平方”推出，而不是额外假设。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=iff.0h2v.s4.7044d0119cc7 from=translated src=- shape=f1ddf79a vocab=d9d7a064
-/
theorem legendre_eq_neg_one_iff_quadraticNonresidue {p : ℕ} [Fact p.Prime] {a : ℤ} :
    legendreSym p a = -1 ↔ IsQuadraticNonresidue p a := by
  rw [legendreSym.eq_neg_one_iff, IsQuadraticNonresidue, quadraticResidue_iff_isSquare]
  constructor
  · intro hnotSquare
    refine ⟨?_, hnotSquare⟩
    intro ha
    apply hnotSquare
    rw [ha]
    exact ⟨0, by simp⟩
  · exact fun h ↦ h.2

/-- **Euler 判别法**：非零整数 `a` 模素数 `p` 是二次剩余，当且仅当
`a^(p/2) = 1` 于 `ZMod p` 中成立。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=iff.1h2v.s7.3a64007f186b from=translated src=- shape=1ff735ee vocab=3a25c7b3
-/
theorem quadraticResidue_iff_eulerCriterion {p : ℕ} [Fact p.Prime] {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    IsQuadraticResidue p a ↔ (a : ZMod p) ^ (p / 2) = 1 := by
  rw [quadraticResidue_iff_isSquare]
  exact ZMod.euler_criterion p ha

/-- Gauss 引理中的“越过半程”计数：考察 `1 ≤ x ≤ p/2`，统计 `a x` 的标准
模 `p` 代表元落在上半区的次数。
> **Entry**: number-theory.elementary.quadratic-residues-/
def gaussUpperHalfCount (p : ℕ) (a : ℤ) : ℕ :=
  #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val}

/-- **Gauss 引理**：对奇素数 `p` 和 `p ∤ a`，Legendre 符号等于
`(-1)` 的“越过半程”次数次幂。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=eq.2h2v.s6.6613054d3e4f from=translated src=- shape=1b617456 vocab=26cc73b3
-/
theorem legendre_eq_neg_one_pow_gaussUpperHalfCount {p : ℕ} [Fact p.Prime] {a : ℤ}
    (hp : p ≠ 2) (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = (-1 : ℤ) ^ gaussUpperHalfCount p a := by
  simpa only [gaussUpperHalfCount] using ZMod.gauss_lemma hp ha

/-- Gauss 引理的二次剩余形式：非零 `a` 是二次剩余，当且仅当越过半程的次数为偶数。
这由 Legendre 的 `1`-分类和 `(-1)^k = 1 ⇔ k` 偶逐层推出。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=iff.2h2v.s6.6d52c3dce0df from=translated src=- shape=5fa37f01 vocab=217841cc
-/
theorem quadraticResidue_iff_gaussUpperHalfCount_even {p : ℕ} [Fact p.Prime] {a : ℤ}
    (hp : p ≠ 2) (ha : (a : ZMod p) ≠ 0) :
    IsQuadraticResidue p a ↔ Even (gaussUpperHalfCount p a) := by
  rw [← legendre_eq_one_iff_quadraticResidue ha,
    legendre_eq_neg_one_pow_gaussUpperHalfCount hp ha,
    neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)]

/-- Gauss 引理的二次非剩余形式：非零 `a` 是二次非剩余，当且仅当越过半程的次数为奇数。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=iff.2h2v.s6.7e9c455b1a00 from=translated src=- shape=5fa37f01 vocab=6e8361f8
-/
theorem quadraticNonresidue_iff_gaussUpperHalfCount_odd {p : ℕ} [Fact p.Prime] {a : ℤ}
    (hp : p ≠ 2) (ha : (a : ZMod p) ≠ 0) :
    IsQuadraticNonresidue p a ↔ Odd (gaussUpperHalfCount p a) := by
  rw [← legendre_eq_neg_one_iff_quadraticNonresidue,
    legendre_eq_neg_one_pow_gaussUpperHalfCount hp ha,
    neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)]

/-- Jacobi 符号在素数分母处退化为 Legendre 符号。这是从素数模理论进入合数模乘法
推广的接口。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=eq.0h2v.s4.1bbc69371c04 from=translated src=- shape=221861ce vocab=7786ec28
-/
theorem jacobi_prime_denominator (p : ℕ) [Fact p.Prime] (a : ℤ) :
    jacobiSym a p = legendreSym p a := by
  exact (jacobiSym.legendreSym.to_jacobiSym p a).symm

/-- 若 `a` 与 `n` 互素，则平方 `a²` 的 Jacobi 符号为 `1`。证明先用 Jacobi 对
分子的乘法性拆开，再用其 `±1` 二分，而不是直接调用现成平方结论。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=eq.1h2v.s5.e46b3fadeb19 from=translated src=- shape=a46b3fd7 vocab=8c356643
-/
theorem jacobi_square_of_coprime {a : ℤ} {n : ℕ} (hcop : a.gcd n = 1) :
    jacobiSym (a ^ 2) n = 1 := by
  rw [pow_two, jacobiSym.mul_left]
  rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;> rw [h] <;> norm_num

/-- Jacobi 符号等于 `1` 在合数模下并不充分：`J(2 | 15) = 1`，但模 `15` 没有
平方等于 `2` 的剩余类。第二部分穷举有限环的十五个元素，因而是可核验的具体反例。
> **Entry**: number-theory.elementary.quadratic-residues
@isnad1 id=and.0h0v.s4.8b173c6eba76 from=translated src=- shape=48af6517 vocab=6c077318
-/
theorem jacobi_one_not_sufficient_for_quadraticResidue :
    jacobiSym 2 15 = 1 ∧ ¬IsQuadraticResidue 15 2 := by
  constructor
  · rw [jacobiSym.at_two (by exact ⟨7, by norm_num⟩ : Odd 15)]
    norm_num [χ₈]
  · rintro ⟨x, hx⟩
    fin_cases x <;> (revert hx; decide)

end SandronesLibrary.NumberTheory.Elementary
