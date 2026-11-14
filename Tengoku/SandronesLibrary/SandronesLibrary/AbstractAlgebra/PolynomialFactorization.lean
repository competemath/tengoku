/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.PolynomialDivision
import Tengoku.Seed.RingTheory.Polynomial.UniqueFactorization
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 抽象代数 / 域上多项式的唯一分解、根重数与导数

本模块以 Mathlib 的正式承载 `Polynomial K` 建立 A3.4 的教材接口：先给出域上非零
多项式的不可约因子分解、相伴意义下的唯一性与首一规范化分解；再把根重数解释为一次因子
`X - C a` 的最高整除幂，并发展乘积、单根、重根及导数判据；最后在特征零域上用迭代
导数刻画根重数，并把 `roots` 中的计数与重数对应起来。

这些声明直接复用 Mathlib 已成熟验证的唯一分解整环、`normalizedFactors`、`rootMultiplicity`、
形式导数和根多重集接口。公开结论保留教材常用的数学方向与命名，使调用者可以在
`Polynomial K` 上直接推理，同时不重复构造因子分解算法或重证底层唯一分解理论。

> **Entry**: abstract-algebra.poly.factorization
-/

namespace SandronesLibrary.AbstractAlgebra.PolynomialFactorization

open Polynomial
open UniqueFactorizationMonoid

/-! ## 唯一分解 -/

/-- **不可约因子分解的存在性**：域上每个非零多项式都相伴于有限个不可约多项式的乘积。相伴关系准确保留了教材分解中允许相差一个非零常数因子的含义。
> **Entry**: abstract-algebra.poly.factorization-/
theorem polynomial_exists_irreducible_factorization
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0) :
    ∃ factors : Multiset (Polynomial K),
      (∀ q ∈ factors, Irreducible q) ∧ Associated factors.prod p := by
  exact WfDvdMonoid.exists_factors p hp

/-- **不可约分解的相伴唯一性**：若两个不可约因子多重集的乘积相伴，则两组因子可逐项按相伴关系配对；`Multiset.Rel Associated` 同时忽略排列并记录单位倍数。
> **Entry**: abstract-algebra.poly.factorization-/
theorem polynomial_irreducible_factorization_unique
    {K : Type*} [Field K] {s t : Multiset (Polynomial K)}
    (hs : ∀ q ∈ s, Irreducible q) (ht : ∀ q ∈ t, Irreducible q)
    (hprod : Associated s.prod t.prod) :
    Multiset.Rel Associated s t := by
  exact UniqueFactorizationMonoid.factors_unique hs ht hprod

/-- **规范化因子分解公式**：任意多项式都等于首项系数对应的常数多项式乘以全部规范化
不可约因子的积。该等式采用 Mathlib 的 `normalizedFactors`，因而也统一处理零多项式。
> **Entry**: abstract-algebra.poly.factorization-/
theorem polynomial_eq_leadingCoeff_mul_normalizedFactors
    {K : Type*} [Field K] [DecidableEq K] (p : Polynomial K) :
    C p.leadingCoeff * (normalizedFactors p).prod = p := by
  exact Polynomial.leadingCoeff_mul_prod_normalizedFactors p

/-- **规范化因子的性质**：非零多项式的每个规范化因子既首一又不可约。首一条件选定了相伴类中的唯一代表，是从“相伴唯一”过渡到严格唯一的关键。
> **Entry**: abstract-algebra.poly.factorization-/
theorem normalizedFactor_monic_irreducible
    {K : Type*} [Field K] [DecidableEq K]
    {p q : Polynomial K} (hp : p ≠ 0) (hq : q ∈ normalizedFactors p) :
    q.Monic ∧ Irreducible q := by
  have h := (Polynomial.mem_normalizedFactors_iff hp).mp hq
  exact ⟨h.2.1, h.1⟩

/-- **首一不可约分解的严格唯一性**：两组首一且不可约的因子若乘积相等，则因子多重集本身相等。多重集等式已经吸收因子排列，而首一性消除了单位倍数的不确定性。
> **Entry**: abstract-algebra.poly.factorization-/
theorem monic_irreducible_factorization_unique
    {K : Type*} [Field K] {s t : Multiset (Polynomial K)}
    (hsM : ∀ q ∈ s, q.Monic) (htM : ∀ q ∈ t, q.Monic)
    (hsI : ∀ q ∈ s, Irreducible q) (htI : ∀ q ∈ t, Irreducible q)
    (hprod : s.prod = t.prod) : s = t := by
  classical
  have hsNorm : s.map normalize = s := by
    calc
      s.map normalize = s.map id :=
        Multiset.map_congr rfl (fun q hq => (hsM q hq).normalize_eq_self)
      _ = s := Multiset.map_id s
  have htNorm : t.map normalize = t := by
    calc
      t.map normalize = t.map id :=
        Multiset.map_congr rfl (fun q hq => (htM q hq).normalize_eq_self)
      _ = t := Multiset.map_id t
  have hsFactors := UniqueFactorizationMonoid.normalizedFactors_prod_eq s hsI
  have htFactors := UniqueFactorizationMonoid.normalizedFactors_prod_eq t htI
  rw [hsNorm] at hsFactors
  rw [htNorm] at htFactors
  calc
    s = normalizedFactors s.prod := hsFactors.symm
    _ = normalizedFactors t.prod := by rw [hprod]
    _ = t := htFactors

/-! ## 根重数的整除刻画 -/

/-- **正重数与根的等价性**：对非零多项式，元素 `a` 是根，当且仅当它的根重数严格为正。这把求值为零的语义与一次因子整除的语义连接起来。
> **Entry**: abstract-algebra.poly.factorization-/
theorem rootMultiplicity_pos_iff_isRoot
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0) {a : K} :
    0 < p.rootMultiplicity a ↔ p.IsRoot a := by
  exact Polynomial.rootMultiplicity_pos hp

/-- **重数的幂整除刻画**：对非零多项式，`(X - C a)^n` 整除 `p` 当且仅当 `n` 不超过 `a` 在 `p` 中的根重数。
> **Entry**: abstract-algebra.poly.factorization-/
theorem pow_X_sub_C_dvd_iff_le_rootMultiplicity
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0)
    {a : K} {n : ℕ} :
    (X - C a) ^ n ∣ p ↔ n ≤ p.rootMultiplicity a := by
  exact (Polynomial.le_rootMultiplicity_iff hp).symm

/-- **根重数恰等于给定自然数的判据**：重数等于 `n`，当且仅当 `n` 次幂整除而 `n+1` 次幂不整除。这是教材中“最高整除幂”的直接表述。
> **Entry**: abstract-algebra.poly.factorization-/
theorem rootMultiplicity_eq_iff
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0)
    {a : K} {n : ℕ} :
    p.rootMultiplicity a = n ↔
      (X - C a) ^ n ∣ p ∧ ¬(X - C a) ^ (n + 1) ∣ p := by
  constructor
  · intro h
    constructor
    · apply (Polynomial.le_rootMultiplicity_iff hp).mp
      omega
    · apply (Polynomial.rootMultiplicity_le_iff hp a n).mp
      omega
  · rintro ⟨hn, hsucc⟩
    have hnle : n ≤ p.rootMultiplicity a :=
      (Polynomial.le_rootMultiplicity_iff hp).mpr hn
    have hle : p.rootMultiplicity a ≤ n :=
      (Polynomial.rootMultiplicity_le_iff hp a n).mpr hsucc
    exact le_antisymm hle hnle

/-- **纯一次因子幂的根重数**：`(X - C a)^n` 在 `a` 处的根重数恰为 `n`，给出根重数定义的标准基准例。
> **Entry**: abstract-algebra.poly.factorization-/
theorem rootMultiplicity_X_sub_C_pow
    {K : Type*} [Field K] (a : K) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  exact Polynomial.rootMultiplicity_X_sub_C_pow a n

/-- **乘积的根重数可加性**：两个非零多项式乘积在 `a` 处的重数，等于两个因子各自重数之和。非零假设排除了零多项式的特殊约定。
> **Entry**: abstract-algebra.poly.factorization-/
theorem rootMultiplicity_mul
    {K : Type*} [Field K] {p q : Polynomial K} {a : K}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).rootMultiplicity a = p.rootMultiplicity a + q.rootMultiplicity a := by
  exact Polynomial.rootMultiplicity_mul (mul_ne_zero hp hq)

/-! ## 导数的基础公式 -/

/-- **形式导数的系数公式**：导数的第 `n` 个系数等于原多项式第 `n+1` 个系数乘以自然数 `n+1` 在系数域中的像。
> **Entry**: abstract-algebra.poly.factorization-/
theorem coefficient_derivative
    {K : Type*} [Field K] (p : Polynomial K) (n : ℕ) :
    p.derivative.coeff n = p.coeff (n + 1) * (n + 1 : K) := by
  exact Polynomial.coeff_derivative p n

/-- **形式导数的乘积法则**：多项式乘积的导数满足 Leibniz 公式 `(pq)' = p'q + pq'`，与经典微分法则完全一致。
> **Entry**: abstract-algebra.poly.factorization-/
theorem derivative_mul
    {K : Type*} [Field K] (p q : Polynomial K) :
    (p * q).derivative = p.derivative * q + p * q.derivative := by
  exact Polynomial.derivative_mul

/-! ## 单根、重根与导数判据 -/

/-- **单根**：若 `a` 是 `p` 的根且根重数恰为一，则称 `a` 为 `p` 的单根。此定义随后用于导数非零判据。
> **Entry**: abstract-algebra.poly.factorization-/
def SimpleRoot {K : Type*} [Field K] (p : Polynomial K) (a : K) : Prop :=
  p.IsRoot a ∧ p.rootMultiplicity a = 1

/-- **重根**：若 `a` 是 `p` 的根且根重数严格大于一，则称 `a` 为 `p` 的重根。
> **Entry**: abstract-algebra.poly.factorization-/
def RepeatedRoot {K : Type*} [Field K] (p : Polynomial K) (a : K) : Prop :=
  p.IsRoot a ∧ 1 < p.rootMultiplicity a

/-- **重数一与单根的等价性**：对非零多项式，根重数恰为一当且仅当满足本模块的 `SimpleRoot` 教材定义。
> **Entry**: abstract-algebra.poly.factorization-/
theorem rootMultiplicity_eq_one_iff
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0) {a : K} :
    p.rootMultiplicity a = 1 ↔ SimpleRoot p a := by
  constructor
  · intro h
    refine ⟨(Polynomial.rootMultiplicity_pos hp).mp ?_, h⟩
    omega
  · exact fun h => h.2

/-- **重数大于一的导数判据**：对非零多项式，`a` 的重数大于一，当且仅当 `a` 同时是原多项式及其形式导数的根。
> **Entry**: abstract-algebra.poly.factorization-/
theorem one_lt_rootMultiplicity_iff_isRoot_derivative
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0) {a : K} :
    1 < p.rootMultiplicity a ↔ p.IsRoot a ∧ p.derivative.IsRoot a := by
  exact Polynomial.one_lt_rootMultiplicity_iff_isRoot hp

/-- **单根的导数求值判据**：已知 `a` 是非零多项式 `p` 的根时，`a` 为单根当且仅当 `p'` 在 `a` 处的值非零。
> **Entry**: abstract-algebra.poly.factorization-/
theorem simpleRoot_iff_derivative_eval_ne_zero
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0)
    {a : K} (ha : p.IsRoot a) :
    SimpleRoot p a ↔ p.derivative.eval a ≠ 0 := by
  rw [SimpleRoot, and_iff_right ha, ne_eq, ← Polynomial.IsRoot.def]
  constructor
  · intro hm hder
    have hlt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨ha, hder⟩
    omega
  · intro hnot
    have hpos : 0 < p.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hp).mpr ha
    have hle : p.rootMultiplicity a ≤ 1 := by
      by_contra h
      have hlt : 1 < p.rootMultiplicity a := Nat.lt_of_not_ge h
      exact hnot ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mp hlt).2
    omega

/-- **重根的导数根判据**：已知 `a` 是非零多项式 `p` 的根时，`a` 为重根当且仅当它也是 `p'` 的根。
> **Entry**: abstract-algebra.poly.factorization-/
theorem repeatedRoot_iff_isRoot_derivative
    {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0)
    {a : K} (ha : p.IsRoot a) :
    RepeatedRoot p a ↔ p.derivative.IsRoot a := by
  rw [RepeatedRoot, and_iff_right ha,
    Polynomial.one_lt_rootMultiplicity_iff_isRoot hp, and_iff_right ha]

/-! ## 特征零下的导数重数 -/

/-- **特征零下导数使重数下降一**：若 `a` 是 `p` 的根，则形式导数在 `a` 处的根重数等于原重数减一；特征零假设防止指数系数消失。
> **Entry**: abstract-algebra.poly.factorization-/
theorem derivative_rootMultiplicity
    {K : Type*} [Field K] [CharZero K]
    {p : Polynomial K} {a : K} (ha : p.IsRoot a) :
    p.derivative.rootMultiplicity a = p.rootMultiplicity a - 1 := by
  exact Polynomial.derivative_rootMultiplicity_of_root ha

/-- **迭代导数刻画根重数**：在特征零域上，`n` 小于根重数，当且仅当前 `n` 阶以内的每个迭代导数都仍以 `a` 为根。
> **Entry**: abstract-algebra.poly.factorization-/
theorem lt_rootMultiplicity_iff_iteratedDerivative_isRoot
    {K : Type*} [Field K] [CharZero K]
    {p : Polynomial K} (hp : p ≠ 0) {a : K} {n : ℕ} :
    n < p.rootMultiplicity a ↔
      ∀ m ≤ n, ((Polynomial.derivative)^[m] p).IsRoot a := by
  exact Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hp

/-- **根多重集中的计数等于根重数**：在给定系数域可判定相等时，`p.roots` 中 `a` 的出现次数恰为 `p.rootMultiplicity a`。
> **Entry**: abstract-algebra.poly.factorization-/
theorem roots_count_eq_rootMultiplicity
    {K : Type*} [Field K] [DecidableEq K] (p : Polynomial K) (a : K) :
    p.roots.count a = p.rootMultiplicity a := by
  exact Polynomial.count_roots p

end SandronesLibrary.AbstractAlgebra.PolynomialFactorization
