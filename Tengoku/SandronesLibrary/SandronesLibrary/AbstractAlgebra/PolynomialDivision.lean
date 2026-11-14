/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.PolynomialDefinition
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.RingEuclidean
import Tengoku.Seed.Algebra.Polynomial.FieldDivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/PolynomialDivision.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 抽象代数 / 多项式带余除法与 Euclidean 算法

本模块先在 Mathlib 的正式承载 `Polynomial R` 上建立可直接复用的多项式带余除法接口，随后
保留本库有限支撑系数序列 `PolynomialSequence R` 的兼容版本。两部分首先处理交换环上的首一
除式：正式承载使用 `Polynomial.Monic`、`divByMonic` 与 `modByMonic`，兼容承载则使用逐系数
`Monic` 及其具名桥。之后把系数环加强为域，为任意非零除式给出商余恒等式，并采用诚实处理零
多项式的自然数度量构造本库 `EuclideanDomainAxioms`。最后直接调用 A2 已证明的 Euclidean
算法，得到多项式最大公因数的泛性质和 Bézout 恒等式。

Mathlib 的 `Polynomial.Monic`、`divByMonic`、`modByMonic`、域上 `/` 与 `%` 是经过教材解释的
正式公开承载，而不是静默证明后端；其类型类假设在每条定理中显式给出。旧
`PolynomialSequence` 接口继续使用具名桥。两条路线共同调用本库 `GreatestCommonDivisor` 与
`EuclideanDomainAxioms`，公开签名不泄漏模、子模或代数扩张结构。

> **Entry**: abstract-algebra.poly.division
-/

namespace SandronesLibrary.AbstractAlgebra.PolynomialDivision

open SandronesLibrary.AbstractAlgebra.Ring
open SandronesLibrary.AbstractAlgebra.PolynomialDefinition


/-! ### Mathlib `Polynomial` 正式承载接口 -/

/-- **正式承载上的首一除法恒等式**：对交换环上的 Mathlib 多项式 `p,d`，若除式 `d`
首一，则 `p` 等于 `d` 乘以首一商，再加首一余数。该接口直接使用成熟的
`divByMonic` 与 `modByMonic` 运算，供仍以 `Polynomial R` 为承载的下游代码复用。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlib_monic_division_identity {R : Type*} [CommRing R]
    (p d : Polynomial R) (_hd : d.Monic) :
    p = d * p.divByMonic d + p.modByMonic d := by
  rw [add_comm, Polynomial.modByMonic_add_div]

/-- **正式承载上的首一余数次数界**：在非平凡交换环上，以首一多项式 `d` 除 `p`，
所得 `modByMonic` 余数的次数严格小于 `d` 的次数；零余数的次数 `⊥` 也包含在结论中。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlib_monic_remainder_degree_lt {R : Type*} [CommRing R] [Nontrivial R]
    (p d : Polynomial R) (hd : d.Monic) :
    (p.modByMonic d).degree < d.degree := by
  exact Polynomial.degree_modByMonic_lt p hd

/-- **正式承载上的首一整除判据**：对首一除式 `d`，`p` 的首一余数为零，当且仅当
`d` 整除 `p`。这是余数计算与环论整除关系之间的标准接口。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlib_monic_remainder_eq_zero_iff_dvd {R : Type*} [CommRing R]
    (p d : Polynomial R) (hd : d.Monic) :
    p.modByMonic d = 0 ↔ d ∣ p := by
  exact Polynomial.modByMonic_eq_zero_iff_dvd hd

/-- **正式承载上的首一商余唯一性**：若 `p = d*q+r`，`d` 首一且 `r` 的次数严格小于
`d` 的次数，则候选商 `q` 和余数 `r` 分别等于 `divByMonic` 与 `modByMonic` 给出的结果。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlib_monic_quotient_remainder_unique
    {R : Type*} [CommRing R] [Nontrivial R]
    (p d q r : Polynomial R) (hd : d.Monic)
    (hidentity : p = d * q + r) (hdegree : r.degree < d.degree) :
    q = p.divByMonic d ∧ r = p.modByMonic d := by
  have hidentity' : r + d * q = p := by
    rw [hidentity, add_comm]
  have hu := Polynomial.div_modByMonic_unique q r hd ⟨hidentity', hdegree⟩
  exact ⟨hu.1.symm, hu.2.symm⟩

/-- **正式承载上的零安全 Euclidean 度量**：零多项式的次数为 `⊥`，故度量取 `0`；
非零 `n` 次多项式的度量取 `n+1`。加一保证每个非零多项式的度量严格为正。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def mathlibPolynomialDegreeMeasure {K : Type*} [Field K]
    (p : Polynomial K) : ℕ :=
  match p.degree with
  | ⊥ => 0
  | (n : ℕ) => n + 1

private theorem mathlibPolynomialDegreeMeasure_lt_of_degree_lt
    {K : Type*} [Field K] {r d : Polynomial K} (hdegree : r.degree < d.degree) :
    mathlibPolynomialDegreeMeasure r < mathlibPolynomialDegreeMeasure d := by
  cases hr : r.degree with
  | bot =>
      cases hd : d.degree with
      | bot => simp [hr, hd] at hdegree
      | coe n => simp [mathlibPolynomialDegreeMeasure, hr, hd]
  | coe m =>
      cases hd : d.degree with
      | bot => simp [hr, hd] at hdegree
      | coe n =>
          have hmn : m < n := by simpa [hr, hd] using hdegree
          simp only [mathlibPolynomialDegreeMeasure, hr, hd]
          omega

/-- **正式承载上的域多项式除法恒等式**：域上每个非零多项式 `d` 都可作为除式，且
`p = d * (p / d) + p % d`。商和余数直接采用 Mathlib 多项式 EuclideanDomain 运算。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlib_polynomial_division_identity {K : Type*} [Field K]
    (p d : Polynomial K) (_hd : d ≠ 0) :
    p = d * (p / d) + p % d := by
  rw [add_comm, EuclideanDomain.mod_add_div]

/-- **正式承载上的余数度量下降**：域上以非零 `d` 除 `p` 时，余数 `p % d` 的
零安全自然数度量严格小于 `d` 的度量，为本库 Euclidean 递归提供终止依据。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlib_polynomial_remainder_measure_lt {K : Type*} [Field K]
    (p d : Polynomial K) (hd : d ≠ 0) :
    mathlibPolynomialDegreeMeasure (p % d) < mathlibPolynomialDegreeMeasure d := by
  apply mathlibPolynomialDegreeMeasure_lt_of_degree_lt
  exact Polynomial.degree_mod_lt p hd

/-- **正式承载上的 Euclidean 环公理**：对域 `K`，以零安全次数为度量、`/` 为商、`%`
为余数，把 `Polynomial K` 组装成本库普通数据结构 `EuclideanDomainAxioms`；不额外注册实例。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def mathlibPolynomialEuclideanDomainAxioms
    (K : Type*) [Field K] : EuclideanDomainAxioms (Polynomial K) := by
  exact {
    domain := (integralDomainAxioms_iff_isDomain (R := Polynomial K)).2 inferInstance
    measure := mathlibPolynomialDegreeMeasure
    quotient := fun a b => a / b
    remainder := fun a b => a % b
    divisionWithRemainder := by
      intro a b hb
      exact ⟨mathlib_polynomial_division_identity a b hb,
        mathlib_polynomial_remainder_measure_lt a b hb⟩ }

/-- **正式承载上的最大公因数泛性质**：本库 Euclidean 算法作用于 `Polynomial K` 后得到的
`euclideanGCD` 同时整除 `a,b`，并被 `a,b` 的每个公因子整除。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlibPolynomialGCD_isGreatestCommonDivisor {K : Type*} [Field K]
    (a b : Polynomial K) :
    GreatestCommonDivisor
      (euclideanGCD (mathlibPolynomialEuclideanDomainAxioms K) a b) a b := by
  exact euclideanGCD_isGreatestCommonDivisor
    (mathlibPolynomialEuclideanDomainAxioms K) a b

/-- **正式承载上的 Bézout 恒等式**：对域上的任意 Mathlib 多项式 `a,b`，存在多项式
`s,t`，使 Euclidean 算法所得 gcd 等于 `s*a+t*b`。
> **Entry**: abstract-algebra.poly.division-/
theorem mathlibPolynomialGCD_bezout {K : Type*} [Field K]
    (a b : Polynomial K) :
    ∃ s t : Polynomial K,
      euclideanGCD (mathlibPolynomialEuclideanDomainAxioms K) a b = s * a + t * b := by
  exact euclideanDomain_bezout_for_gcd
    (mathlibPolynomialEuclideanDomainAxioms K) a b

/-! ### 本库 `PolynomialSequence` 教材接口 -/

/-- **首一多项式的本库定义**：存在指标 `n`，使第 `n` 项系数等于一，且所有严格高于
`n` 的系数都为零。这个定义直接读取本库系数序列，不依赖外部首项系数谓词；在零环中也按
系数等式本身解释，不暗中加入非平凡性假设。
> **Entry**: abstract-algebra.poly.division-/
def Monic {R : Type*} [CommRing R] (p : PolynomialSequence R) : Prop :=
  ∃ n : ℕ, coefficient p n = 1 ∧ ∀ m : ℕ, n < m → coefficient p m = 0

/-- 本库逐系数首一定义与具名 Mathlib 多项式桥后的首一谓词等价。证明分别处理零环和非平凡环；
该定理是明确的兼容边界，后续公开除法定理仍以本库 `Monic` 为前提。
> **Entry**: abstract-algebra.poly.division-/
theorem monic_iff_mathlib_monic {R : Type*} [CommRing R]
    (p : PolynomialSequence R) :
    Monic p ↔ (toMathlibPolynomial p).Monic := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      letI : Subsingleton R := hR
      constructor
      · intro _
        rw [Polynomial.Monic.def]
        exact Subsingleton.elim _ _
      · intro _
        exact ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  | inr hR =>
      letI : Nontrivial R := hR
      constructor
      · rintro ⟨n, hn, habove⟩
        have hcn : coefficient p n ≠ 0 := by
          rw [hn]
          exact one_ne_zero
        have hd : degree p = (n : WithBot ℕ) :=
          (degree_eq_nat_iff p n).2 ⟨hcn, habove⟩
        have hdm : (toMathlibPolynomial p).degree = (n : WithBot ℕ) := by
          simpa only [← degree_eq_mathlib_degree] using hd
        have hnat : (toMathlibPolynomial p).natDegree = n :=
          Polynomial.natDegree_eq_of_degree_eq_some hdm
        rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hnat,
          coefficient_toMathlibPolynomial]
        exact hn
      · intro hp
        refine ⟨(toMathlibPolynomial p).natDegree, ?_, ?_⟩
        · rw [← coefficient_toMathlibPolynomial, Polynomial.coeff_natDegree,
            hp.leadingCoeff]
        · intro m hm
          rw [← coefficient_toMathlibPolynomial]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt hm

/-- **首一除法的商**：把本库多项式 `p,d` 经具名桥转换到实现层，执行首一除法，再返回本库
有限支撑系数序列。定义本身对所有 `p,d` 有值；标准数学性质由后续 `Monic d` 前提保证。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def monicQuotient {R : Type*} [CommRing R]
    (p d : PolynomialSequence R) : PolynomialSequence R :=
  fromMathlibPolynomial (toMathlibPolynomial p |>.divByMonic (toMathlibPolynomial d))

/-- **首一除法的余数**：与 `monicQuotient` 配套，把实现层首一余数重新读取为本库多项式。
它将在首一除式下满足严格次数界，并由此给出商和余数的唯一性。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def monicRemainder {R : Type*} [CommRing R]
    (p d : PolynomialSequence R) : PolynomialSequence R :=
  fromMathlibPolynomial (toMathlibPolynomial p |>.modByMonic (toMathlibPolynomial d))

/-- **首一商的承载一致性桥**：把本库 `monicQuotient p d` 转到 Mathlib 正式多项式承载后，
恰好得到 `toMathlibPolynomial p` 除以 `toMathlibPolynomial d` 的 `divByMonic` 首一商。
该桥对任意交换环及任意除式成立；首一性只在商的数学性质中需要。
> **Entry**: abstract-algebra.poly.division-/
theorem toMathlibPolynomial_monicQuotient {R : Type*} [CommRing R]
    (p d : PolynomialSequence R) :
    toMathlibPolynomial (monicQuotient p d) =
      (toMathlibPolynomial p).divByMonic (toMathlibPolynomial d) := by
  exact toMathlibPolynomial_fromMathlibPolynomial _

/-- **首一余数的承载一致性桥**：把本库 `monicRemainder p d` 转到 Mathlib 正式承载后，
恰好得到对应两多项式的 `modByMonic` 首一余数。该等式直接记录双向承载转换互为逆映射。
> **Entry**: abstract-algebra.poly.division-/
theorem toMathlibPolynomial_monicRemainder {R : Type*} [CommRing R]
    (p d : PolynomialSequence R) :
    toMathlibPolynomial (monicRemainder p d) =
      (toMathlibPolynomial p).modByMonic (toMathlibPolynomial d) := by
  exact toMathlibPolynomial_fromMathlibPolynomial _

/-- **首一带余除法恒等式**：若 `d` 首一，则被除式等于除式乘商再加余数，
`p = d * monicQuotient p d + monicRemainder p d`。
> **Entry**: abstract-algebra.poly.division-/
theorem monic_division_identity {R : Type*} [CommRing R]
    (p d : PolynomialSequence R) (_hd : Monic d) :
    p = d * monicQuotient p d + monicRemainder p d := by
  apply toMathlib_injective
  rw [toMathlib_add, toMathlib_mul]
  simp only [monicQuotient, monicRemainder,
    toMathlibPolynomial_fromMathlibPolynomial]
  rw [add_comm, Polynomial.modByMonic_add_div]

/-- **首一余数的次数界**：在非平凡交换环上，以首一多项式 `d` 作除式所得余数次数严格小于
`d` 的次数。次数取值于 `WithBot ℕ`，所以零余数的次数 `⊥` 也被诚实包含在结论中。
> **Entry**: abstract-algebra.poly.division-/
theorem monic_remainder_degree_lt {R : Type*} [CommRing R] [Nontrivial R]
    (p d : PolynomialSequence R) (hd : Monic d) :
    degree (monicRemainder p d) < degree d := by
  rw [degree_eq_mathlib_degree, degree_eq_mathlib_degree]
  simp only [monicRemainder, toMathlibPolynomial_fromMathlibPolynomial]
  exact Polynomial.degree_modByMonic_lt _ ((monic_iff_mathlib_monic d).1 hd)

/-- **余数为零的整除判据**：对首一除式 `d`，`p` 除以 `d` 的余数为零，当且仅当按本库
显式乘子定义的 `DividesElement d p` 成立。结论不以 Lean 的整除记号作为公开接口。
> **Entry**: abstract-algebra.poly.division-/
theorem monic_remainder_eq_zero_iff_dividesElement {R : Type*} [CommRing R]
    (p d : PolynomialSequence R) (hd : Monic d) :
    monicRemainder p d = 0 ↔ DividesElement d p := by
  rw [← toMathlib_injective.eq_iff, toMathlib_zero]
  simp only [monicRemainder, toMathlibPolynomial_fromMathlibPolynomial]
  rw [Polynomial.modByMonic_eq_zero_iff_dvd ((monic_iff_mathlib_monic d).1 hd)]
  exact (dividesElement_iff_dvd).symm.trans (by
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨fromMathlibPolynomial q, ?_⟩
      apply toMathlib_injective
      rw [toMathlib_mul, toMathlibPolynomial_fromMathlibPolynomial]
      exact hq
    · rintro ⟨q, hq⟩
      exact ⟨toMathlibPolynomial q, by
        rw [← toMathlib_mul]
        exact congrArg toMathlibPolynomial hq⟩)

/-- **首一带余除法的唯一性**：若 `q,r` 已满足 `p = d*q+r`，且 `r` 的次数严格小于首一除式
`d` 的次数，则 `q,r` 必分别等于本模块定义的 `monicQuotient` 与 `monicRemainder`。
> **Entry**: abstract-algebra.poly.division-/
theorem monic_quotient_remainder_unique {R : Type*} [CommRing R] [Nontrivial R]
    (p d q r : PolynomialSequence R) (hd : Monic d)
    (hidentity : p = d * q + r) (hdegree : degree r < degree d) :
    q = monicQuotient p d ∧ r = monicRemainder p d := by
  have hmathIdentity :
      toMathlibPolynomial r + toMathlibPolynomial d * toMathlibPolynomial q =
        toMathlibPolynomial p := by
    calc
      toMathlibPolynomial r + toMathlibPolynomial d * toMathlibPolynomial q =
          toMathlibPolynomial (r + d * q) := by
            rw [toMathlib_add, toMathlib_mul]
      _ = toMathlibPolynomial p := by rw [add_comm, ← hidentity]
  have hmathDegree :
      (toMathlibPolynomial r).degree < (toMathlibPolynomial d).degree := by
    simpa only [← degree_eq_mathlib_degree] using hdegree
  have hu := Polynomial.div_modByMonic_unique
    (toMathlibPolynomial q) (toMathlibPolynomial r)
    ((monic_iff_mathlib_monic d).1 hd) ⟨hmathIdentity, hmathDegree⟩
  constructor
  · apply toMathlib_injective
    simpa only [monicQuotient, toMathlibPolynomial_fromMathlibPolynomial] using hu.1.symm
  · apply toMathlib_injective
    simpa only [monicRemainder, toMathlibPolynomial_fromMathlibPolynomial] using hu.2.symm

/-- **域上任意多项式除法的商**：域中每个非零首项系数都可逆，因此不再要求除式首一。
该定义对零除式也给出实现层约定的总函数值；带余除法公理只在除式非零时使用它。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def polynomialQuotient {K : Type*} [Field K]
    (p d : PolynomialSequence K) : PolynomialSequence K :=
  fromMathlibPolynomial (toMathlibPolynomial p / toMathlibPolynomial d)

/-- **域上任意多项式除法的余数**：与 `polynomialQuotient` 配套，把域上通常的多项式余数
返回为本库 `PolynomialSequence K`。非零除式下它具有严格较小的次数。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def polynomialRemainder {K : Type*} [Field K]
    (p d : PolynomialSequence K) : PolynomialSequence K :=
  fromMathlibPolynomial (toMathlibPolynomial p % toMathlibPolynomial d)

/-- **域上多项式商的承载一致性桥**：本库 `polynomialQuotient p d` 经具名桥转换后，
等于 Mathlib 正式承载上的商 `toMathlibPolynomial p / toMathlibPolynomial d`。
该桥包括 Mathlib 对零除式采用的总函数约定，不额外要求 `d ≠ 0`。
> **Entry**: abstract-algebra.poly.division-/
theorem toMathlibPolynomial_polynomialQuotient {K : Type*} [Field K]
    (p d : PolynomialSequence K) :
    toMathlibPolynomial (polynomialQuotient p d) =
      toMathlibPolynomial p / toMathlibPolynomial d := by
  exact toMathlibPolynomial_fromMathlibPolynomial _

/-- **域上多项式余数的承载一致性桥**：本库 `polynomialRemainder p d` 经具名桥转换后，
等于 Mathlib 正式承载上的余数 `toMathlibPolynomial p % toMathlibPolynomial d`。
它使两套除法接口的余数定理可以直接互相搬运。
> **Entry**: abstract-algebra.poly.division-/
theorem toMathlibPolynomial_polynomialRemainder {K : Type*} [Field K]
    (p d : PolynomialSequence K) :
    toMathlibPolynomial (polynomialRemainder p d) =
      toMathlibPolynomial p % toMathlibPolynomial d := by
  exact toMathlibPolynomial_fromMathlibPolynomial _

/-- **多项式 Euclidean 度量**：零多项式次数为 `⊥`，度量定义为 `0`；非零多项式次数为
自然数 `n` 时，度量定义为 `n+1`。加一使每个非零多项式的度量严格为正，从而不会把常数
多项式与零多项式混为同一终止层级。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def polynomialDegreeMeasure {K : Type*} [Field K]
    (p : PolynomialSequence K) : ℕ :=
  match degree p with
  | ⊥ => 0
  | (n : ℕ) => n + 1

/-- **零安全次数度量的承载一致性桥**：本库系数序列 `p` 的 `polynomialDegreeMeasure`
等于其 Mathlib 正式承载的 `mathlibPolynomialDegreeMeasure`。两侧都把零多项式映为 `0`，
把非零 `n` 次多项式映为 `n+1`，一致性仅依赖现有次数桥。
> **Entry**: abstract-algebra.poly.division-/
theorem polynomialDegreeMeasure_eq_mathlibPolynomialDegreeMeasure
    {K : Type*} [Field K] (p : PolynomialSequence K) :
    polynomialDegreeMeasure p =
      mathlibPolynomialDegreeMeasure (toMathlibPolynomial p) := by
  rw [polynomialDegreeMeasure, mathlibPolynomialDegreeMeasure,
    degree_eq_mathlib_degree]

private theorem polynomialDegreeMeasure_lt_of_degree_lt {K : Type*} [Field K]
    {r d : PolynomialSequence K} (hdegree : degree r < degree d) :
    polynomialDegreeMeasure r < polynomialDegreeMeasure d := by
  cases hr : degree r with
  | bot =>
      cases hd : degree d with
      | bot => simp [hr, hd] at hdegree
      | coe n => simp [polynomialDegreeMeasure, hr, hd]
  | coe m =>
      cases hd : degree d with
      | bot => simp [hr, hd] at hdegree
      | coe n =>
          have hmn : m < n := by simpa [hr, hd] using hdegree
          simp only [polynomialDegreeMeasure, hr, hd]
          omega

/-- **域上多项式带余除法恒等式**：若 `d ≠ 0`，则任意 `p` 都分解为
`p = d * polynomialQuotient p d + polynomialRemainder p d`。
> **Entry**: abstract-algebra.poly.division-/
theorem polynomial_division_identity {K : Type*} [Field K]
    (p d : PolynomialSequence K) (_hd : d ≠ 0) :
    p = d * polynomialQuotient p d + polynomialRemainder p d := by
  apply toMathlib_injective
  rw [toMathlib_add, toMathlib_mul]
  simp only [polynomialQuotient, polynomialRemainder,
    toMathlibPolynomial_fromMathlibPolynomial]
  rw [add_comm, EuclideanDomain.mod_add_div]

/-- **余数度量严格下降**：非零除式 `d` 下，余数的零安全自然数度量严格小于 `d` 的度量。
这是把通常的严格次数界转写为本库 Euclidean 算法递归所需的自然数终止条件。
> **Entry**: abstract-algebra.poly.division-/
theorem polynomial_remainder_measure_lt {K : Type*} [Field K]
    (p d : PolynomialSequence K) (hd : d ≠ 0) :
    polynomialDegreeMeasure (polynomialRemainder p d) < polynomialDegreeMeasure d := by
  apply polynomialDegreeMeasure_lt_of_degree_lt
  rw [degree_eq_mathlib_degree, degree_eq_mathlib_degree]
  simp only [polynomialRemainder, toMathlibPolynomial_fromMathlibPolynomial]
  apply Polynomial.degree_mod_lt
  intro hzero
  apply hd
  apply toMathlib_injective
  rw [hzero, toMathlib_zero]

/-- **域上本库多项式的 Euclidean 环公理**：整环部分来自本库多项式整环定理，度量采用
`polynomialDegreeMeasure`，商与余数采用本模块定义；除法恒等式和严格下降共同组成
`DivisionWithRemainder`。这里构造的是本库普通数据结构，不注册或暴露 Mathlib
`EuclideanDomain` 类型类。
> **Entry**: abstract-algebra.poly.division-/
noncomputable def polynomialEuclideanDomainAxioms (K : Type*) [Field K] :
    EuclideanDomainAxioms (PolynomialSequence K) where
  domain := polynomial_integralDomainAxioms
    ((integralDomainAxioms_iff_isDomain (R := K)).2 inferInstance)
  measure := polynomialDegreeMeasure
  quotient := polynomialQuotient
  remainder := polynomialRemainder
  divisionWithRemainder := by
    intro a b hb
    exact ⟨polynomial_division_identity a b hb,
      polynomial_remainder_measure_lt a b hb⟩

/-- **多项式 Euclidean 最大公因数的泛性质**：由本库 Euclidean 算法得到的多项式
`euclideanGCD` 同时整除 `a,b`，并被 `a,b` 的每个公因子整除，即满足本库
`GreatestCommonDivisor` 定义。
> **Entry**: abstract-algebra.poly.division-/
theorem polynomialGCD_isGreatestCommonDivisor {K : Type*} [Field K]
    (a b : PolynomialSequence K) :
    GreatestCommonDivisor
      (euclideanGCD (polynomialEuclideanDomainAxioms K) a b) a b := by
  exact euclideanGCD_isGreatestCommonDivisor (polynomialEuclideanDomainAxioms K) a b

/-- **多项式 gcd 的 Bézout 恒等式**：域上任意本库多项式 `a,b` 存在本库多项式系数
`s,t`，使 Euclidean 算法给出的 gcd 等于 `s*a+t*b`。该结论直接复用环论层扩展 Euclidean
算法，不引入模或理想作为公开对象。
> **Entry**: abstract-algebra.poly.division-/
theorem polynomialGCD_bezout {K : Type*} [Field K]
    (a b : PolynomialSequence K) :
    ∃ s t : PolynomialSequence K,
      euclideanGCD (polynomialEuclideanDomainAxioms K) a b = s * a + t * b := by
  exact euclideanDomain_bezout_for_gcd (polynomialEuclideanDomainAxioms K) a b

end SandronesLibrary.AbstractAlgebra.PolynomialDivision
