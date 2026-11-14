/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.RingDivisibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/PolynomialDefinition.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 抽象代数 / 有限支撑系数序列兼容承载

本模块从教材定义出发，把多项式实现为自然数指标、非零项有限的系数序列，并完整证明它与
Mathlib `Polynomial R` 双向互逆。按照课程承载维护方案，后续多项式课程正式采用语义一致且成熟的
`Polynomial R`；公开对象 `PolynomialSequence R` 作为已有代码的兼容承载继续保留，不做破坏式
删除。系数、环运算、常数多项式、不定元、次数、求值、根与整除性的旧接口仍可稳定使用。

`toMathlibPolynomial` 与 `fromMathlibPolynomial` 是旧兼容承载到正式承载的迁移路径；其互逆、
系数和运算保持定理说明两种表示没有数学语义差异。`Finsupp` 仍只属于实现细节。新章节应直接
量化 `Polynomial R`，旧下游则可继续依赖 `PolynomialSequence`、`RingHomomorphism`、
`IntegralDomainAxioms` 和 `DividesElement`。

> **Entry**: abstract-algebra.poly.def
-/

namespace SandronesLibrary.AbstractAlgebra.PolynomialDefinition

open SandronesLibrary.AbstractAlgebra.Ring


/-- **旧兼容多项式表示**：由系数函数 `ℕ → R` 及其非零位置集合有限的证明组成。
> **Entry**: abstract-algebra.poly.def-/
structure PolynomialSequence (R : Type*) [Zero R] where
  coefficients : ℕ → R
  finiteSupport : {n | coefficients n ≠ 0}.Finite

/-- `coefficient p n` 是本库多项式 `p` 的 `X^n` 项系数。
> **Entry**: abstract-algebra.poly.def-/
def coefficient {R : Type*} [Zero R] (p : PolynomialSequence R) (n : ℕ) : R :=
  p.coefficients n

/-- **系数支撑**：本库多项式所有非零系数指标组成的有限集。
> **Entry**: abstract-algebra.poly.def-/
noncomputable def coefficientSupport {R : Type*} [Zero R]
    (p : PolynomialSequence R) : Finset ℕ :=
  p.finiteSupport.toFinset

/-- 指标属于系数支撑，当且仅当该项系数非零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=iff.0h3v.s5.522caf63ed70 from=translated src=- shape=d82f7599 vocab=e5ef8549
-/
theorem mem_coefficientSupport_iff {R : Type*} [Zero R]
    (p : PolynomialSequence R) (n : ℕ) :
    n ∈ coefficientSupport p ↔ coefficient p n ≠ 0 := by
  simp [coefficientSupport, coefficient]

/-- **多项式外延性**：每一项系数都相同的两个本库多项式相等。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.1h3v.s5.b491e10b4eec from=translated src=- shape=48e4affc vocab=e9a8ded5
-/
@[ext] theorem ext {R : Type*} [Zero R] {p q : PolynomialSequence R}
    (h : ∀ n, coefficient p n = coefficient q n) : p = q := by
  cases p with
  | mk pc pf =>
    cases q with
    | mk qc qf =>
      simp only [coefficient] at h
      have : pc = qc := funext h
      subst qc
      rfl

private noncomputable def coefficientFinsupp {R : Type*} [Zero R]
    (p : PolynomialSequence R) : ℕ →₀ R :=
  Finsupp.onFinset p.finiteSupport.toFinset p.coefficients (by
    intro n hn
    simpa using hn)

/-- **到 Mathlib 的具名桥**：把本库有限支撑系数序列转换为 Mathlib `Polynomial`。
这是旧表示迁移到正式 `Polynomial` 承载的兼容边界，不是新的课程多项式定义。
> **Entry**: abstract-algebra.poly.def-/
noncomputable def toMathlibPolynomial {R : Type*} [Semiring R]
    (p : PolynomialSequence R) : Polynomial R :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (coefficientFinsupp p))

/-- **从 Mathlib 返回本库的具名桥**：读取 Mathlib 多项式的系数与有限支撑证明。
> **Entry**: abstract-algebra.poly.def-/
def fromMathlibPolynomial {R : Type*} [Semiring R]
    (p : Polynomial R) : PolynomialSequence R where
  coefficients := p.coeff
  finiteSupport := by
    refine p.support.finite_toSet.subset ?_
    intro n hn
    exact Polynomial.mem_support_iff.mpr hn

/-- 到 Mathlib 的具名桥保持每一项系数。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s5.a8563f3be708 from=translated src=- shape=04a2bb94 vocab=686616d3
-/
theorem coefficient_toMathlibPolynomial {R : Type*} [Semiring R]
    (p : PolynomialSequence R) (n : ℕ) :
    (toMathlibPolynomial p).coeff n = coefficient p n := by
  simp [toMathlibPolynomial, coefficientFinsupp, coefficient]

/-- 从 Mathlib 返回本库的具名桥保持每一项系数。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s4.2541e3e67157 from=translated src=- shape=04a2bb94 vocab=a069842a
-/
theorem coefficient_fromMathlibPolynomial {R : Type*} [Semiring R]
    (p : Polynomial R) (n : ℕ) :
    coefficient (fromMathlibPolynomial p) n = p.coeff n := by
  rfl

/-- 本库系数支撑经过具名桥后，正好等于 Mathlib 多项式的支撑。这是实现桥，不是教材定义。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s4.c1489e191126 from=translated src=- shape=759d10b6 vocab=ff28e8f7
-/
theorem coefficientSupport_eq_mathlib_support {R : Type*} [Semiring R]
    (p : PolynomialSequence R) :
    coefficientSupport p = (toMathlibPolynomial p).support := by
  ext n
  rw [mem_coefficientSupport_iff, Polynomial.mem_support_iff,
    coefficient_toMathlibPolynomial]

/-- 两个具名桥在“Mathlib → 本库 → Mathlib”方向互为逆映射。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s4.4b406819b6f0 from=translated src=- shape=2896fe98 vocab=5e8c2bf6
-/
theorem toMathlibPolynomial_fromMathlibPolynomial {R : Type*} [Semiring R]
    (p : Polynomial R) :
    toMathlibPolynomial (fromMathlibPolynomial p) = p := by
  ext n
  rw [coefficient_toMathlibPolynomial, coefficient_fromMathlibPolynomial]

/-- 两个具名桥在“本库 → Mathlib → 本库”方向互为逆映射。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s4.f284150308de from=translated src=- shape=2896fe98 vocab=cecbf1ee
-/
theorem fromMathlibPolynomial_toMathlibPolynomial {R : Type*} [Semiring R]
    (p : PolynomialSequence R) :
    fromMathlibPolynomial (toMathlibPolynomial p) = p := by
  ext n
  rw [coefficient_fromMathlibPolynomial, coefficient_toMathlibPolynomial]

private noncomputable def transportedZero {R : Type*} [Semiring R] :
    PolynomialSequence R := fromMathlibPolynomial 0
private noncomputable def transportedOne {R : Type*} [Semiring R] :
    PolynomialSequence R := fromMathlibPolynomial 1
private noncomputable def transportedAdd {R : Type*} [Semiring R]
    (p q : PolynomialSequence R) : PolynomialSequence R :=
  fromMathlibPolynomial (toMathlibPolynomial p + toMathlibPolynomial q)
private noncomputable def transportedMul {R : Type*} [Semiring R]
    (p q : PolynomialSequence R) : PolynomialSequence R :=
  fromMathlibPolynomial (toMathlibPolynomial p * toMathlibPolynomial q)
private noncomputable def transportedNeg {R : Type*} [Ring R]
    (p : PolynomialSequence R) : PolynomialSequence R :=
  fromMathlibPolynomial (-toMathlibPolynomial p)

/-- 本库多项式的零元实例；运算由私有有限支撑实现传输。
> **Entry**: abstract-algebra.poly.def-/
noncomputable instance {R : Type*} [Semiring R] : Zero (PolynomialSequence R) :=
  ⟨transportedZero⟩
/-- 本库多项式的乘法单位元实例。
> **Entry**: abstract-algebra.poly.def-/
noncomputable instance {R : Type*} [Semiring R] : One (PolynomialSequence R) :=
  ⟨transportedOne⟩
/-- 本库多项式的逐系数加法实例。
> **Entry**: abstract-algebra.poly.def-/
noncomputable instance {R : Type*} [Semiring R] : Add (PolynomialSequence R) :=
  ⟨transportedAdd⟩
/-- 本库多项式的卷积乘法实例。
> **Entry**: abstract-algebra.poly.def-/
noncomputable instance {R : Type*} [Semiring R] : Mul (PolynomialSequence R) :=
  ⟨transportedMul⟩
/-- 本库多项式的逐系数取负实例。
> **Entry**: abstract-algebra.poly.def-/
noncomputable instance {R : Type*} [Ring R] : Neg (PolynomialSequence R) :=
  ⟨transportedNeg⟩

/-- 具名桥保持零多项式。该基础搬运性质公开供后续章节复用，避免重复证明。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h1v.s5.959114c1412c from=translated src=- shape=7b5bff60 vocab=9484c804
-/
theorem toMathlib_zero {R : Type*} [Semiring R] :
    toMathlibPolynomial (0 : PolynomialSequence R) = 0 := by
  exact toMathlibPolynomial_fromMathlibPolynomial 0
/-- 具名桥保持乘法单位元。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h1v.s5.b3baefc20672 from=translated src=- shape=7b5bff60 vocab=9484c804
-/
theorem toMathlib_one {R : Type*} [Semiring R] :
    toMathlibPolynomial (1 : PolynomialSequence R) = 1 := by
  exact toMathlibPolynomial_fromMathlibPolynomial 1
/-- 具名桥保持多项式加法，是后续章节共享的证明搬运接口。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s6.b412f59786ee from=translated src=- shape=e69ef69b vocab=739f8ea3
-/
theorem toMathlib_add {R : Type*} [Semiring R] (p q : PolynomialSequence R) :
    toMathlibPolynomial (p + q) = toMathlibPolynomial p + toMathlibPolynomial q := by
  exact toMathlibPolynomial_fromMathlibPolynomial _
/-- 具名桥保持多项式乘法，是整除、除法与因式分解章节共享的证明搬运接口。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s6.0db9593f2561 from=translated src=- shape=e69ef69b vocab=b5ad4903
-/
theorem toMathlib_mul {R : Type*} [Semiring R] (p q : PolynomialSequence R) :
    toMathlibPolynomial (p * q) = toMathlibPolynomial p * toMathlibPolynomial q := by
  exact toMathlibPolynomial_fromMathlibPolynomial _
/-- 具名桥保持多项式取负。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s5.7aa93edce647 from=translated src=- shape=5c68212b vocab=4bbe2427
-/
theorem toMathlib_neg {R : Type*} [Ring R] (p : PolynomialSequence R) :
    toMathlibPolynomial (-p) = -toMathlibPolynomial p := by
  exact toMathlibPolynomial_fromMathlibPolynomial _

/-- 到 Mathlib 承载层的具名桥是单射；后续章节应复用本定理而不再展开双向桥。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=injectiv.0h1v.s4.6fc4030bb226 from=translated src=- shape=e716c754 vocab=c8664e00
-/
theorem toMathlib_injective {R : Type*} [Semiring R] :
    Function.Injective (toMathlibPolynomial : PolynomialSequence R → Polynomial R) := by
  intro p q h
  rw [← fromMathlibPolynomial_toMathlibPolynomial p,
    ← fromMathlibPolynomial_toMathlibPolynomial q, h]

/-- 当系数类型是交换环时，本库多项式运算满足交换环的全部公理。
证明借助具名桥的单射性在私有实现层验证这些等式。
> **Entry**: abstract-algebra.poly.def-/
noncomputable instance {R : Type*} [CommRing R] : CommRing (PolynomialSequence R) where
  add := (inferInstance : Add (PolynomialSequence R)).add
  add_assoc := by
    intro a b c
    apply toMathlib_injective
    simp only [toMathlib_add, add_assoc]
  zero := (inferInstance : Zero (PolynomialSequence R)).zero
  zero_add := by
    intro a
    apply toMathlib_injective
    simp only [toMathlib_add, toMathlib_zero, zero_add]
  add_zero := by
    intro a
    apply toMathlib_injective
    simp only [toMathlib_add, toMathlib_zero, add_zero]
  neg := (inferInstance : Neg (PolynomialSequence R)).neg
  neg_add_cancel := by
    intro a
    apply toMathlib_injective
    simp only [toMathlib_add, toMathlib_neg, toMathlib_zero, neg_add_cancel]
  add_comm := by
    intro a b
    apply toMathlib_injective
    simp only [toMathlib_add, add_comm]
  mul := (inferInstance : Mul (PolynomialSequence R)).mul
  mul_assoc := by
    intro a b c
    apply toMathlib_injective
    simp only [toMathlib_mul, mul_assoc]
  one := (inferInstance : One (PolynomialSequence R)).one
  one_mul := by
    intro a
    apply toMathlib_injective
    simp only [toMathlib_mul, toMathlib_one, one_mul]
  mul_one := by
    intro a
    apply toMathlib_injective
    simp only [toMathlib_mul, toMathlib_one, mul_one]
  left_distrib := by
    intro a b c
    apply toMathlib_injective
    simp only [toMathlib_mul, toMathlib_add, mul_add]
  right_distrib := by
    intro a b c
    apply toMathlib_injective
    simp only [toMathlib_mul, toMathlib_add, add_mul]
  zero_mul := by
    intro a
    apply toMathlib_injective
    simp only [toMathlib_mul, toMathlib_zero, zero_mul]
  mul_zero := by
    intro a
    apply toMathlib_injective
    simp only [toMathlib_mul, toMathlib_zero, mul_zero]
  mul_comm := by
    intro a b
    apply toMathlib_injective
    simp only [toMathlib_mul, mul_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

private noncomputable def transportedConstant {R : Type*} [CommRing R]
    (a : R) : PolynomialSequence R :=
  fromMathlibPolynomial (Polynomial.C a)

private noncomputable def transportedX {R : Type*} [CommRing R] : PolynomialSequence R :=
  fromMathlibPolynomial Polynomial.X

private noncomputable def transportedDegree {R : Type*} [CommRing R]
    (p : PolynomialSequence R) : WithBot ℕ :=
  (toMathlibPolynomial p).degree

private noncomputable def transportedEvaluate {R : Type*} [CommRing R]
    (a : R) (p : PolynomialSequence R) : R :=
  (toMathlibPolynomial p).eval a

/-- **常数多项式**：`constant a` 的常数项为 `a`，其余系数为零。
> **Entry**: abstract-algebra.poly.def-/
noncomputable def constant {R : Type*} [CommRing R] (a : R) : PolynomialSequence R :=
  transportedConstant a

/-- **不定元**：`X` 的一次项系数为一，其余系数为零。
> **Entry**: abstract-algebra.poly.def-/
noncomputable def X {R : Type*} [CommRing R] : PolynomialSequence R :=
  transportedX

/-- **次数**：返回最高非零项指标，并采用诚实约定 `degree 0 = ⊥`。
> **Entry**: abstract-algebra.poly.def-/
noncomputable def degree {R : Type*} [CommRing R] (p : PolynomialSequence R) : WithBot ℕ :=
  transportedDegree p

/-- **多项式求值**：`evaluate a p` 把不定元代入系数环元素 `a`。
> **Entry**: abstract-algebra.poly.def-/
noncomputable def evaluate {R : Type*} [CommRing R]
    (a : R) (p : PolynomialSequence R) : R :=
  transportedEvaluate a p

/-- **根**：`a` 是 `p` 的根，当且仅当 `p` 在 `a` 处的求值为零。
> **Entry**: abstract-algebra.poly.def-/
def IsRoot {R : Type*} [CommRing R] (p : PolynomialSequence R) (a : R) : Prop :=
  evaluate a p = 0

/-- **求值的教材有限和公式**：只在本库非零系数支撑上求和，因此该和确实有限。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s6.d621cb45ab31 from=translated src=- shape=ac11cd6a vocab=6ec23ca0
-/
theorem evaluate_eq_coefficientSupport_sum {R : Type*} [CommRing R]
    (a : R) (p : PolynomialSequence R) :
    evaluate a p = ∑ n ∈ coefficientSupport p, coefficient p n * a ^ n := by
  rw [evaluate]
  change (toMathlibPolynomial p).eval a = _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, coefficientSupport_eq_mathlib_support]
  simp only [coefficient_toMathlibPolynomial]

/-- 旧兼容求值经具名桥后与正式承载的 `Polynomial.eval` 一致。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s5.7cf42c690439 from=translated src=- shape=273843aa vocab=83617b96
-/
theorem evaluate_eq_mathlib_eval {R : Type*} [CommRing R]
    (a : R) (p : PolynomialSequence R) :
    evaluate a p = (toMathlibPolynomial p).eval a := by
  rfl

/-- 根的教材有限和判据。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=iff.0h3v.s6.cc6e1fbcb2b9 from=translated src=- shape=7ad5e73b vocab=33a0bfc0
-/
theorem isRoot_iff_coefficientSupport_sum_eq_zero {R : Type*} [CommRing R]
    (p : PolynomialSequence R) (a : R) :
    IsRoot p a ↔ (∑ n ∈ coefficientSupport p, coefficient p n * a ^ n) = 0 := by
  rw [IsRoot, evaluate_eq_coefficientSupport_sum]

/-- 本库根谓词与具名 Mathlib 桥后的根谓词等价。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=iff.0h3v.s5.867825e73514 from=translated src=- shape=6f62c8ab vocab=595a5a9c
-/
theorem isRoot_iff_mathlib_isRoot {R : Type*} [CommRing R]
    (p : PolynomialSequence R) (a : R) :
    IsRoot p a ↔ (toMathlibPolynomial p).IsRoot a := by
  rw [IsRoot, Polynomial.IsRoot, evaluate_eq_mathlib_eval]

/-- 零多项式的每一项系数均为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s6.9171fbb07a5d from=translated src=- shape=242dd53f vocab=c4d03831
-/
theorem coefficient_zero {R : Type*} [CommRing R] (n : ℕ) :
    coefficient (0 : PolynomialSequence R) n = 0 := by
  rw [← coefficient_toMathlibPolynomial, toMathlib_zero]
  exact Polynomial.coeff_zero n
/-- 单位多项式的常数项系数为一。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h1v.s6.223860676527 from=translated src=- shape=61888708 vocab=c4d03831
-/
theorem coefficient_one_zero {R : Type*} [CommRing R] :
    coefficient (1 : PolynomialSequence R) 0 = 1 := by
  rw [← coefficient_toMathlibPolynomial, toMathlib_one]
  exact Polynomial.coeff_one_zero
/-- 单位多项式的所有正次数项系数均为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s6.54da82478882 from=translated src=- shape=7d8b1bc8 vocab=15fdde91
-/
theorem coefficient_one_succ {R : Type*} [CommRing R] (n : ℕ) :
    coefficient (1 : PolynomialSequence R) (n + 1) = 0 := by
  rw [← coefficient_toMathlibPolynomial, toMathlib_one]
  rw [Polynomial.coeff_one]
  simp
/-- 多项式和的第 `n` 项系数等于对应系数之和。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h4v.s7.942f1a0ece2f from=translated src=- shape=58dae8f8 vocab=15fdde91
-/
theorem coefficient_add {R : Type*} [CommRing R] (p q : PolynomialSequence R) (n : ℕ) :
    coefficient (p + q) n = coefficient p n + coefficient q n := by
  rw [← coefficient_toMathlibPolynomial, toMathlib_add, Polynomial.coeff_add,
    coefficient_toMathlibPolynomial, coefficient_toMathlibPolynomial]
/-- 负多项式的第 `n` 项系数等于原系数的加法逆元。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s6.d663b18666b9 from=translated src=- shape=81d4d1ad vocab=1e7d4219
-/
theorem coefficient_neg {R : Type*} [CommRing R] (p : PolynomialSequence R) (n : ℕ) :
    coefficient (-p) n = -coefficient p n := by
  rw [← coefficient_toMathlibPolynomial, toMathlib_neg, Polynomial.coeff_neg,
    coefficient_toMathlibPolynomial]
/-- **卷积公式**：乘积的第 `n` 项系数是所有次数和为 `n` 的系数乘积之和。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h4v.s7.2faa948e9533 from=translated src=- shape=1b8ed100 vocab=99b4149b
-/
theorem coefficient_mul {R : Type*} [CommRing R] (p q : PolynomialSequence R) (n : ℕ) :
    coefficient (p * q) n = ∑ k ∈ Finset.range (n + 1),
      coefficient p k * coefficient q (n - k) := by
  rw [← coefficient_toMathlibPolynomial, toMathlib_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coefficient_toMathlibPolynomial]
/-- 常数多项式 `constant a` 的零次项系数为 `a`。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s4.f5f36c20044f from=translated src=- shape=c116036b vocab=59e9c522
-/
theorem coefficient_constant_zero {R : Type*} [CommRing R] (a : R) :
    coefficient (constant a) 0 = a := by
  simp [coefficient, constant, transportedConstant, fromMathlibPolynomial]
/-- 常数多项式的所有正次数项系数均为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s5.2d8aa4654614 from=translated src=- shape=3bb45212 vocab=35da6b44
-/
theorem coefficient_constant_succ {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    coefficient (constant a) (n + 1) = 0 := by
  simp [coefficient, constant, transportedConstant, fromMathlibPolynomial]
/-- 不定元 `X` 的常数项系数为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h1v.s5.d8776b7137a5 from=translated src=- shape=e6ec5b5c vocab=8913d400
-/
theorem coefficient_X_zero {R : Type*} [CommRing R] :
    coefficient (X : PolynomialSequence R) 0 = 0 := by
  simp [coefficient, X, transportedX, fromMathlibPolynomial]
/-- 不定元 `X` 的一次项系数为一。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h1v.s5.e7d7eb99d884 from=translated src=- shape=e6ec5b5c vocab=8913d400
-/
theorem coefficient_X_one {R : Type*} [CommRing R] :
    coefficient (X : PolynomialSequence R) 1 = 1 := by
  simp [coefficient, X, transportedX, fromMathlibPolynomial]
/-- 零多项式次数的诚实约定是 `⊥`，而不是自然数零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h1v.s5.dc09f8a90b7e from=translated src=- shape=e023bc36 vocab=386d0637
-/
theorem degree_zero {R : Type*} [CommRing R] :
    degree (0 : PolynomialSequence R) = ⊥ := by
  rw [degree, transportedDegree, toMathlib_zero, Polynomial.degree_zero]

/-- 旧兼容次数经具名桥后与正式承载的 `Polynomial.degree` 一致。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s5.44e166dc4234 from=translated src=- shape=759d10b6 vocab=68e3b388
-/
theorem degree_eq_mathlib_degree {R : Type*} [CommRing R]
    (p : PolynomialSequence R) :
    degree p = (toMathlibPolynomial p).degree := by
  rfl

/-- 多项式次数为 `⊥`，当且仅当所有本库系数都为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=iff.0h2v.s5.12137f952079 from=translated src=- shape=beb404d0 vocab=4e88fc67
-/
theorem degree_eq_bot_iff_coefficients_zero {R : Type*} [CommRing R]
    (p : PolynomialSequence R) :
    degree p = ⊥ ↔ ∀ n : ℕ, coefficient p n = 0 := by
  constructor
  · intro h n
    rw [← coefficient_toMathlibPolynomial]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [← degree_eq_mathlib_degree]
    exact h ▸ WithBot.bot_lt_coe n
  · intro h
    have hp : p = 0 := ext h
    exact hp ▸ degree_zero

/-- 严格高于次数的每一项系数都为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.1h3v.s6.2d20b67dd7c9 from=translated src=- shape=8fa66991 vocab=345640d7
-/
theorem coefficient_eq_zero_of_degree_lt {R : Type*} [CommRing R]
    (p : PolynomialSequence R) (n : ℕ)
    (h : degree p < (n : WithBot ℕ)) :
    coefficient p n = 0 := by
  rw [← coefficient_toMathlibPolynomial]
  exact Polynomial.coeff_eq_zero_of_degree_lt
    (degree_eq_mathlib_degree p ▸ h)

/-- 若次数是有限值 `n`，则最高次项系数非零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=ne.1h3v.s5.4e9ed83347ce from=translated src=- shape=8fa66991 vocab=5fbd12ef
-/
theorem coefficient_ne_zero_of_degree_eq {R : Type*} [CommRing R]
    (p : PolynomialSequence R) (n : ℕ)
    (h : degree p = (n : WithBot ℕ)) :
    coefficient p n ≠ 0 := by
  rw [← coefficient_toMathlibPolynomial]
  exact Polynomial.coeff_ne_zero_of_eq_degree
    (degree_eq_mathlib_degree p ▸ h)

/-- **次数的系数刻画**：`degree p = n` 当且仅当第 `n` 项非零而所有更高项为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=iff.0h3v.s6.c6fb4447621e from=translated src=- shape=66803a24 vocab=345640d7
-/
theorem degree_eq_nat_iff {R : Type*} [CommRing R]
    (p : PolynomialSequence R) (n : ℕ) :
    degree p = (n : WithBot ℕ) ↔
      coefficient p n ≠ 0 ∧ ∀ m : ℕ, n < m → coefficient p m = 0 := by
  rw [degree_eq_mathlib_degree]
  constructor
  · intro h
    constructor
    · rw [← coefficient_toMathlibPolynomial]
      exact Polynomial.coeff_ne_zero_of_eq_degree h
    · intro m hnm
      rw [← coefficient_toMathlibPolynomial]
      exact Polynomial.coeff_eq_zero_of_degree_lt (h ▸ WithBot.coe_lt_coe.mpr hnm)
  · rintro ⟨hn, habove⟩
    apply le_antisymm
    · exact (Polynomial.degree_le_iff_coeff_zero _ _).2 fun m hnm => by
        rw [coefficient_toMathlibPolynomial]
        exact habove m (WithBot.coe_lt_coe.mp hnm)
    · apply Polynomial.le_degree_of_ne_zero
      rwa [coefficient_toMathlibPolynomial]

/-- 满足“最高非零项”刻画的次数指标是唯一的。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.2h4v.s7.3cb85836ab09 from=translated src=- shape=59fb4a69 vocab=6a04ccc4
-/
theorem degree_index_unique {R : Type*} [CommRing R]
    (p : PolynomialSequence R) (m n : ℕ)
    (hm : coefficient p m ≠ 0 ∧ ∀ k : ℕ, m < k → coefficient p k = 0)
    (hn : coefficient p n ≠ 0 ∧ ∀ k : ℕ, n < k → coefficient p k = 0) :
    m = n := by
  have hdm := (degree_eq_nat_iff p m).2 hm
  have hdn := (degree_eq_nat_iff p n).2 hn
  exact WithBot.coe_eq_coe.mp (hdm.symm.trans hdn)

/-- 零多项式在任意元素处求值都为零。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s5.29f66b16694c from=translated src=- shape=c5725963 vocab=99bf4ee9
-/
theorem evaluate_zero {R : Type*} [CommRing R] (a : R) :
    evaluate a (0 : PolynomialSequence R) = 0 := by
  rw [evaluate, transportedEvaluate, toMathlib_zero, Polynomial.eval_zero]
/-- 单位多项式在任意元素处求值都为一。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h2v.s5.9e3dee5fe9ab from=translated src=- shape=c5725963 vocab=99bf4ee9
-/
theorem evaluate_one {R : Type*} [CommRing R] (a : R) :
    evaluate a (1 : PolynomialSequence R) = 1 := by
  rw [evaluate, transportedEvaluate, toMathlib_one, Polynomial.eval_one]
/-- 求值保持多项式加法。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h4v.s6.f634999f2e3f from=translated src=- shape=af1d8ab1 vocab=01371d79
-/
theorem evaluate_add {R : Type*} [CommRing R] (a : R) (p q : PolynomialSequence R) :
    evaluate a (p + q) = evaluate a p + evaluate a q := by
  rw [evaluate, transportedEvaluate, toMathlib_add, Polynomial.eval_add]
  rfl
/-- 求值保持加法逆元。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h3v.s6.59e2bb1c6d76 from=translated src=- shape=01c78dce vocab=2444e838
-/
theorem evaluate_neg {R : Type*} [CommRing R] (a : R) (p : PolynomialSequence R) :
    evaluate a (-p) = -evaluate a p := by
  rw [evaluate, transportedEvaluate, toMathlib_neg, Polynomial.eval_neg]
  rfl
/-- 求值保持多项式乘法。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=eq.0h4v.s6.277c182a602b from=translated src=- shape=af1d8ab1 vocab=c34f3baf
-/
theorem evaluate_mul {R : Type*} [CommRing R] (a : R) (p q : PolynomialSequence R) :
    evaluate a (p * q) = evaluate a p * evaluate a q := by
  rw [evaluate, transportedEvaluate, toMathlib_mul, Polynomial.eval_mul]
  rfl

/-- 固定代入点后的求值函数满足本库 `RingHomomorphism`：保持零、一、加法、乘法和负元。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=ringhomo.0h2v.s6.30bd27d616ea from=translated src=- shape=153b52a2 vocab=80e0d3c0
-/
theorem evaluate_ringHomomorphism {R : Type*} [CommRing R] (a : R) :
    RingHomomorphism (evaluate a : PolynomialSequence R → R) := by
  exact ⟨evaluate_zero a, evaluate_one a, evaluate_add a, evaluate_mul a, evaluate_neg a⟩

/-- **因式定理**：本库多项式 `X - constant a` 整除 `p`，当且仅当 `a` 是 `p` 的根。
公开签名完全使用本库 `PolynomialSequence`、`DividesElement` 与 `IsRoot`；Mathlib 只在证明中
经由具名桥验证对应事实。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=iff.0h3v.s7.b126b2e000bc from=translated src=- shape=8938bf44 vocab=95ba3f9e
-/
theorem divides_X_sub_constant_iff_root {R : Type*} [CommRing R]
    (p : PolynomialSequence R) (a : R) :
    DividesElement (X - constant a) p ↔ IsRoot p a := by
  have hfactor : toMathlibPolynomial (X - constant a) =
      Polynomial.X - Polynomial.C a := by
    simp only [sub_eq_add_neg, toMathlib_add, toMathlib_neg, X, constant,
      transportedX, transportedConstant,
      toMathlibPolynomial_fromMathlibPolynomial]
  constructor
  · rintro ⟨q, hq⟩
    have hm := congrArg toMathlibPolynomial hq
    rw [toMathlib_mul, hfactor] at hm
    have hdvd : Polynomial.X - Polynomial.C a ∣ toMathlibPolynomial p := ⟨_, hm⟩
    have hr := (Polynomial.dvd_iff_isRoot (p := toMathlibPolynomial p) (a := a)).mp hdvd
    exact (isRoot_iff_mathlib_isRoot p a).2 hr
  · intro hr
    have hr' := (isRoot_iff_mathlib_isRoot p a).1 hr
    have hdvd : Polynomial.X - Polynomial.C a ∣ toMathlibPolynomial p :=
      (Polynomial.dvd_iff_isRoot (p := toMathlibPolynomial p) (a := a)).mpr hr'
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨fromMathlibPolynomial q, ?_⟩
    apply toMathlib_injective
    rw [toMathlib_mul, hfactor, toMathlibPolynomial_fromMathlibPolynomial]
    exact hq

/-- **多项式环的整环性**：若系数环满足本库 `IntegralDomainAxioms`，则本库多项式环也满足
同一套整环公理，包括交换环律、零不等于一和无零因子。
> **Entry**: abstract-algebra.poly.def
@isnad1 id=integral.1h1v.s6.195d1311c220 from=translated src=- shape=d96e9922 vocab=b90674fd
-/
theorem polynomial_integralDomainAxioms {R : Type*} [CommRing R]
    (hR : IntegralDomainAxioms R) : IntegralDomainAxioms (PolynomialSequence R) := by
  letI : IsDomain R := (integralDomainAxioms_iff_isDomain (R := R)).mp hR
  refine ⟨commRing_has_commutativeRingAxioms (PolynomialSequence R), ?_, ?_⟩
  · intro h
    have hm := congrArg toMathlibPolynomial h
    rw [toMathlib_zero, toMathlib_one] at hm
    exact zero_ne_one hm
  · intro p q hpq
    have hm := congrArg toMathlibPolynomial hpq
    rw [toMathlib_mul, toMathlib_zero] at hm
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hm with hp | hq
    · exact Or.inl (toMathlib_injective (hp.trans toMathlib_zero.symm))
    · exact Or.inr (toMathlib_injective (hq.trans toMathlib_zero.symm))

end SandronesLibrary.AbstractAlgebra.PolynomialDefinition
