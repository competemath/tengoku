/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldSplitting
import Tengoku.Seed.FieldTheory.Normal.Basic
import Tengoku.Seed.FieldTheory.Perfect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/FieldSeparableNormal.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 抽象代数 / 可分扩张与正规扩张

本模块在 A3.5 的显式域嵌入、代数元和最小多项式，A3.6 的有限扩张，
以及 A3.7 的分裂域接口之上，建立可分多项式、可分元、可分扩张与
正规扩张的教材定义链。

可分多项式直接采用与形式导数的 Bézout 恒等式；可分元要求其教材
最小多项式可分；可分扩张要求每个元素可分。正规扩张要求扩张代数，
并要求每个元素的教材最小多项式在目标域中分裂。本模块进一步证明
导数判据、可分扩张代数性、分裂域正规性、有限正规扩张的分裂域刻画，
以及有限基域上的有限扩张可分。

公开 API 只使用显式 `FieldEmbedding`、正式 `Polynomial` 和 A3.5--A3.7
教材谓词。Mathlib 的代数实例、整性、有限维、可分与正规扩张类仅在
私有证明后端出现，不进入公开声明类型。

根重数刻画与“在扩域中有根的不可约多项式必分裂”的等价刻画属于
后续第二批接口；它们不改变本模块已经固定的四个核心定义。

> **Entry**: abstract-algebra.field.separable-normal
-/

namespace SandronesLibrary.AbstractAlgebra.FieldSeparableNormal

open Polynomial
open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldDegree
open SandronesLibrary.AbstractAlgebra.FieldSplitting


/-! ## 显式教材定义 -/

/-- 可分多项式的 Bézout 定义：存在多项式 `a`、`b`，使 `a * p` 与
`b * p.derivative` 之和为一。它精确表达 `p` 与形式导数互素。

> **Entry**: abstract-algebra.field.separable-normal-/
def SeparablePolynomial {K : Type*} [Field K] (p : Polynomial K) : Prop :=
  ∃ a b : Polynomial K, a * p + b * p.derivative = 1

/-- 可分元：存在一个满足 A3.5 首一、湮灭和整除泛性质的最小多项式，
并且该多项式满足 `SeparablePolynomial`。超越元因此不会被误判为可分。

> **Entry**: abstract-algebra.field.separable-normal-/
def SeparableElement {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (x : L) : Prop :=
  ∃ p : Polynomial K, MinimalPolynomialOf e x p ∧ SeparablePolynomial p

/-- 可分扩张：目标域的每个元素都是相对于指定 `FieldEmbedding` 的可分元。
该定义沿用代数扩张语境，因此可分扩张自动是代数扩张。

> **Entry**: abstract-algebra.field.separable-normal-/
def SeparableExtension {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : Prop :=
  ∀ x : L, SeparableElement e x

/-- 正规扩张：扩张首先代数，并且目标域中每个元素的任意教材最小多项式
都沿指定嵌入在目标域中分裂。这是最小多项式版的教材正规性定义。

> **Entry**: abstract-algebra.field.separable-normal-/
def NormalExtension {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : Prop :=
  AlgebraicExtension e ∧
    ∀ x : L, ∀ p : Polynomial K,
      MinimalPolynomialOf e x p → PolynomialSplitsIn e p

/-! ## 私有 Mathlib 证明后端

以下桥局部安装由显式嵌入诱导的代数结构，将教材最小多项式、
可分性、正规性、有限维和分裂域与 Mathlib 成熟接口对齐。
高级结构不会进入公开签名。
-/

-- A3.8-01：显式嵌入诱导的代数映射等于其环同态桥。
private theorem algebraMap_eq_embedding {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    @algebraMap K L _ _ e.toRingHom.toAlgebra = e.toRingHom := by
  exact RingHom.algebraMap_toAlgebra e.toRingHom

-- A3.8-02：Mathlib 代数求值与 A3.5 显式求值一致。
private theorem aeval_eq_evaluateOver {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) (x : L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    Polynomial.aeval x p = evaluateOver e p x := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  rw [Polynomial.aeval_def, algebraMap_eq_embedding]
  rfl

-- A3.8-03：A3.5 代数元与局部 Mathlib 整元谓词对齐。
private theorem algebraicElement_iff_isIntegral {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (x : L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    AlgebraicElement e x ↔ IsIntegral K x := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · rintro ⟨p, hp, hev⟩
    apply IsAlgebraic.isIntegral
    refine ⟨p, hp, ?_⟩
    rwa [aeval_eq_evaluateOver e]
  · rintro ⟨p, hpmonic, hev⟩
    refine ⟨p, hpmonic.ne_zero, ?_⟩
    rwa [← aeval_eq_evaluateOver e]

-- A3.8-04：A3.5 最小多项式泛性质唯一确定 Mathlib `minpoly`。
private theorem minimalPolynomialOf_iff_minpoly {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (x : L)
    (ha : AlgebraicElement e x) (p : Polynomial K) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    MinimalPolynomialOf e x p ↔ p = minpoly K x := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have hxint : IsIntegral K x := (algebraicElement_iff_isIntegral e x).mp ha
  have hmin : MinimalPolynomialOf e x (minpoly K x) := by
    refine ⟨minpoly.monic hxint, ?_, ?_⟩
    · rw [← aeval_eq_evaluateOver e]
      exact minpoly.aeval K x
    · intro q hq
      apply minpoly.dvd K x
      rwa [aeval_eq_evaluateOver e]
  constructor
  · intro hp
    exact minimalPolynomialOf_unique e hp hmin
  · rintro rfl
    exact hmin

-- A3.8-05：Bézout 型教材定义与 Mathlib 可分多项式谓词严格一致。
private theorem separablePolynomial_iff_mathlib {K : Type*} [Field K]
    (p : Polynomial K) : SeparablePolynomial p ↔ p.Separable := by
  simpa [SeparablePolynomial] using (Polynomial.separable_def' p).symm

-- A3.8-06：教材可分元与 Mathlib `IsSeparable` 对齐。
private theorem separableElement_iff_mathlib {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (x : L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    SeparableElement e x ↔ IsSeparable K x := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · rintro ⟨p, hpmin, hpsep⟩
    have ha : AlgebraicElement e x :=
      ⟨p, hpmin.1.ne_zero, hpmin.2.1⟩
    have hp_eq : p = minpoly K x :=
      (minimalPolynomialOf_iff_minpoly e x ha p).mp hpmin
    rw [IsSeparable, ← hp_eq]
    exact (separablePolynomial_iff_mathlib p).mp hpsep
  · intro hx
    have ha : AlgebraicElement e x :=
      (algebraicElement_iff_isIntegral e x).mpr hx.isIntegral
    refine ⟨minpoly K x, ?_, ?_⟩
    · exact (minimalPolynomialOf_iff_minpoly e x ha (minpoly K x)).mpr rfl
    · exact (separablePolynomial_iff_mathlib (minpoly K x)).mpr hx

-- A3.8-07：教材可分扩张与 Mathlib 可分扩张类对齐。
private theorem separableExtension_iff_mathlib {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    SeparableExtension e ↔ Algebra.IsSeparable K L := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · intro h
    exact ⟨fun x => (separableElement_iff_mathlib e x).mp (h x)⟩
  · intro h x
    exact (separableElement_iff_mathlib e x).mpr (h.isSeparable' x)

-- A3.8-08：教材正规扩张与 Mathlib 正规扩张类对齐。
private theorem normalExtension_iff_mathlib {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    NormalExtension e ↔ Normal K L := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · rintro ⟨halg, hsplits⟩
    apply normal_iff.mpr
    intro x
    have ha : AlgebraicElement e x := halg x
    have hxint : IsIntegral K x :=
      (algebraicElement_iff_isIntegral e x).mp ha
    refine ⟨hxint, ?_⟩
    have hmin : MinimalPolynomialOf e x (minpoly K x) :=
      (minimalPolynomialOf_iff_minpoly e x ha (minpoly K x)).mpr rfl
    simpa [PolynomialSplitsIn, algebraMap_eq_embedding e] using
      hsplits x (minpoly K x) hmin
  · intro hn
    have hn' := normal_iff.mp hn
    constructor
    · intro x
      exact (algebraicElement_iff_isIntegral e x).mpr (hn' x).1
    · intro x p hp
      have ha : AlgebraicElement e x :=
        (algebraicElement_iff_isIntegral e x).mpr (hn' x).1
      have hp_eq : p = minpoly K x :=
        (minimalPolynomialOf_iff_minpoly e x ha p).mp hp
      subst p
      simpa [PolynomialSplitsIn, algebraMap_eq_embedding e] using (hn' x).2

/-- 本库显式可分扩张谓词与由同一域嵌入诱导的 Mathlib 可分扩张类完全等价。
这是跨模块复用的正式桥；后续证明不应再次展开最小多项式转换链。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=iff.0h3v.s5.c9a03f104a32 from=translated src=- shape=416502ef vocab=68fada8f
-/
theorem separableExtension_iff_mathlibIsSeparable {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    SeparableExtension e ↔ Algebra.IsSeparable K L :=
  separableExtension_iff_mathlib e

/-- 本库显式正规扩张谓词与由同一域嵌入诱导的 Mathlib `Normal` 类完全等价。
该桥集中封装代数性、最小多项式和分裂语义的对齐，避免上层模块重复证明。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=iff.0h3v.s5.2d24ac8b300b from=translated src=- shape=416502ef vocab=6247c201
-/
theorem normalExtension_iff_mathlibNormal {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    NormalExtension e ↔ Normal K L :=
  normalExtension_iff_mathlib e

-- A3.8-09：A3.6 显式有限域基产生 Mathlib 有限维实例。
private theorem finiteFieldExtension_to_finiteDimensional {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FiniteFieldExtension e → FiniteDimensional K L := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  rintro ⟨n, b, hb⟩
  have hcomb (c : Fin n → K) :
      fieldLinearCombination e Finset.univ c b = ∑ i, c i • b i := by
    simp [fieldLinearCombination, Algebra.smul_def, algebraMap_eq_embedding e]
    rfl
  have hli : LinearIndependent K b := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    apply hb.1 c
    rw [hcomb]
    exact hc
  have hsp : ⊤ ≤ Submodule.span K (Set.range b) := by
    intro x hx
    obtain ⟨c, hc⟩ := hb.2 x
    rw [← hc, hcomb]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B : Module.Basis (Fin n) K L := Module.Basis.mk hli hsp
  exact Module.Finite.of_basis B

-- A3.8-10：A3.7 分裂域谓词与 Mathlib 分裂域类对齐并保留非零边界。
private theorem splittingFieldFor_iff_mathlib {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (p : Polynomial K) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    SplittingFieldFor e p ↔ p ≠ 0 ∧ Polynomial.IsSplittingField K L p := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have hroot : PolynomialRootSetIn e p = p.rootSet L := by
    ext x
    rw [Polynomial.mem_rootSet]
    simp only [PolynomialRootSetIn, Set.mem_ofPred_eq, aeval_eq_evaluateOver]
  have hgenerated (S : Set L) :
      generatedIntermediateFieldSet e S =
        ((IntermediateField.adjoin K S : IntermediateField K L) : Set L) := by
    ext x
    constructor
    · intro hx
      apply hx (IntermediateField.adjoin K S : Set L)
      · refine ⟨⟨⟨IntermediateField.zero_mem _, IntermediateField.one_mem _,
            ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · exact fun _ _ ha hb => IntermediateField.add_mem _ ha hb
        · exact fun _ _ ha hb => IntermediateField.mul_mem _ ha hb
        · exact fun _ ha => IntermediateField.neg_mem _ ha
        · exact fun _ hx _ => IntermediateField.inv_mem _ hx
        · rintro _ ⟨a, rfl⟩
          change algebraMap K L a ∈ (IntermediateField.adjoin K S)
          exact IntermediateField.algebraMap_mem _ a
      · exact IntermediateField.subset_adjoin K S
    · intro hx T hT hST
      let U : IntermediateField K L :=
        { carrier := T
          mul_mem' := fun {a b} ha hb => hT.1.1.2.2.2.1 ha hb
          add_mem' := fun {a b} ha hb => hT.1.1.2.2.1 ha hb
          algebraMap_mem' := fun a => by
            rw [algebraMap_eq_embedding e]
            exact hT.2 ⟨a, rfl⟩
          inv_mem' := fun x hx => by
            by_cases hzero : x = 0
            · simpa [hzero] using hT.1.1.1
            · exact hT.1.2 hx hzero }
      have hSU : S ⊆ (U : Set L) := by
        intro y hy
        exact hST hy
      exact (IntermediateField.adjoin_le_iff.mpr hSU :
        IntermediateField.adjoin K S ≤ U) hx
  constructor
  · rintro ⟨hp, hsplits, hgen⟩
    refine ⟨hp, isSplittingField_iff_intermediateField.mpr ⟨?_, ?_⟩⟩
    · simpa [PolynomialSplitsIn, algebraMap_eq_embedding e] using hsplits
    · rw [← hroot]
      apply SetLike.coe_injective
      rw [← hgenerated]
      exact hgen
  · rintro ⟨hp, hsf⟩
    obtain ⟨hsplits, hadjoin⟩ :=
      isSplittingField_iff_intermediateField.mp hsf
    refine ⟨hp, ?_, ?_⟩
    · simpa [PolynomialSplitsIn, algebraMap_eq_embedding e] using hsplits
    · rw [hroot, hgenerated]
      exact congrArg (fun F : IntermediateField K L => (F : Set L)) hadjoin

-- A3.8-11：有限正规扩张存在一个非零的 Mathlib 分裂域多项式。
private theorem normal_finite_exists_nonzero_isSplittingField {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    Normal K L → FiniteDimensional K L →
      ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.IsSplittingField K L p := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  intro hn hfd
  letI : Normal K L := hn
  letI : FiniteDimensional K L := hfd
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField K L
  by_cases hpzero : p = 0
  · subst p
    letI : Polynomial.IsSplittingField K L (0 : Polynomial K) := hp
    have hadjoin :=
      Polynomial.IsSplittingField.adjoin_rootSet L (0 : Polynomial K)
    rw [Polynomial.rootSet_zero, Algebra.adjoin_empty] at hadjoin
    have hbij : Function.Bijective (algebraMap K L) :=
      Algebra.bijective_algebraMap_iff.mpr hadjoin.symm
    let f : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L) hbij
    haveI : Polynomial.IsSplittingField K K (Polynomial.C (1 : K)) :=
      Polynomial.isSplittingField_C 1
    have hconstant :
        Polynomial.IsSplittingField K L (Polynomial.C (1 : K)) :=
      Polynomial.IsSplittingField.of_algEquiv L (Polynomial.C (1 : K)) f
    exact ⟨Polynomial.C 1, by simp, hconstant⟩
  · exact ⟨p, hpzero, hp⟩

-- A3.8-12：可分多项式的根不是其导数的根，使用显式求值陈述。
private theorem separable_root_derivative_ne_zero_bridge {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (p : Polynomial K) (x : L) :
    SeparablePolynomial p → evaluateOver e p x = 0 →
      evaluateOver e p.derivative x ≠ 0 := by
  intro hp hx
  have hsep : p.Separable := (separablePolynomial_iff_mathlib p).mp hp
  exact hsep.eval₂_derivative_ne_zero e.toRingHom hx

-- A3.8-13：有限基域上的显式有限扩张可分。
private theorem finite_base_finite_extension_separable_bridge {K L : Type*}
    [Field K] [Field L] [Finite K] (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) : SeparableExtension e := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have halg : AlgebraicExtension e :=
    finiteFieldExtension_isAlgebraic e hfin
  letI : Algebra.IsAlgebraic K L :=
    ⟨fun x => ((algebraicElement_iff_isIntegral e x).mp (halg x)).isAlgebraic⟩
  letI : PerfectField K := PerfectField.ofFinite
  have hsep : Algebra.IsSeparable K L := inferInstance
  exact (separableExtension_iff_mathlib e).mpr hsep

/-! ## 可分多项式 -/

/-- 展开 `SeparablePolynomial`：可分性恰好是多项式与其导数满足 Bézout
恒等式。该形式为后续导数和根的判据提供直接入口。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=iff.0h2v.s9.7b2ab7841d2e from=translated src=- shape=086d1bd1 vocab=ec788592
-/
theorem separablePolynomial_iff_bezout_derivative {K : Type*} [Field K]
    (p : Polynomial K) :
    SeparablePolynomial p ↔
      ∃ a b : Polynomial K, a * p + b * p.derivative = 1 := by
  rfl

/-- 可分多项式非零。若原多项式为零，其导数也为零，任何两个倍数之和
仍为零，不可能等于单位多项式。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=ne.1h2v.s5.f4ceb2652d80 from=translated src=- shape=4ceda3f7 vocab=369969ed
-/
theorem separablePolynomial_ne_zero {K : Type*} [Field K]
    {p : Polynomial K} (hp : SeparablePolynomial p) : p ≠ 0 := by
  exact (separablePolynomial_iff_mathlib p).mp hp |>.ne_zero

/-- 沿显式域嵌入映射全部系数前后，可分性等价。域嵌入的单射性保证
映射不会制造或消除多项式与导数之间的公因子。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=iff.0h4v.s5.ed87dc23c0c2 from=translated src=- shape=b3131f1c vocab=2341c4d2
-/
theorem separablePolynomial_map_iff {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) :
    SeparablePolynomial (p.map e.toRingHom) ↔ SeparablePolynomial p := by
  rw [separablePolynomial_iff_mathlib, separablePolynomial_iff_mathlib]
  exact Polynomial.separable_map e.toRingHom

/-- 域上的不可约多项式可分，当且仅当其形式导数非零。
不可约性把“与导数互素”化为导数不被原多项式整除，
而次数严格下降排除非零整除。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=iff.1h2v.s8.ea8f65b41a8d from=translated src=- shape=6aa2f9f4 vocab=15204b76
-/
theorem irreducible_separablePolynomial_iff_derivative_ne_zero
    {K : Type*} [Field K] {p : Polynomial K} (hp : Irreducible p) :
    SeparablePolynomial p ↔ p.derivative ≠ 0 := by
  rw [separablePolynomial_iff_mathlib]
  exact Polynomial.separable_iff_derivative_ne_zero hp

/-- 可分多项式在任意显式扩域中的根都不是其形式导数的根。把 Bézout
恒等式在该点求值后，若两者同时为零便会得到 `0 = 1`。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=ne.2h5v.s8.b693c303f9e8 from=translated src=- shape=1bc9e95d vocab=ee2ff487
-/
theorem separablePolynomial_root_derivative_ne_zero {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (p : Polynomial K) (x : L)
    (hp : SeparablePolynomial p) (hx : evaluateOver e p x = 0) :
    evaluateOver e p.derivative x ≠ 0 := by
  exact separable_root_derivative_ne_zero_bridge e p x hp hx

/-! ## 可分元与可分扩张 -/

/-- 每个可分元都是 A3.5 意义下的代数元。其可分最小多项式非零并在
该元素处显式求值为零，因而直接给出代数性见证。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=algebrai.1h4v.s5.d5fcd2b2f491 from=translated src=- shape=1c0fac9a vocab=ba041a33
-/
theorem separableElement_isAlgebraic {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {x : L} (hx : SeparableElement e x) :
    AlgebraicElement e x := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  apply (algebraicElement_iff_isIntegral e x).mpr
  exact ((separableElement_iff_mathlib e x).mp hx).isIntegral

/-- 给定元素代数性及一个满足 A3.5 泛性质的最小多项式后，元素可分
当且仅当这个具体多项式可分。最小多项式唯一性消除了见证选择。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=iff.2h5v.s5.58aedf639ed2 from=translated src=- shape=dfeab284 vocab=dc3df72d
-/
theorem separableElement_iff_minimalPolynomial {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) {x : L} {p : Polynomial K}
    (ha : AlgebraicElement e x) (hp : MinimalPolynomialOf e x p) :
    SeparableElement e x ↔ SeparablePolynomial p := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have hpeq : p = minpoly K x :=
    (minimalPolynomialOf_iff_minpoly e x ha p).mp hp
  rw [separableElement_iff_mathlib, IsSeparable, ← hpeq,
    ← separablePolynomial_iff_mathlib]

/-- 可分扩张必为代数扩张。逐个元素应用“可分元必代数”即可得到
A3.6 的 `AlgebraicExtension`。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=algebrai.1h3v.s4.4f82a415d146 from=translated src=- shape=f61ba1fe vocab=265b8dc7
-/
theorem separableExtension_isAlgebraic {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hsep : SeparableExtension e) :
    AlgebraicExtension e := by
  intro x
  exact separableElement_isAlgebraic e (hsep x)

/-! ## 正规扩张 -/

/-- 正规扩张首先是代数扩张。这是 `NormalExtension` 定义的第一分量，
明确正规性不适用于本模块未处理的超越扩张。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=algebrai.1h3v.s4.e13638bda30e from=translated src=- shape=f61ba1fe vocab=fa9ee731
-/
theorem NormalExtension.isAlgebraic {K L : Type*} [Field K] [Field L]
    {e : FieldEmbedding K L} (h : NormalExtension e) : AlgebraicExtension e :=
  h.1

/-- 正规扩张中，每个元素的任意教材最小多项式都在目标域中分裂。
该投影是正规性的主要操作接口，并保留显式基域嵌入。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=polynomi.2h5v.s5.6a324601de28 from=translated src=- shape=8e896ebb vocab=abedbba5
-/
theorem NormalExtension.minimalPolynomial_splits {K L : Type*}
    [Field K] [Field L] {e : FieldEmbedding K L} (h : NormalExtension e)
    (x : L) (p : Polynomial K) (hp : MinimalPolynomialOf e x p) :
    PolynomialSplitsIn e p := by
  exact h.2 x p hp

/-- 非零多项式的分裂域是正规扩张。证明后端把 A3.7 的分裂且由根生成
条件对齐到成熟分裂域接口，再调用分裂域正规性定理。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=normalex.1h4v.s5.17444741cdf4 from=translated src=- shape=8a1cdd60 vocab=0627b642
-/
theorem splittingFieldFor_normalExtension {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (p : Polynomial K)
    (h : SplittingFieldFor e p) : NormalExtension e := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have hsf : Polynomial.IsSplittingField K L p :=
    (splittingFieldFor_iff_mathlib e p).mp h |>.2
  letI : Polynomial.IsSplittingField K L p := hsf
  apply (normalExtension_iff_mathlib e).mpr
  exact Normal.of_isSplittingField p

/-- 显式扩张有限且正规，当且仅当它满足某个非零多项式的
`SplittingFieldFor`。非零条件与 A3.7 的零多项式边界保持一致。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=iff.0h3v.s5.b043cdc0c426 from=translated src=- shape=5ab89d26 vocab=0b93dc00
-/
theorem finite_normalExtension_iff_exists_splittingFieldFor {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    FiniteFieldExtension e ∧ NormalExtension e ↔
      ∃ p : Polynomial K, SplittingFieldFor e p := by
  constructor
  · rintro ⟨hfin, hnormal⟩
    letI : Algebra K L := e.toRingHom.toAlgebra
    have hn : Normal K L := (normalExtension_iff_mathlib e).mp hnormal
    have hfd : FiniteDimensional K L :=
      finiteFieldExtension_to_finiteDimensional e hfin
    obtain ⟨p, hp, hsf⟩ :=
      normal_finite_exists_nonzero_isSplittingField e hn hfd
    exact ⟨p, (splittingFieldFor_iff_mathlib e p).mpr ⟨hp, hsf⟩⟩
  · rintro ⟨p, hp⟩
    exact ⟨splittingFieldFor_finite e p hp,
      splittingFieldFor_normalExtension e p hp⟩

/-! ## 有限基域上的可分性 -/

/-- 有限基域上的每个显式有限扩张都是可分扩张。有限域是完美域，而
有限扩张先由 A3.6 得到代数性，因此每个最小多项式均可分。

> **Entry**: abstract-algebra.field.separable-normal
@isnad1 id=separabl.1h3v.s5.c4c988afed14 from=translated src=- shape=5edc50de vocab=f934c642
-/
theorem finiteFieldExtension_over_finiteField_isSeparable {K L : Type*}
    [Field K] [Field L] [Finite K] (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) : SeparableExtension e := by
  exact finite_base_finite_extension_separable_bridge e hfin

end SandronesLibrary.AbstractAlgebra.FieldSeparableNormal
