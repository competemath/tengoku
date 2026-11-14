/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.PolynomialFactorization
import Tengoku.Seed.FieldTheory.Minpoly.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/FieldExtension.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 抽象代数 / 域扩张、代数元与最小多项式

本模块以显式函数形式的域嵌入为起点，建立域扩张的教材定义链。域嵌入记录本库
`RingHomomorphism` 与单射性；子域和中间域直接用底层集合的封闭性质表达；生成中间域
定义为所有候选中间域的交。随后使用正式承载 `Polynomial K` 定义跨系数域求值、代数元、
超越元、最小多项式的整除泛性质以及单扩张。

公开教材 API 始终显式携带 `FieldEmbedding K L`，并使用 `SubfieldSet`、
`IntermediateFieldSet` 等集合谓词，不要求调用者提供隐式的 Mathlib `Algebra`、
`IntermediateField` 或模结构。Mathlib 的 `Algebra`、`aeval` 与 `minpoly` 仅出现在
私有桥和证明后端；这些桥证明其语义与显式嵌入和 `evaluateOver` 完全一致。

> **Entry**: abstract-algebra.field.extension
-/

namespace SandronesLibrary.AbstractAlgebra.FieldExtension

open Polynomial
open SandronesLibrary.AbstractAlgebra.Ring


/-! ## 显式域嵌入 -/

/-- **显式域嵌入**：从域 `K` 到域 `L` 的普通函数，连同本库环同态律和单射性。
显式保存嵌入可避免全局实例静默选择基域映射，并允许比较同一对域之间的不同嵌入。
> **Entry**: abstract-algebra.field.extension-/
structure FieldEmbedding (K L : Type*) [Field K] [Field L] where
  toFun : K → L
  map_isRingHomomorphism : RingHomomorphism toFun
  injective : Function.Injective toFun

/-- **函数强制转换**：域嵌入可直接作为其底层函数使用，记作 `e x`。
> **Entry**: abstract-algebra.field.extension-/
instance {K L : Type*} [Field K] [Field L] : CoeFun (FieldEmbedding K L) (fun _ => K → L) :=
  ⟨FieldEmbedding.toFun⟩

/-- **环同态桥**：把显式域嵌入打包为 Mathlib `RingHom`，底层函数保持不变。
该桥供成熟多项式接口使用；教材侧仍以 `FieldEmbedding` 为主要承载。
> **Entry**: abstract-algebra.field.extension-/
def FieldEmbedding.toRingHom {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : K →+* L where
  toFun := e.toFun
  map_one' := e.map_isRingHomomorphism.2.1
  map_mul' := e.map_isRingHomomorphism.2.2.2.1
  map_zero' := e.map_isRingHomomorphism.1
  map_add' := e.map_isRingHomomorphism.2.2.1

/-- **恒等域嵌入**：域上的恒等函数保持所有环运算且为单射，因此给出自身到自身的嵌入。
> **Entry**: abstract-algebra.field.extension-/
def FieldEmbedding.id (K : Type*) [Field K] : FieldEmbedding K K where
  toFun := fun x => x
  map_isRingHomomorphism := by
    exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  injective := Function.injective_id

/-- **域嵌入的复合**：若 `K` 嵌入 `L` 且 `L` 嵌入 `M`，函数复合给出 `K` 到 `M` 的嵌入。
环同态律逐层复合，单射性由两个嵌入的单射性得到。
> **Entry**: abstract-algebra.field.extension-/
def FieldEmbedding.comp {K L M : Type*} [Field K] [Field L] [Field M]
    (g : FieldEmbedding L M) (e : FieldEmbedding K L) : FieldEmbedding K M where
  toFun := g.toFun ∘ e.toFun
  map_isRingHomomorphism := by
    exact ⟨by simp only [Function.comp_apply, e.map_isRingHomomorphism.1,
        g.map_isRingHomomorphism.1],
      by simp only [Function.comp_apply, e.map_isRingHomomorphism.2.1,
        g.map_isRingHomomorphism.2.1],
      fun a b => by simp only [Function.comp_apply, e.map_isRingHomomorphism.2.2.1,
        g.map_isRingHomomorphism.2.2.1],
      fun a b => by simp only [Function.comp_apply, e.map_isRingHomomorphism.2.2.2.1,
        g.map_isRingHomomorphism.2.2.2.1],
      fun a => by simp only [Function.comp_apply, e.map_isRingHomomorphism.2.2.2.2,
        g.map_isRingHomomorphism.2.2.2.2]⟩
  injective := g.injective.comp e.injective

/-- **逆元保持**：显式域嵌入把 `x⁻¹` 映为 `(e x)⁻¹`，包括 `x = 0` 的域逆元约定。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=eq.0h4v.s6.4a00d7b93e71 from=translated src=- shape=103c51f1 vocab=4549efac
-/
theorem FieldEmbedding.map_inv {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (x : K) : e x⁻¹ = (e x)⁻¹ := by
  exact map_inv₀ e.toRingHom x

/-! ## 子域与中间域 -/

/-- **子域的集合定义**：`S` 首先是本库 `SubringSet`，并对其中每个非零元素的逆元封闭。
这正是教材中子域对域运算封闭的集合表述。
> **Entry**: abstract-algebra.field.extension-/
def SubfieldSet {L : Type*} [Field L] (S : Set L) : Prop :=
  SubringSet S ∧ ∀ ⦃x : L⦄, x ∈ S → x ≠ 0 → x⁻¹ ∈ S

/-- **中间域的集合定义**：`L` 的子域集合若还包含基域嵌入 `e` 的全部像，就构成中间域。
定义显式保留所选基域嵌入，不依赖全局标量结构。
> **Entry**: abstract-algebra.field.extension-/
def IntermediateFieldSet {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (S : Set L) : Prop :=
  SubfieldSet S ∧ Set.range e.toFun ⊆ S

/-- **最大子域集合**：全集对所有域运算封闭，因此是所在域自身对应的子域集合。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=subfield.0h1v.s3.d07088d90e4f from=translated src=- shape=84bfdc15 vocab=84cc45f0
-/
theorem subfieldSet_univ {L : Type*} [Field L] : SubfieldSet (Set.univ : Set L) := by
  simp [SubfieldSet, SubringSet]

/-- **最大中间域集合**：目标域全集既是子域，又显然包含基域嵌入的全部像。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=intermed.0h3v.s4.2f708905bdc0 from=translated src=- shape=ad2ae334 vocab=f195bab7
-/
theorem intermediateFieldSet_univ {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : IntermediateFieldSet e (Set.univ : Set L) := by
  exact ⟨subfieldSet_univ, Set.subset_univ _⟩

/-- **子域对任意交封闭**：若一族集合各自为子域，则它们的逐点交集仍对全部域运算封闭。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=subfield.1h3v.s5.1f2488ba44be from=translated src=- shape=64831ca3 vocab=3f3199af
-/
theorem subfieldSet_iInter {L ι : Type*} [Field L] {F : ι → Set L}
    (hF : ∀ i, SubfieldSet (F i)) : SubfieldSet (⋂ i, F i) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Set.mem_iInter]
    exact fun i => (hF i).1.1
  · simp only [Set.mem_iInter]
    exact fun i => (hF i).1.2.1
  · intro a b ha hb
    simp only [Set.mem_iInter] at ha hb ⊢
    exact fun i => (hF i).1.2.2.1 (ha i) (hb i)
  · intro a b ha hb
    simp only [Set.mem_iInter] at ha hb ⊢
    exact fun i => (hF i).1.2.2.2.1 (ha i) (hb i)
  · intro a ha
    simp only [Set.mem_iInter] at ha ⊢
    exact fun i => (hF i).1.2.2.2.2 (ha i)
  · intro x hx hne
    simp only [Set.mem_iInter] at hx ⊢
    exact fun i => (hF i).2 (hx i) hne

/-- **中间域对任意交封闭**：任意交保留子域封闭性，并继续包含基域嵌入的每个像。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=intermed.1h5v.s5.8b5ee672f2ae from=translated src=- shape=026fb6f0 vocab=51306f73
-/
theorem intermediateFieldSet_iInter {K L ι : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {F : ι → Set L}
    (hF : ∀ i, IntermediateFieldSet e (F i)) :
    IntermediateFieldSet e (⋂ i, F i) := by
  refine ⟨subfieldSet_iInter (fun i => (hF i).1), ?_⟩
  intro x hx
  simp only [Set.mem_iInter]
  exact fun i => (hF i).2 hx

/-! ## 生成中间域 -/

/-- **生成中间域**：`S` 生成的中间域由所有包含 `S` 的中间域集合之交刻画。
元素属于该集合，当且仅当它属于每一个包含 `S` 的候选中间域。
> **Entry**: abstract-algebra.field.extension-/
def generatedIntermediateFieldSet {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (S : Set L) : Set L :=
  {x | ∀ T : Set L, IntermediateFieldSet e T → S ⊆ T → x ∈ T}

/-- **生成集合确为中间域**：交集式定义对域运算封闭，并包含基域嵌入的全部像。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=intermed.0h4v.s5.d5fb62593180 from=translated src=- shape=61ca9d3d vocab=7a05b4a9
-/
theorem generatedIntermediateFieldSet_isIntermediateField {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (S : Set L) :
    IntermediateFieldSet e (generatedIntermediateFieldSet e S) := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro T hT hST
    exact hT.1.1.1
  · intro T hT hST
    exact hT.1.1.2.1
  · intro a b ha hb T hT hST
    exact hT.1.1.2.2.1 (ha T hT hST) (hb T hT hST)
  · intro a b ha hb T hT hST
    exact hT.1.1.2.2.2.1 (ha T hT hST) (hb T hT hST)
  · intro a ha T hT hST
    exact hT.1.1.2.2.2.2 (ha T hT hST)
  · intro x hx hne T hT hST
    exact hT.1.2 (hx T hT hST) hne
  · intro x hx T hT hST
    exact hT.2 hx

/-- **生成集包含性**：每个生成元都属于所有包含生成集的候选中间域，因而属于生成中间域。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=le.0h4v.s5.6d9de0d46f6d from=translated src=- shape=cff4f7eb vocab=1233e22c
-/
theorem subset_generatedIntermediateFieldSet {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (S : Set L) :
    S ⊆ generatedIntermediateFieldSet e S := by
  intro x hx T hT hST
  exact hST hx

/-- **基域像包含性**：生成中间域作为中间域，必包含显式嵌入的全部基域元素。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=le.0h4v.s5.ce48247ec436 from=translated src=- shape=b9b79832 vocab=d2c40951
-/
theorem range_subset_generatedIntermediateFieldSet {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (S : Set L) :
    Set.range e.toFun ⊆ generatedIntermediateFieldSet e S := by
  exact (generatedIntermediateFieldSet_isIntermediateField e S).2

/-- **生成中间域的最小性**：任何包含 `S` 的中间域都包含 `S` 所生成的中间域。
这是交集式生成构造的教材泛性质。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=le.2h5v.s5.cafb078bb9f3 from=translated src=- shape=0a96152a vocab=20ab0a42
-/
theorem generatedIntermediateFieldSet_least {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {S T : Set L}
    (hT : IntermediateFieldSet e T) (hST : S ⊆ T) :
    generatedIntermediateFieldSet e S ⊆ T := by
  intro x hx
  exact hx T hT hST

/-- **生成构造的单调性**：若 `S ⊆ T`，则由 `S` 生成的中间域包含于由 `T` 生成的中间域。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=le.1h5v.s5.5a9287469a76 from=translated src=- shape=a3343d1e vocab=1233e22c
-/
theorem generatedIntermediateFieldSet_mono {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {S T : Set L} (hST : S ⊆ T) :
    generatedIntermediateFieldSet e S ⊆ generatedIntermediateFieldSet e T := by
  apply generatedIntermediateFieldSet_least e
  · exact generatedIntermediateFieldSet_isIntermediateField e T
  · exact hST.trans (subset_generatedIntermediateFieldSet e T)

/-! ## 异系数环求值 -/

/-- **跨系数域求值**：先沿显式嵌入把 `K` 的系数送入 `L`，再把不定元代入 `a : L`。
实现采用正式 `Polynomial.eval₂`，但基域映射由参数 `e` 明确给出。
> **Entry**: abstract-algebra.field.extension-/
def evaluateOver {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) (a : L) : L :=
  Polynomial.eval₂ e.toRingHom a p

/-- **常数求值公式**：常数多项式 `C c` 沿嵌入求值后等于基域元素 `c` 的像 `e c`。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=eq.0h5v.s7.a841100a04bd from=translated src=- shape=f4dcf3cc vocab=98013124
-/
theorem evaluateOver_C {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (c : K) (a : L) :
    evaluateOver e (C c) a = e c := by
  exact Polynomial.eval₂_C e.toRingHom a

/-- **不定元求值公式**：把不定元 `X` 代入 `a` 的结果恰为 `a`。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=eq.0h4v.s5.3e552148f7b8 from=translated src=- shape=58fccfcb vocab=4b340d91
-/
theorem evaluateOver_X {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (a : L) : evaluateOver e X a = a := by
  exact Polynomial.eval₂_X e.toRingHom a

/-- **求值保持加法**：两个 `K` 系数多项式之和在 `a` 处的值等于各自求值之和。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=eq.0h6v.s7.540f06d4c884 from=translated src=- shape=e5e7ebc6 vocab=fedc599e
-/
theorem evaluateOver_add {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p q : Polynomial K) (a : L) :
    evaluateOver e (p + q) a = evaluateOver e p a + evaluateOver e q a := by
  exact Polynomial.eval₂_add (p := p) (q := q) e.toRingHom a

/-- **求值保持乘法**：两个 `K` 系数多项式之积在 `a` 处的值等于各自求值之积。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=eq.0h6v.s7.5d471320f967 from=translated src=- shape=e5e7ebc6 vocab=aa99d86d
-/
theorem evaluateOver_mul {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p q : Polynomial K) (a : L) :
    evaluateOver e (p * q) a = evaluateOver e p a * evaluateOver e q a := by
  exact Polynomial.eval₂_mul (p := p) (q := q) e.toRingHom a

/-! ## 代数元与超越元 -/

/-- **代数元**：存在非零 `K` 系数多项式沿 `e` 在 `a` 处取值为零时，`a` 在该扩张上代数。
非零条件排除了零多项式给出的空洞关系。
> **Entry**: abstract-algebra.field.extension-/
def AlgebraicElement {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (a : L) : Prop :=
  ∃ p : Polynomial K, p ≠ 0 ∧ evaluateOver e p a = 0

/-- **超越元**：若 `a` 不满足任何非零 `K` 系数多项式关系，则称它在显式扩张 `e` 上超越。
> **Entry**: abstract-algebra.field.extension-/
def TranscendentalElement {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (a : L) : Prop :=
  ¬ AlgebraicElement e a

/-- **基域像都是代数元**：`e x` 被一次多项式 `X - C x` 湮灭，因此在扩张上代数。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=algebrai.0h4v.s4.a771de673e8a from=translated src=- shape=637b049f vocab=31576d60
-/
theorem base_image_algebraic {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (x : K) : AlgebraicElement e (e x) := by
  refine ⟨X - C x, Polynomial.X_sub_C_ne_zero x, ?_⟩
  rw [sub_eq_add_neg, evaluateOver_add, evaluateOver_X]
  have hnegC : -(C x) = C (-x) := by simp
  rw [hnegC, evaluateOver_C]
  have hneg : e.toFun (-x) = -e.toFun x := e.toRingHom.map_neg x
  rw [hneg]
  exact add_neg_cancel (e x)

/-- **超越性的逐多项式判据**：`a` 超越，当且仅当每个非零 `K` 系数多项式在 `a` 处均非零。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=iff.0h4v.s6.8f3fd7b3b032 from=translated src=- shape=4d12a21a vocab=28578b27
-/
theorem transcendentalElement_iff {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (a : L) :
    TranscendentalElement e a ↔
      ∀ p : Polynomial K, p ≠ 0 → evaluateOver e p a ≠ 0 := by
  constructor
  · intro h p hp hev
    exact h ⟨p, hp, hev⟩
  · intro h halg
    obtain ⟨p, hp, hev⟩ := halg
    exact h p hp hev

/-! ## 最小多项式 -/

/-- **最小多项式的教材泛性质**：`p` 首一、湮灭 `a`，并整除所有湮灭 `a` 的多项式。
首一性固定相伴类代表，整除条件表达最小次数性质而无需在定义中作选择。
> **Entry**: abstract-algebra.field.extension-/
def MinimalPolynomialOf {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (a : L) (p : Polynomial K) : Prop :=
  p.Monic ∧ evaluateOver e p a = 0 ∧
    ∀ q : Polynomial K, evaluateOver e q a = 0 → p ∣ q

/-- 私有桥：由显式嵌入构造的 `Algebra` 实例，其基域映射正是该嵌入的环同态桥。-/
private theorem toAlgebra_algebraMap_eq {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    @algebraMap K L _ _ e.toRingHom.toAlgebra = e.toRingHom := by
  exact RingHom.algebraMap_toAlgebra e.toRingHom

/-- 私有桥：所选 `Algebra` 下的 `aeval` 与本库显式异系数求值一致。-/
private theorem aeval_eq_evaluateOver {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (p : Polynomial K) (a : L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    Polynomial.aeval a p = evaluateOver e p a := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  rw [Polynomial.aeval_def, toAlgebra_algebraMap_eq]
  rfl

/-- 私有桥：教材定义的代数元在显式嵌入诱导的 `Algebra` 下是整元。-/
private theorem algebraicElement_isIntegral {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {a : L} (ha : AlgebraicElement e a) :
    @IsIntegral K L _ _ e.toRingHom.toAlgebra a := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  apply IsAlgebraic.isIntegral
  obtain ⟨p, hp, hev⟩ := ha
  refine ⟨p, hp, ?_⟩
  rwa [aeval_eq_evaluateOver e]

/-- 私有桥：显式嵌入诱导的 `Algebra` 下，Mathlib 最小多项式满足本库教材泛性质。-/
private theorem minpoly_isMinimalPolynomialOf {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {a : L} (ha : AlgebraicElement e a) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    MinimalPolynomialOf e a (minpoly K a) := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have haIntegral : IsIntegral K a := algebraicElement_isIntegral e ha
  refine ⟨minpoly.monic haIntegral, ?_, ?_⟩
  · rw [← aeval_eq_evaluateOver e]
    exact minpoly.aeval K a
  · intro q hq
    apply minpoly.dvd K a
    rwa [aeval_eq_evaluateOver e]

/-- **最小多项式存在性**：每个代数元都有满足首一、湮灭和整除泛性质的多项式。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=ex.1h4v.s5.251fadba3b3b from=translated src=- shape=978201a7 vocab=3949c08e
-/
theorem minimalPolynomialOf_exists {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {a : L} (ha : AlgebraicElement e a) :
    ∃ p : Polynomial K, MinimalPolynomialOf e a p := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  exact ⟨minpoly K a, minpoly_isMinimalPolynomialOf e ha⟩

/-- **最小多项式唯一性**：两个满足教材泛性质的多项式互相整除；首一性消除单位倍数后严格相等。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=eq.2h6v.s6.8bf77583b1f3 from=translated src=- shape=20d1d06a vocab=4775785f
-/
theorem minimalPolynomialOf_unique {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {a : L} {p q : Polynomial K}
    (hp : MinimalPolynomialOf e a p) (hq : MinimalPolynomialOf e a q) : p = q := by
  have hpq : p ∣ q := hp.2.2 q hq.2.1
  have hqp : q ∣ p := hq.2.2 p hp.2.1
  apply Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hpq
  · exact Polynomial.natDegree_le_of_dvd hqp hp.1.ne_zero
  · rw [hp.1.leadingCoeff, hq.1.leadingCoeff]

/-- **最小多项式非零**：满足教材泛性质的多项式首一，而域上的首一多项式不可能为零。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=ne.1h5v.s6.c76ee9454731 from=translated src=- shape=9efa3760 vocab=4775785f
-/
theorem minimalPolynomialOf_ne_zero {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {a : L} {p : Polynomial K}
    (hp : MinimalPolynomialOf e a p) : p ≠ 0 := by
  exact hp.1.ne_zero

/-- **最小多项式不可约**：代数元的首一最小多项式在基域多项式环中不可约。
证明后端将教材泛性质唯一识别为 Mathlib `minpoly`，公开结论不暴露其结构。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=irreduci.2h5v.s6.651360383565 from=translated src=- shape=247de262 vocab=a9281c6d
-/
theorem minimalPolynomialOf_irreducible {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {a : L} {p : Polynomial K}
    (ha : AlgebraicElement e a) (hp : MinimalPolynomialOf e a p) :
    Irreducible p := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  have hmin : MinimalPolynomialOf e a (minpoly K a) :=
    minpoly_isMinimalPolynomialOf e ha
  have hp_eq : p = minpoly K a := minimalPolynomialOf_unique e hp hmin
  rw [hp_eq]
  exact minpoly.irreducible (algebraicElement_isIntegral e ha)

/-! ## 单扩张 -/

/-- **单扩张**：若单元素集合 `{a}` 生成的中间域就是整个目标域，则称该扩张由 `a` 单生成。
> **Entry**: abstract-algebra.field.extension-/
def SimpleExtension {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (a : L) : Prop :=
  generatedIntermediateFieldSet e ({a} : Set L) = Set.univ

/-- **单扩张的展开判据**：单扩张等价于生成元 `a` 所生成的中间域集合等于全集。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=iff.0h4v.s5.e4f2fdf0c88a from=translated src=- shape=7d625909 vocab=1f699631
-/
theorem simpleExtension_iff {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (a : L) :
    SimpleExtension e a ↔ generatedIntermediateFieldSet e ({a} : Set L) = Set.univ := by
  rfl

/-- **生成元属于生成域**：元素 `a` 必属于由单元素集合 `{a}` 生成的中间域。
> **Entry**: abstract-algebra.field.extension
@isnad1 id=mem.0h4v.s5.85b6ca8d7dbb from=translated src=- shape=db3a5616 vocab=6d2324d6
-/
theorem generator_mem_generatedIntermediateFieldSet {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (a : L) :
    a ∈ generatedIntermediateFieldSet e ({a} : Set L) := by
  exact subset_generatedIntermediateFieldSet e ({a} : Set L) (Set.mem_singleton a)

end SandronesLibrary.AbstractAlgebra.FieldExtension
