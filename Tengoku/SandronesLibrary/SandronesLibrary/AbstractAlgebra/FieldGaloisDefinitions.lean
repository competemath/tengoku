/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldSeparableNormalCharacterizations
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.Group

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 抽象代数 / Galois 扩张、自同构群与固定域

本模块建立 A3.9a 的教材定义层。基域自同构直接复用 A3.7 已验证的
`FieldIsomorphismOver e e`，不再复制一套同构结构；恒等、复合与逆运算
随后逐项满足本库 `GroupAxioms`。任意一族基域自同构的固定元素构成
`FixedFieldSet`，并被证明是包含基域像的中间域集合。最后，Galois 扩张
按教材定义为可分且正规，并由 A3.8 第二批给出不可约多项式刻画。

公开 API 只使用显式嵌入、集合谓词和本库教材定义。Mathlib 的隐式代数
结构、代数同构、打包中间域、子群和 Galois 类型类均不进入公开声明。
有限 Galois 基本定理、阶数公式及固定域—子群对应属于 A3.9b，不在此处。

`FieldAutomorphismOver` 是 `abbrev`；声明映射工具若漏掉缩写，必须人工
核对其展开、以下运算和 `fieldAutomorphismOver_groupAxioms` 真实使用链。

> **Entry**: abstract-algebra.field.galois-definitions
-/

namespace SandronesLibrary.AbstractAlgebra.FieldGaloisDefinitions

open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldSplitting
open SandronesLibrary.AbstractAlgebra.FieldDegree
open SandronesLibrary.AbstractAlgebra.FieldSeparableNormal
open SandronesLibrary.AbstractAlgebra.Group

/-! ## 显式基域自同构 -/

/-- **基域自同构**：`L/K` 的自同构就是 `L` 到自身的
`FieldIsomorphismOver e e`。这复用已有正逆嵌入与固定基域条件。

> **Entry**: abstract-algebra.field.galois-definitions-/
abbrev FieldAutomorphismOver {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) := FieldIsomorphismOver e e

/-- 恒等基域自同构，正向与逆向映射都是目标域上的恒等嵌入。

> **Entry**: abstract-algebra.field.galois-definitions-/
def FieldAutomorphismOver.identity {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : FieldAutomorphismOver e :=
  FieldIsomorphismOver.refl e

/-- 基域自同构的复合，约定 `(σ * τ)(x) = σ(τ(x))`，因此实现时按反序
调用既有 `FieldIsomorphismOver.trans`。

> **Entry**: abstract-algebra.field.galois-definitions-/
def FieldAutomorphismOver.comp {K L : Type*} [Field K] [Field L]
    {e : FieldEmbedding K L} (σ τ : FieldAutomorphismOver e) :
    FieldAutomorphismOver e :=
  FieldIsomorphismOver.trans τ σ

/-- 基域自同构的逆：交换原同构保存的正向与逆向域嵌入。

> **Entry**: abstract-algebra.field.galois-definitions-/
def FieldAutomorphismOver.inverse {K L : Type*} [Field K] [Field L]
    {e : FieldEmbedding K L} (σ : FieldAutomorphismOver e) :
    FieldAutomorphismOver e :=
  FieldIsomorphismOver.symm σ

/-- 自同构类型的单位元采用恒等基域自同构。

> **Entry**: abstract-algebra.field.galois-definitions-/
instance {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L} :
    One (FieldAutomorphismOver e) :=
  ⟨FieldAutomorphismOver.identity e⟩

/-- 自同构类型的乘法采用约定次序的函数复合。

> **Entry**: abstract-algebra.field.galois-definitions-/
instance {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L} :
    Mul (FieldAutomorphismOver e) :=
  ⟨FieldAutomorphismOver.comp⟩

/-- 自同构类型的逆运算采用基域上同构的对称同构。

> **Entry**: abstract-algebra.field.galois-definitions-/
instance {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L} :
    Inv (FieldAutomorphismOver e) :=
  ⟨FieldAutomorphismOver.inverse⟩

/-! ## 私有外延与群律后端 -/

private theorem fieldEmbedding_ext_bridge
    {K L : Type*} [Field K] [Field L]
    {f g : FieldEmbedding K L} (h : ∀ x : K, f x = g x) : f = g := by
  cases f with
  | mk ff fh fi =>
    cases g with
    | mk gf gh gi =>
      dsimp at h
      have hfun : ff = gf := funext h
      cases hfun
      rfl

private theorem fieldAutomorphismOver_ext_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    {σ τ : FieldAutomorphismOver e}
    (h : ∀ x : L, σ.forward x = τ.forward x) : σ = τ := by
  have hforward : σ.forward = τ.forward := fieldEmbedding_ext_bridge h
  have hinverse : FieldIsomorphismOver.inverse σ =
      FieldIsomorphismOver.inverse τ := by
    apply fieldEmbedding_ext_bridge
    intro y
    apply τ.forward.injective
    rw [τ.right_inverse]
    rw [← hforward, σ.right_inverse]
  cases σ with
  | mk sf si sli sri sfix =>
    cases τ with
    | mk tf ti tli tri tfix =>
      dsimp at hforward hinverse
      cases hforward
      cases hinverse
      rfl

private theorem fieldAutomorphismOver_mul_assoc_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ τ υ : FieldAutomorphismOver e) : (σ * τ) * υ = σ * (τ * υ) := by
  apply fieldAutomorphismOver_ext_bridge
  intro x
  rfl

private theorem fieldAutomorphismOver_one_mul_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : 1 * σ = σ := by
  apply fieldAutomorphismOver_ext_bridge
  intro x
  rfl

private theorem fieldAutomorphismOver_mul_one_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : σ * 1 = σ := by
  apply fieldAutomorphismOver_ext_bridge
  intro x
  rfl

private theorem fieldAutomorphismOver_inv_mul_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : σ⁻¹ * σ = 1 := by
  apply fieldAutomorphismOver_ext_bridge
  intro x
  exact σ.left_inverse x

private theorem fieldAutomorphismOver_mul_inv_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : σ * σ⁻¹ = 1 := by
  apply fieldAutomorphismOver_ext_bridge
  intro x
  exact σ.right_inverse x

/-! ## 自同构的教材群公理 -/

/-- 两个基域自同构若正向函数逐点相同，则整个正逆同构结构相等。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.1h5v.s6.bcc1d01ece59 from=translated src=- shape=d30c0e48 vocab=a5424383
-/
@[ext] theorem FieldAutomorphismOver.ext
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    {σ τ : FieldAutomorphismOver e}
    (h : ∀ x : L, σ.forward x = τ.forward x) : σ = τ :=
  fieldAutomorphismOver_ext_bridge h

/-- 自同构乘法逐点就是函数复合，外层先应用 `σ`。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h6v.s6.970fbdae9d3c from=translated src=- shape=f7a1cf14 vocab=300c7bf7
-/
theorem fieldAutomorphismOver_comp_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ τ : FieldAutomorphismOver e) (x : L) :
    (σ * τ).forward x = σ.forward (τ.forward x) := rfl

/-- 恒等自同构逐点固定目标域中的每个元素。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h4v.s5.13e07f6f50ef from=translated src=- shape=e1eb6ae9 vocab=a5424383
-/
theorem fieldAutomorphismOver_identity_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L} (x : L) :
    (1 : FieldAutomorphismOver e).forward x = x := rfl

/-- 逆自同构的正向函数就是原同构中保存的逆向域嵌入。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h5v.s6.488f3d34e99c from=translated src=- shape=09b6e8c5 vocab=d2638757
-/
theorem fieldAutomorphismOver_inverse_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) (x : L) :
    σ⁻¹.forward x = (FieldIsomorphismOver.inverse σ) x := rfl

/-- 基域自同构的复合满足结合律。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h6v.s7.aa6fde3297c1 from=translated src=- shape=fa3c97c8 vocab=c1c55788
-/
theorem fieldAutomorphismOver_mul_assoc
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ τ υ : FieldAutomorphismOver e) : (σ * τ) * υ = σ * (τ * υ) :=
  fieldAutomorphismOver_mul_assoc_bridge σ τ υ

/-- 恒等基域自同构是复合运算的左单位元。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h4v.s6.8cf0ba52a407 from=translated src=- shape=057f9e03 vocab=c1c55788
-/
theorem fieldAutomorphismOver_one_mul
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : 1 * σ = σ :=
  fieldAutomorphismOver_one_mul_bridge σ

/-- 恒等基域自同构是复合运算的右单位元。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h4v.s6.ed6742e179d1 from=translated src=- shape=c8fc1d81 vocab=c1c55788
-/
theorem fieldAutomorphismOver_mul_one
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : σ * 1 = σ :=
  fieldAutomorphismOver_mul_one_bridge σ

/-- 逆基域自同构满足左逆律。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h4v.s6.42bc37dc9aab from=translated src=- shape=ad064468 vocab=e37696fb
-/
theorem fieldAutomorphismOver_inv_mul
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : σ⁻¹ * σ = 1 :=
  fieldAutomorphismOver_inv_mul_bridge σ

/-- 逆基域自同构满足右逆律。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h4v.s6.df71713394bb from=translated src=- shape=3e31cd51 vocab=e37696fb
-/
theorem fieldAutomorphismOver_mul_inv
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) : σ * σ⁻¹ = 1 :=
  fieldAutomorphismOver_mul_inv_bridge σ

/-- 恒等、复合和逆运算满足本库逐条列出的全部群公理，因而显式
基域自同构在教材意义下组成一个群。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=groupaxi.0h3v.s5.f9405ee349f0 from=translated src=- shape=272b61da vocab=30c018b2
-/
theorem fieldAutomorphismOver_groupAxioms
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    GroupAxioms (FieldAutomorphismOver e) :=
  ⟨fieldAutomorphismOver_mul_assoc, fieldAutomorphismOver_one_mul,
    fieldAutomorphismOver_mul_one, fieldAutomorphismOver_inv_mul,
    fieldAutomorphismOver_mul_inv⟩

/-! ## 固定域集合 -/

/-- **固定域集合**：`H` 中每个显式基域自同构都逐点固定的目标域元素。
定义允许任意自同构族；域封闭性不需要预先假设 `H` 是子群。

> **Entry**: abstract-algebra.field.galois-definitions-/
def FixedFieldSet {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Set (FieldAutomorphismOver e)) : Set L :=
  {x | ∀ σ, σ ∈ H → σ.forward x = x}

private theorem fixedFieldSet_isSubfield_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Set (FieldAutomorphismOver e)) :
    SubfieldSet (FixedFieldSet e H) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro σ hσ; exact σ.forward.map_isRingHomomorphism.1
  · intro σ hσ; exact σ.forward.map_isRingHomomorphism.2.1
  · intro x y hx hy σ hσ
    rw [σ.forward.map_isRingHomomorphism.2.2.1, hx σ hσ, hy σ hσ]
  · intro x y hx hy σ hσ
    rw [σ.forward.map_isRingHomomorphism.2.2.2.1, hx σ hσ, hy σ hσ]
  · intro x hx σ hσ
    rw [σ.forward.map_isRingHomomorphism.2.2.2.2, hx σ hσ]
  · intro x hx hne σ hσ
    rw [FieldEmbedding.map_inv, hx σ hσ]

/-- 固定域成员关系展开为被给定自同构族中的每个元素逐点固定。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=iff.0h5v.s6.cd36d8fe3362 from=translated src=- shape=04c08281 vocab=06e7c5c1
-/
theorem mem_fixedFieldSet_iff
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Set (FieldAutomorphismOver e)) (x : L) :
    x ∈ FixedFieldSet e H ↔ ∀ σ, σ ∈ H → σ.forward x = x := Iff.rfl

/-- 空自同构族不施加固定条件，故其固定域集合是整个目标域。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=eq.0h3v.s5.346aecd7a250 from=translated src=- shape=5968bfa2 vocab=bba07e4a
-/
theorem fixedFieldSet_empty
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    FixedFieldSet e ∅ = Set.univ := by
  ext x
  simp [FixedFieldSet]

/-- 全体基域自同构的固定域成员恰为被每个基域自同构固定的元素。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=iff.0h4v.s6.4868f8886d44 from=translated src=- shape=39919709 vocab=f6db9c2b
-/
theorem mem_fixedFieldSet_univ_iff
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) (x : L) :
    x ∈ FixedFieldSet e Set.univ ↔
      ∀ σ : FieldAutomorphismOver e, σ.forward x = x := by
  simp [FixedFieldSet]

/-- 任意自同构族的共同固定元素对全部域运算封闭，构成子域集合。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=subfield.0h4v.s5.e3e2ef63ea4b from=translated src=- shape=7e7d181c vocab=3b1917af
-/
theorem fixedFieldSet_isSubfield
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Set (FieldAutomorphismOver e)) :
    SubfieldSet (FixedFieldSet e H) :=
  fixedFieldSet_isSubfield_bridge e H

/-- 每个基域自同构都固定所选基域嵌入的全部像。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=le.0h4v.s5.24bff7d6966b from=translated src=- shape=c194c88f vocab=489c1e75
-/
theorem base_range_subset_fixedFieldSet
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Set (FieldAutomorphismOver e)) :
    Set.range e.toFun ⊆ FixedFieldSet e H := by
  rintro _ ⟨x, rfl⟩ σ hσ
  exact σ.fixes_base x

/-- 固定域集合既是目标域的子域，又包含显式基域嵌入的像，因而满足
本库 `IntermediateFieldSet` 教材判据。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=intermed.0h4v.s5.f0e112fa59aa from=translated src=- shape=f2618e85 vocab=5e7de01e
-/
theorem fixedFieldSet_isIntermediateField
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (H : Set (FieldAutomorphismOver e)) :
    IntermediateFieldSet e (FixedFieldSet e H) :=
  ⟨fixedFieldSet_isSubfield e H, base_range_subset_fixedFieldSet e H⟩

/-- 自同构族越大，共同固定元素越少，因此固定域集合随自同构族反变。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=le.1h5v.s6.0ad8664a8ef6 from=translated src=- shape=38cf818d vocab=9301d4ef
-/
theorem fixedFieldSet_antitone
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    {H J : Set (FieldAutomorphismOver e)} (hHJ : H ⊆ J) :
    FixedFieldSet e J ⊆ FixedFieldSet e H := by
  intro x hx σ hσ
  exact hx σ (hHJ hσ)

/-! ## Galois 扩张 -/

/-- **Galois 扩张**：相对于显式嵌入 `e`，扩张同时可分且正规。

> **Entry**: abstract-algebra.field.galois-definitions-/
def GaloisExtension {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : Prop :=
  SeparableExtension e ∧ NormalExtension e

/-- Galois 扩张定义展开为可分扩张与正规扩张的合取。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=iff.0h3v.s5.9951e3f282fe from=translated src=- shape=a74ed316 vocab=df5ce968
-/
theorem galoisExtension_iff
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    GaloisExtension e ↔ SeparableExtension e ∧ NormalExtension e := Iff.rfl

/-- Galois 扩张的可分性投影。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=separabl.1h3v.s4.b42d7826210b from=translated src=- shape=f61ba1fe vocab=d8b34cfb
-/
theorem GaloisExtension.isSeparable
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (h : GaloisExtension e) : SeparableExtension e := h.1

/-- Galois 扩张的正规性投影。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=normalex.1h3v.s4.7c9160071c0f from=translated src=- shape=f61ba1fe vocab=f3824908
-/
theorem GaloisExtension.isNormal
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (h : GaloisExtension e) : NormalExtension e := h.2

/-- Galois 扩张必为代数扩张，这是正规性分量的直接推论。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=algebrai.1h3v.s4.6eb7b9267818 from=translated src=- shape=f61ba1fe vocab=a86eddf4
-/
theorem GaloisExtension.isAlgebraic
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (h : GaloisExtension e) : AlgebraicExtension e := h.isNormal.isAlgebraic

/-- Galois 扩张等价于可分且代数，并且每个在目标域中有根的基域
不可约多项式都在目标域中完全分裂。这是 A3.8 第二批正规性刻画的展开。

> **Entry**: abstract-algebra.field.galois-definitions
@isnad1 id=iff.0h3v.s6.e05756b8b346 from=translated src=- shape=5b42c0de vocab=adf3bb20
-/
theorem galoisExtension_iff_irreducible_with_root_splits
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    GaloisExtension e ↔
      SeparableExtension e ∧ AlgebraicExtension e ∧
        ∀ p : Polynomial K,
          Irreducible p →
            (∃ x : L, evaluateOver e p x = 0) →
              PolynomialSplitsIn e p := by
  rw [GaloisExtension, normalExtension_iff_irreducible_with_root_splits]

end SandronesLibrary.AbstractAlgebra.FieldGaloisDefinitions
