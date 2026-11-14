/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldGaloisDefinitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 抽象代数 / 有限 Galois 基本对应

本模块在 A3.9a 的显式基域自同构、固定域与 Galois 扩张定义之上，建立
有限 Galois 基本定理的集合式教材承载。公开层使用
`IntermediateFieldSet`、`SubgroupSet`、`FixedFieldSet` 与
`FieldAutomorphismOver`，把中间域和自同构子群之间的反变关系写成可直接
计算的集合包含与恢复等式。

证明分为三层。第一层建立固定集合的自同构群与固定域之间的 Galois
connection；第二层为显式中间域构造真实的载体域、基域嵌入、包含嵌入和
restriction，并证明限制与恒等、复合、逆相容；第三层通过换基等价、群的
有限基数与相对扩张次数相等，以及同维包含的消去，分别恢复中间域与
子群。

Mathlib 的 `Algebra`、打包中间域、`AlgEquiv`、有限维与固定点工具只在
私有桥和证明体中充当成熟后端。公开声明保持本库的显式嵌入和集合
谓词；证明不调用直接给出最终恢复结论的现成接口，以保留教材数值链的
真实内容。

本模块止于有限 Galois 基本对应，并只额外导出“全自同构群阶等于总
次数”这一薄数值接口，供后续模块复用已经完成的私有换基。
次数—指数、正规子群、
限制同态的核与像、商群等进一步推论不在本文件内展开。

> **Entry**: abstract-algebra.field.galois-correspondence
-/

namespace SandronesLibrary.AbstractAlgebra.FieldGaloisCorrespondence

open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldDegree
open SandronesLibrary.AbstractAlgebra.FieldSplitting
open SandronesLibrary.AbstractAlgebra.FieldSeparableNormal
open SandronesLibrary.AbstractAlgebra.FieldGaloisDefinitions
open SandronesLibrary.AbstractAlgebra.Group

noncomputable local instance fieldAutomorphismOverGroup
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    Group (FieldAutomorphismOver e) := by
  let h := fieldAutomorphismOver_groupAxioms e
  exact Group.ofLeftAxioms h.mul_assoc h.one_mul h.inv_mul

/-! ## Fixing 自同构集合 -/

/-- 固定集合 `E` 中每个元素的全部显式基域自同构。

> **Entry**: abstract-algebra.field.galois-correspondence-/
def FixingAutomorphismSet {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (E : Set L) :
    Set (FieldAutomorphismOver e) :=
  {σ | ∀ x, x ∈ E → σ.forward x = x}

/-- Fixing 自同构集合的成员关系展开。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem mem_fixingAutomorphismSet_iff
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (E : Set L) (σ : FieldAutomorphismOver e) :
    σ ∈ FixingAutomorphismSet e E ↔
      ∀ x, x ∈ E → σ.forward x = x :=
  Iff.rfl

-- A3.9b-06：固定任意集合的自同构直接组成正式子群。
private noncomputable def fixingAutomorphismSubgroup_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (E : Set L) :
    Subgroup (FieldAutomorphismOver e) :=
  { carrier := FixingAutomorphismSet e E
    one_mem' := by
      intro x hx
      exact fieldAutomorphismOver_identity_apply x
    mul_mem' := by
      intro σ τ hσ hτ x hx
      rw [fieldAutomorphismOver_comp_apply, hτ x hx, hσ x hx]
    inv_mem' := by
      intro σ hσ x hx
      change
        (SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ) x = x
      apply σ.forward.injective
      rw [σ.right_inverse, hσ x hx] }

-- A3.9b-07：集合包含关系诱导 fixing 自同构集合的反向包含。
private theorem fixingAutomorphismSet_antitone_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    {E F : Set L} (hEF : E ⊆ F) :
    FixingAutomorphismSet e F ⊆ FixingAutomorphismSet e E := by
  intro σ hσ x hx
  exact hσ x (hEF hx)

/-- 固定给定集合的自同构构成本库 `SubgroupSet` 意义下的子群集合。
这是从首选正式 fixing 子群 carrier 退回集合式封闭判据的兼容接口；
正式子群本身不再依赖该旧判定定理构造。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem fixingAutomorphismSet_isSubgroup
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (E : Set L) :
    SubgroupSet (FixingAutomorphismSet e E) := by
  change SubgroupSet
    ((fixingAutomorphismSubgroup_bridge e E :
      Subgroup (FieldAutomorphismOver e)) :
      Set (FieldAutomorphismOver e))
  exact (fixingAutomorphismSubgroup_bridge e E).subgroupSet

/-- 固定 `E` 中每个元素的基域自同构所成的 Mathlib 正式子群。
这是后续课程接口首选的子群承载；底层 carrier 仍是教材定义
`FixingAutomorphismSet e E`，因而不引入第二套 fixing 语义。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable def fixingAutomorphismSubgroup
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (E : Set L) :
    Subgroup (FieldAutomorphismOver e) :=
  fixingAutomorphismSubgroup_bridge e E

/-- fixing 正式子群的成员关系就是逐点固定给定集合。这个展开式允许
教材证明直接使用元素条件，而无需展开 `Subgroup` 的实现字段。

> **Entry**: abstract-algebra.field.galois-correspondence-/
@[simp] theorem mem_fixingAutomorphismSubgroup_iff
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (E : Set L)
    (σ : FieldAutomorphismOver e) :
    σ ∈ fixingAutomorphismSubgroup e E ↔
      ∀ x, x ∈ E → σ.forward x = x := by
  change σ ∈ FixingAutomorphismSet e E ↔ _
  exact mem_fixingAutomorphismSet_iff e E σ

/-- fixing 正式子群强制转换回集合后，严格等于原有教材 fixing 集合。
该等式是旧集合接口与首选正式接口之间的 carrier 兼容桥。

> **Entry**: abstract-algebra.field.galois-correspondence-/
@[simp] theorem fixingAutomorphismSubgroup_carrier
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (E : Set L) :
    ((fixingAutomorphismSubgroup e E :
      Subgroup (FieldAutomorphismOver e)) :
      Set (FieldAutomorphismOver e)) = FixingAutomorphismSet e E := by
  rfl

/-- 被要求逐点固定的集合越大，满足条件的基域自同构越少。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem fixingAutomorphismSet_antitone
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    {E F : Set L} (hEF : E ⊆ F) :
    FixingAutomorphismSet e F ⊆ FixingAutomorphismSet e E :=
  fixingAutomorphismSet_antitone_bridge hEF

/-! ## 集合级 Galois connection -/

-- A3.9b-10：域集合包含于固定域等价于自同构族逐点固定该域集合。
private theorem intermediate_subset_fixedFieldSet_iff_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (E : Set L) (H : Set (FieldAutomorphismOver e)) :
    E ⊆ FixedFieldSet e H ↔ H ⊆ FixingAutomorphismSet e E := by
  constructor
  · intro hE σ hσ x hx
    exact hE hx σ hσ
  · intro hH x hx σ hσ
    exact hH hσ x hx

/-- 固定域与 fixing 自同构集合满足反变 Galois connection：`E` 包含于
`H` 的固定域，当且仅当 `H` 中每个自同构逐点固定 `E`。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem intermediate_subset_fixedFieldSet_iff
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (E : Set L) (H : Set (FieldAutomorphismOver e)) :
    E ⊆ FixedFieldSet e H ↔ H ⊆ FixingAutomorphismSet e E :=
  intermediate_subset_fixedFieldSet_iff_bridge E H

/-- 每个集合都包含于“固定该集合的全部自同构”的固定域中。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem subset_fixedFieldSet_fixingAutomorphismSet
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L)
    (E : Set L) :
    E ⊆ FixedFieldSet e (FixingAutomorphismSet e E) :=
  (intermediate_subset_fixedFieldSet_iff E
    (FixingAutomorphismSet e E)).mpr Set.Subset.rfl

/-- 每个自同构族都包含于“其固定域的 fixing 自同构集合”中。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem subset_fixingAutomorphismSet_fixedFieldSet
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L)
    (H : Set (FieldAutomorphismOver e)) :
    H ⊆ FixingAutomorphismSet e (FixedFieldSet e H) :=
  (intermediate_subset_fixedFieldSet_iff (FixedFieldSet e H) H).mp
    Set.Subset.rfl

/-! ## 显式中间域上的 restriction 层 -/

/-- 显式中间域数据由一个目标域子集及其中间域集合证明组成。该结构不把
Mathlib 的打包 `IntermediateField` 暴露给教材 API。

> **Entry**: abstract-algebra.field.galois-correspondence-/
structure ExplicitIntermediateField {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) where
  carrier : Set L
  isIntermediate : IntermediateFieldSet e carrier

/-- 显式中间域的元素载体就是其底层集合对应的子类型。

> **Entry**: abstract-algebra.field.galois-correspondence-/
def IntermediateFieldCarrier {K L : Type*} [Field K] [Field L]
    {e : FieldEmbedding K L} (F : ExplicitIntermediateField e) :=
  {x : L // x ∈ F.carrier}

-- A3.9b-R01：中间域集合的封闭性在子类型上安装完整域结构。
@[instance_reducible]
private noncomputable def intermediateFieldCarrier_field_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) : Field (IntermediateFieldCarrier F) := by
  let S : Subfield L :=
    { carrier := F.carrier
      zero_mem' := F.isIntermediate.1.1.1
      one_mem' := F.isIntermediate.1.1.2.1
      add_mem' := fun {a b} ha hb => F.isIntermediate.1.1.2.2.1 ha hb
      mul_mem' := fun {a b} ha hb => F.isIntermediate.1.1.2.2.2.1 ha hb
      neg_mem' := fun {a} ha => F.isIntermediate.1.1.2.2.2.2 ha
      inv_mem' := fun {a} ha => by
        by_cases ha0 : a = 0
        · simpa [ha0] using F.isIntermediate.1.1.1
        · exact F.isIntermediate.1.2 ha ha0 }
  change Field S
  infer_instance

/-- 显式中间域载体继承目标域运算并构成域。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable instance intermediateFieldCarrierField
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) : Field (IntermediateFieldCarrier F) :=
  intermediateFieldCarrier_field_bridge F

-- A3.9b-R02：基域嵌入的像属于任意显式中间域。
private noncomputable def intermediateFieldBaseEmbedding_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    FieldEmbedding K (IntermediateFieldCarrier F) := by
  refine {
    toFun := fun x => ⟨e x, F.isIntermediate.2 ⟨x, rfl⟩⟩
    map_isRingHomomorphism := ?_
    injective := ?_ }
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact e.map_isRingHomomorphism.1
    · apply Subtype.ext
      exact e.map_isRingHomomorphism.2.1
    · intro a b
      apply Subtype.ext
      exact e.map_isRingHomomorphism.2.2.1 a b
    · intro a b
      apply Subtype.ext
      exact e.map_isRingHomomorphism.2.2.2.1 a b
    · intro a
      apply Subtype.ext
      exact e.map_isRingHomomorphism.2.2.2.2 a
  · intro a b hab
    apply e.injective
    exact congrArg Subtype.val hab

/-- 基域到显式中间域载体的嵌入。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable def intermediateFieldBaseEmbedding
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    FieldEmbedding K (IntermediateFieldCarrier F) :=
  intermediateFieldBaseEmbedding_bridge F

-- A3.9b-R03：显式中间域载体到目标域的包含映射是域嵌入。
private noncomputable def intermediateFieldInclusion_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    FieldEmbedding (IntermediateFieldCarrier F) L := by
  refine {
    toFun := Subtype.val
    map_isRingHomomorphism := ?_
    injective := Subtype.val_injective }
  exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- 显式中间域载体到原目标域的自然包含嵌入。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable def intermediateFieldInclusion
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    FieldEmbedding (IntermediateFieldCarrier F) L :=
  intermediateFieldInclusion_bridge F

-- A3.9b-R03A：基域嵌入经中间域载体包含回目标域后逐点不变。
private theorem intermediateFieldBaseEmbedding_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (x : K) :
    intermediateFieldInclusion F (intermediateFieldBaseEmbedding F x) = e x := by
  rfl

/-- 基域嵌入在中间域载体中计算后再包含回 `L`，等于原嵌入。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem intermediateFieldBaseEmbedding_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (x : K) :
    intermediateFieldInclusion F (intermediateFieldBaseEmbedding F x) = e x :=
  intermediateFieldBaseEmbedding_apply_bridge F x

/-- 自同构正逆均保持显式中间域集合。两个方向都显式记录，以便限制后
仍能构造互逆的域嵌入。

> **Entry**: abstract-algebra.field.galois-correspondence-/
def PreservesIntermediateField
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (σ : FieldAutomorphismOver e) (F : ExplicitIntermediateField e) : Prop :=
  (∀ x, x ∈ F.carrier → σ.forward x ∈ F.carrier) ∧
    (∀ x, x ∈ F.carrier →
      SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ x ∈
        F.carrier)

-- A3.9b-R04：保持中间域的自同构正向映射可限制到中间域载体。
private noncomputable def restrictEmbedding_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    FieldEmbedding (IntermediateFieldCarrier F) (IntermediateFieldCarrier F) := by
  refine {
    toFun := fun x => ⟨σ.forward x.val, hσ.1 x.val x.property⟩
    map_isRingHomomorphism := ?_
    injective := ?_ }
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact σ.forward.map_isRingHomomorphism.1
    · apply Subtype.ext
      exact σ.forward.map_isRingHomomorphism.2.1
    · intro a b
      apply Subtype.ext
      exact σ.forward.map_isRingHomomorphism.2.2.1 a.val b.val
    · intro a b
      apply Subtype.ext
      exact σ.forward.map_isRingHomomorphism.2.2.2.1 a.val b.val
    · intro a
      apply Subtype.ext
      exact σ.forward.map_isRingHomomorphism.2.2.2.2 a.val
  · intro a b hab
    apply Subtype.ext
    apply σ.forward.injective
    exact congrArg Subtype.val hab

/-- 将保持显式中间域的基域自同构限制为该载体上的域嵌入。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable def restrictEmbedding
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    FieldEmbedding (IntermediateFieldCarrier F) (IntermediateFieldCarrier F) :=
  restrictEmbedding_bridge F σ hσ

-- A3.9b-R04A：限制嵌入的底层值与原正向映射对齐。
private theorem restrictEmbedding_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (x : IntermediateFieldCarrier F) :
    (restrictEmbedding F σ hσ x).val = σ.forward x.val := by
  rfl

/-- 限制嵌入逐点等于原自同构的正向映射。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem restrictEmbedding_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (x : IntermediateFieldCarrier F) :
    (restrictEmbedding F σ hσ x).val = σ.forward x.val :=
  restrictEmbedding_apply_bridge F σ hσ x

-- A3.9b-R05：恒等自同构保持每个显式中间域。
private theorem identity_preservesIntermediateField_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    PreservesIntermediateField (1 : FieldAutomorphismOver e) F := by
  constructor
  · intro x hx
    exact hx
  · intro x hx
    exact hx

-- A3.9b-R06：两个保持中间域的自同构之复合仍保持该中间域。
private theorem comp_preservesIntermediateField_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ τ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (hτ : PreservesIntermediateField τ F) :
    PreservesIntermediateField (σ * τ) F := by
  constructor
  · intro x hx
    exact hσ.1 _ (hτ.1 _ hx)
  · intro x hx
    exact hτ.2 _ (hσ.2 _ hx)

-- A3.9b-R07：保持中间域的自同构之逆仍保持该中间域。
private theorem inverse_preservesIntermediateField_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    PreservesIntermediateField σ⁻¹ F := by
  exact ⟨hσ.2, hσ.1⟩

/-- 恒等自同构保持任意显式中间域。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem identity_preservesIntermediateField
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    PreservesIntermediateField (1 : FieldAutomorphismOver e) F :=
  identity_preservesIntermediateField_bridge F

/-- 保持显式中间域的性质对自同构复合封闭。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem comp_preservesIntermediateField
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ τ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (hτ : PreservesIntermediateField τ F) :
    PreservesIntermediateField (σ * τ) F :=
  comp_preservesIntermediateField_bridge F σ τ hσ hτ

/-- 保持显式中间域的性质对自同构取逆封闭。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem inverse_preservesIntermediateField
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    PreservesIntermediateField σ⁻¹ F :=
  inverse_preservesIntermediateField_bridge F σ hσ

-- A3.9b-R07A：恒等自同构的限制嵌入逐点为恒等。
private theorem restrictEmbedding_identity_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (x : IntermediateFieldCarrier F) :
    restrictEmbedding F 1 (identity_preservesIntermediateField F) x = x := by
  apply Subtype.ext
  rw [restrictEmbedding_apply, fieldAutomorphismOver_identity_apply]

-- A3.9b-R07B：复合自同构的限制嵌入逐点等于限制嵌入的复合。
private theorem restrictEmbedding_comp_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ τ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (hτ : PreservesIntermediateField τ F)
    (x : IntermediateFieldCarrier F) :
    restrictEmbedding F (σ * τ)
      (comp_preservesIntermediateField F σ τ hσ hτ) x =
        restrictEmbedding F σ hσ (restrictEmbedding F τ hτ x) := by
  apply Subtype.ext
  rw [restrictEmbedding_apply, fieldAutomorphismOver_comp_apply]
  rw [restrictEmbedding_apply, restrictEmbedding_apply]

/-- 恒等自同构的限制嵌入逐点为恒等。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem restrictEmbedding_identity_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (x : IntermediateFieldCarrier F) :
    restrictEmbedding F 1 (identity_preservesIntermediateField F) x = x :=
  restrictEmbedding_identity_apply_bridge F x

/-- 限制嵌入与自同构复合逐点相容。结论不比较封闭性证明参数。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem restrictEmbedding_comp_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ τ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (hτ : PreservesIntermediateField τ F)
    (x : IntermediateFieldCarrier F) :
    restrictEmbedding F (σ * τ)
      (comp_preservesIntermediateField F σ τ hσ hτ) x =
        restrictEmbedding F σ hσ (restrictEmbedding F τ hτ x) :=
  restrictEmbedding_comp_apply_bridge F σ τ hσ hτ x

-- A3.9b-R08：正逆限制嵌入组装为中间域载体上的基域自同构。
private noncomputable def restrictAutomorphism_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    FieldAutomorphismOver (intermediateFieldBaseEmbedding F) := by
  refine {
    forward := restrictEmbedding F σ hσ
    inverse := restrictEmbedding F σ⁻¹
      (inverse_preservesIntermediateField F σ hσ)
    left_inverse := ?_
    right_inverse := ?_
    fixes_base := ?_ }
  · intro x
    apply Subtype.ext
    rw [restrictEmbedding_apply, restrictEmbedding_apply]
    exact σ.left_inverse x.val
  · intro x
    apply Subtype.ext
    rw [restrictEmbedding_apply, restrictEmbedding_apply]
    exact σ.right_inverse x.val
  · intro x
    apply Subtype.ext
    rw [restrictEmbedding_apply]
    exact σ.fixes_base x

/-- 保持中间域的自同构限制为该中间域载体上的基域自同构。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable def restrictAutomorphism
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    FieldAutomorphismOver (intermediateFieldBaseEmbedding F) :=
  restrictAutomorphism_bridge F σ hσ

-- A3.9b-R08A：限制自同构的正向底层值与原正向映射对齐。
private theorem restrictAutomorphism_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (x : IntermediateFieldCarrier F) :
    ((restrictAutomorphism F σ hσ).forward x).val = σ.forward x.val := by
  exact restrictEmbedding_apply F σ hσ x

/-- 限制自同构逐点等于原自同构的正向映射。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem restrictAutomorphism_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (x : IntermediateFieldCarrier F) :
    ((restrictAutomorphism F σ hσ).forward x).val = σ.forward x.val :=
  restrictAutomorphism_apply_bridge F σ hσ x

-- A3.9b-R09：恒等自同构的限制逐点仍为恒等。
private theorem restrictAutomorphism_identity_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (x : IntermediateFieldCarrier F) :
    (restrictAutomorphism F 1 (identity_preservesIntermediateField F)).forward x = x := by
  apply Subtype.ext
  rw [restrictAutomorphism_apply, fieldAutomorphismOver_identity_apply]

-- A3.9b-R10：复合自同构的限制逐点等于两个限制的复合。
private theorem restrictAutomorphism_comp_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ τ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (hτ : PreservesIntermediateField τ F)
    (x : IntermediateFieldCarrier F) :
    (restrictAutomorphism F (σ * τ)
      (comp_preservesIntermediateField F σ τ hσ hτ)).forward x =
        ((restrictAutomorphism F σ hσ) *
          (restrictAutomorphism F τ hτ)).forward x := by
  apply Subtype.ext
  rw [restrictAutomorphism_apply, fieldAutomorphismOver_comp_apply]
  rw [fieldAutomorphismOver_comp_apply]
  rw [restrictAutomorphism_apply, restrictAutomorphism_apply]

-- A3.9b-R11：逆自同构的限制逐点等于限制自同构的逆。
private theorem restrictAutomorphism_inverse_apply_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (x : IntermediateFieldCarrier F) :
    (restrictAutomorphism F σ⁻¹
      (inverse_preservesIntermediateField F σ hσ)).forward x =
        ((restrictAutomorphism F σ hσ)⁻¹).forward x := by
  rfl

/-- 恒等自同构的限制逐点为恒等。证明参数可能不同，因此采用教材所需的
逐点等式而不伪造依赖证明之间的结构相等。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem restrictAutomorphism_identity_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (x : IntermediateFieldCarrier F) :
    (restrictAutomorphism F 1 (identity_preservesIntermediateField F)).forward x = x :=
  restrictAutomorphism_identity_apply_bridge F x

/-- 限制与自同构复合相容，结论采用逐点等式以屏蔽封闭性证明参数。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem restrictAutomorphism_comp_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ τ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (hτ : PreservesIntermediateField τ F)
    (x : IntermediateFieldCarrier F) :
    (restrictAutomorphism F (σ * τ)
      (comp_preservesIntermediateField F σ τ hσ hτ)).forward x =
        ((restrictAutomorphism F σ hσ) *
          (restrictAutomorphism F τ hτ)).forward x :=
  restrictAutomorphism_comp_apply_bridge F σ τ hσ hτ x

/-- 限制与自同构取逆相容，结论采用逐点等式。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem restrictAutomorphism_inverse_apply
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) (x : IntermediateFieldCarrier F) :
    (restrictAutomorphism F σ⁻¹
      (inverse_preservesIntermediateField F σ hσ)).forward x =
        ((restrictAutomorphism F σ hσ)⁻¹).forward x :=
  restrictAutomorphism_inverse_apply_bridge F σ hσ x

-- A3.9b-R12：逐点固定中间域集合必然同时保持正向与逆向。
private theorem fixing_preservesIntermediateField_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hfix : σ ∈ FixingAutomorphismSet e F.carrier) :
    PreservesIntermediateField σ F := by
  constructor
  · intro x hx
    rw [hfix x hx]
    exact hx
  · intro x hx
    have hinverse :
        SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ x =
          x := by
      apply σ.forward.injective
      rw [σ.right_inverse, hfix x hx]
    rw [hinverse]
    exact hx

-- A3.9b-R13：在给定保持性证明后，逐点固定等价于限制自同构为恒等。
private theorem fixing_iff_restrictAutomorphism_eq_identity_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    σ ∈ FixingAutomorphismSet e F.carrier ↔
      restrictAutomorphism F σ hσ =
        (1 : FieldAutomorphismOver (intermediateFieldBaseEmbedding F)) := by
  constructor
  · intro hfix
    apply FieldAutomorphismOver.ext
    intro x
    apply Subtype.ext
    rw [restrictAutomorphism_apply, hfix x.val x.property,
      fieldAutomorphismOver_identity_apply]
  · intro heq x hx
    let y : IntermediateFieldCarrier F := ⟨x, hx⟩
    have hpoint := congrArg (fun τ => τ.forward y) heq
    have hval := congrArg Subtype.val hpoint
    rw [restrictAutomorphism_apply, fieldAutomorphismOver_identity_apply] at hval
    exact hval

/-- 逐点固定显式中间域的自同构必然保持该中间域。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem fixing_preservesIntermediateField
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hfix : σ ∈ FixingAutomorphismSet e F.carrier) :
    PreservesIntermediateField σ F :=
  fixing_preservesIntermediateField_bridge F σ hfix

/-- 对任意给定的保持性证明，自同构逐点固定显式中间域，当且仅当它在
该载体上的限制自同构等于恒等。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem fixing_iff_restrictAutomorphism_eq_identity
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : PreservesIntermediateField σ F) :
    σ ∈ FixingAutomorphismSet e F.carrier ↔
      restrictAutomorphism F σ hσ =
        (1 : FieldAutomorphismOver (intermediateFieldBaseEmbedding F)) :=
  fixing_iff_restrictAutomorphism_eq_identity_bridge F σ hσ

/-! ## 有限扩张中的两个恢复方向 -/

private def fieldAutomorphismOver_mathlibAlgEquiv_equiv
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FieldAutomorphismOver e ≃ (L ≃ₐ[K] L) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let toMathlib : FieldAutomorphismOver e → (L ≃ₐ[K] L) := fun σ =>
    { toFun := σ.forward
      invFun :=
        SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ
      left_inv := σ.left_inverse
      right_inv := σ.right_inverse
      map_add' := σ.forward.map_isRingHomomorphism.2.2.1
      map_mul' := σ.forward.map_isRingHomomorphism.2.2.2.1
      commutes' := σ.fixes_base }
  let fromMathlib : (L ≃ₐ[K] L) → FieldAutomorphismOver e := fun σ =>
    { forward :=
        { toFun := σ
          map_isRingHomomorphism :=
            ⟨σ.map_zero, σ.map_one, σ.map_add, σ.map_mul, σ.map_neg⟩
          injective := σ.injective }
      inverse :=
        { toFun := σ.symm
          map_isRingHomomorphism :=
            ⟨σ.symm.map_zero, σ.symm.map_one, σ.symm.map_add,
              σ.symm.map_mul, σ.symm.map_neg⟩
          injective := σ.symm.injective }
      left_inverse := σ.symm_apply_apply
      right_inverse := σ.apply_symm_apply
      fixes_base := σ.commutes }
  refine {
    toFun := toMathlib
    invFun := fromMathlib
    left_inv := ?_
    right_inv := ?_ }
  · intro σ
    apply FieldAutomorphismOver.ext
    intro x
    rfl
  · intro σ
    apply AlgEquiv.ext
    intro x
    rfl

-- A3.9b-01：显式自同构在由 `e` 诱导的 Algebra 后端中对应 Mathlib AlgEquiv。

/-- 显式基域自同构群与由同一嵌入诱导的 Mathlib `AlgEquiv` 群乘法等价。
这是正规子群、限制同态和商群推论共用的正式桥；后续模块不应再次构造
相同的正逆映射。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable def fieldAutomorphismOver_mathlibAlgEquiv_mulEquiv
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FieldAutomorphismOver e ≃* (L ≃ₐ[K] L) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  refine
    { toEquiv := fieldAutomorphismOver_mathlibAlgEquiv_equiv e
      map_mul' := ?_ }
  intro σ τ
  apply AlgEquiv.ext
  intro x
  rfl

-- A3.9b-02：显式中间域集合可承载为具有相同底层集合的 Mathlib 中间域。
private theorem subgroup_mathlibSubgroup_bridge
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L)
    (H : Subgroup (FieldAutomorphismOver e)) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    ∃ G : Subgroup (L ≃ₐ[K] L),
      ∃ φ : FieldAutomorphismOver e ≃ (L ≃ₐ[K] L),
        φ '' (H : Set (FieldAutomorphismOver e)) =
            (G : Set (L ≃ₐ[K] L)) ∧
          ∀ σ x, φ σ x = σ.forward x := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let φ := fieldAutomorphismOver_mathlibAlgEquiv_equiv e
  let G : Subgroup (L ≃ₐ[K] L) :=
    { carrier := φ '' (H : Set (FieldAutomorphismOver e))
      one_mem' := by
        refine ⟨1, H.one_mem, ?_⟩
        apply AlgEquiv.ext
        intro x
        rfl
      mul_mem' := by
        rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
        refine ⟨σ * τ, H.mul_mem hσ hτ, ?_⟩
        apply AlgEquiv.ext
        intro x
        rfl
      inv_mem' := by
        rintro _ ⟨σ, hσ, rfl⟩
        refine ⟨σ⁻¹, H.inv_mem hσ, ?_⟩
        apply AlgEquiv.ext
        intro x
        rfl }
  refine ⟨G, φ, rfl, ?_⟩
  intro σ x
  rfl

-- A3.9b-04：本库有限扩张见证在局部 Algebra 后端给出有限维实例。
private theorem finiteFieldExtension_mathlibFiniteDimensional_bridge
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FiniteFieldExtension e → Nonempty (FiniteDimensional K L) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rintro ⟨n, b, hb⟩
  have hsum (c : Fin n → K) :
      fieldLinearCombination e Finset.univ c b = ∑ i, c i • b i := by
    simp only [fieldLinearCombination, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, FieldEmbedding.toRingHom]
    rfl
  have hli : LinearIndependent K b := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    apply hb.1 c
    rw [hsum]
    exact hc
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨c, hc⟩ := hb.2 x
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨c, ?_⟩
    rw [← hsum]
    exact hc
  let B : Module.Basis (Fin n) K L := Module.Basis.mk hli hspan.ge
  exact ⟨Module.Finite.of_basis B⟩

-- A3.9b-08：显式 Galois 条件在局部 Algebra 后端给出 Mathlib IsGalois 实例。
private theorem galoisExtension_mathlibIsGalois_bridge
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    GaloisExtension e → Nonempty (IsGalois K L) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rintro ⟨hsep, hnormal⟩
  exact ⟨isGalois_iff.mpr
    ⟨(separableExtension_iff_mathlibIsSeparable e).mp hsep,
      (normalExtension_iff_mathlibNormal e).mp hnormal⟩⟩

/-- 本库有限 Galois 假设可一次性安装为 Mathlib 的有限维和 `IsGalois`
证明对象。该后端包只供后续证明局部使用，不改变公开教材谓词。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_mathlibBackend
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) (hgal : GaloisExtension e) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    Nonempty (FiniteDimensional K L) ∧ Nonempty (IsGalois K L) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact ⟨finiteFieldExtension_mathlibFiniteDimensional_bridge e hfin,
    galoisExtension_mathlibIsGalois_bridge e hgal⟩

-- A3.9b-09：Mathlib 固定域与 fixing 子群经载体转换后对齐本库两个集合。
private noncomputable def fixedFieldExplicitIntermediate_bridge
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L)
    (H : Set (FieldAutomorphismOver e)) : ExplicitIntermediateField e := by
  exact ⟨FixedFieldSet e H, fixedFieldSet_isIntermediateField e H⟩

-- A3.9b-N02：显式中间域经 fixing 后再取固定域所得闭包。
private noncomputable def fixingClosureExplicitIntermediate_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) : ExplicitIntermediateField e := by
  exact ⟨FixedFieldSet e (FixingAutomorphismSet e F.carrier),
    fixedFieldSet_isIntermediateField e (FixingAutomorphismSet e F.carrier)⟩

-- A3.9b-N03：中间域与 fixing 闭包拥有相同的 fixing 自同构集合。
private theorem fixing_eq_fixingClosure_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    FixingAutomorphismSet e F.carrier =
      FixingAutomorphismSet e
        (fixingClosureExplicitIntermediate_bridge F).carrier := by
  apply Set.Subset.antisymm
  · exact subset_fixingAutomorphismSet_fixedFieldSet e
      (FixingAutomorphismSet e F.carrier)
  · apply fixingAutomorphismSet_antitone
    exact subset_fixedFieldSet_fixingAutomorphismSet e F.carrier

-- A3.9b-N04：有限 Galois 情形下，fixing 自同构的基数等于相应相对次数。
-- A3.9b-C01：固定 `F` 的基域自同构改视为 `L/F` 的显式自同构。
private noncomputable def fixingAutomorphism_to_relative_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (σ : FieldAutomorphismOver e)
    (hσ : σ ∈ FixingAutomorphismSet e F.carrier) :
    FieldAutomorphismOver (intermediateFieldInclusion F) := by
  refine {
    forward := σ.forward
    inverse :=
      SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse σ
    left_inverse := σ.left_inverse
    right_inverse := σ.right_inverse
    fixes_base := ?_ }
  intro x
  change σ.forward x.val = x.val
  exact hσ x.val x.property

-- A3.9b-C02：忘掉较大基域，并记录所得 `K`-自同构逐点固定 `F`。
private noncomputable def relativeAutomorphism_to_fixing_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e)
    (τ : FieldAutomorphismOver (intermediateFieldInclusion F)) :
    {σ : FieldAutomorphismOver e //
      σ ∈ FixingAutomorphismSet e F.carrier} := by
  let σ : FieldAutomorphismOver e :=
    { forward := τ.forward
      inverse :=
        SandronesLibrary.AbstractAlgebra.FieldSplitting.FieldIsomorphismOver.inverse τ
      left_inverse := τ.left_inverse
      right_inverse := τ.right_inverse
      fixes_base := fun x => by
        have hx := τ.fixes_base (intermediateFieldBaseEmbedding F x)
        simpa only [intermediateFieldBaseEmbedding_apply] using hx }
  refine ⟨σ, ?_⟩
  intro x hx
  let y : IntermediateFieldCarrier F := ⟨x, hx⟩
  have hy := τ.fixes_base y
  exact hy

-- A3.9b-C03：上述换基与忘却构造互逆。
private noncomputable def fixingAutomorphism_relative_equiv_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    {σ : FieldAutomorphismOver e //
      σ ∈ FixingAutomorphismSet e F.carrier} ≃
        FieldAutomorphismOver (intermediateFieldInclusion F) := by
  refine {
    toFun := fun σ => fixingAutomorphism_to_relative_bridge F σ.val σ.property
    invFun := relativeAutomorphism_to_fixing_bridge F
    left_inv := ?_
    right_inv := ?_ }
  · intro σ
    apply Subtype.ext
    apply FieldAutomorphismOver.ext
    intro x
    rfl
  · intro τ
    apply FieldAutomorphismOver.ext
    intro x
    rfl

-- A3.9b-C04：显式 `Gal(L/F)` 与 Mathlib 自同构对齐，并记录逐点一致性。
private theorem relativeAutomorphism_mathlibAlgEquiv_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    letI : Algebra (IntermediateFieldCarrier F) L :=
      (intermediateFieldInclusion F).toRingHom.toAlgebra
    ∃ φ : FieldAutomorphismOver (intermediateFieldInclusion F) ≃
        (L ≃ₐ[IntermediateFieldCarrier F] L),
      ∀ σ x, φ σ x = σ.forward x := by
  let _ : Algebra (IntermediateFieldCarrier F) L :=
    (intermediateFieldInclusion F).toRingHom.toAlgebra
  let φ := fieldAutomorphismOver_mathlibAlgEquiv_equiv
    (intermediateFieldInclusion F)
  refine ⟨φ, ?_⟩
  intro σ x
  rfl

-- A3.9b-C05：有限 Galois 扩张沿中间域向上仍有限且 Galois。
private theorem relative_finiteDimensional_isGalois_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (F : ExplicitIntermediateField e) :
    letI : Algebra (IntermediateFieldCarrier F) L :=
      (intermediateFieldInclusion F).toRingHom.toAlgebra
    Nonempty (FiniteDimensional (IntermediateFieldCarrier F) L) ∧
      Nonempty (IsGalois (IntermediateFieldCarrier F) L) := by
  let _ : Algebra K (IntermediateFieldCarrier F) :=
    (intermediateFieldBaseEmbedding F).toRingHom.toAlgebra
  let _ : Algebra (IntermediateFieldCarrier F) L :=
    (intermediateFieldInclusion F).toRingHom.toAlgebra
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let _ : IsScalarTower K (IntermediateFieldCarrier F) L := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      RingHom.algebraMap_toAlgebra]
    apply RingHom.ext
    intro x
    exact intermediateFieldBaseEmbedding_apply F x
  let _ : FiniteDimensional K L :=
    Classical.choice (finiteFieldExtension_mathlibFiniteDimensional_bridge e hfin)
  let _ : IsGalois K L :=
    Classical.choice (galoisExtension_mathlibIsGalois_bridge e hgal)
  have hfd : FiniteDimensional (IntermediateFieldCarrier F) L :=
    FiniteDimensional.right K (IntermediateFieldCarrier F) L
  have hgalois : IsGalois (IntermediateFieldCarrier F) L :=
    IsGalois.tower_top_of_isGalois K (IntermediateFieldCarrier F) L
  exact ⟨⟨hfd⟩, ⟨hgalois⟩⟩

-- A3.9b-C06：显式相对次数与 Mathlib `finrank` 对齐。
private theorem relative_hasExtensionDegree_iff_finrank_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) (n : ℕ) :
    letI : Algebra (IntermediateFieldCarrier F) L :=
      (intermediateFieldInclusion F).toRingHom.toAlgebra
    FiniteDimensional (IntermediateFieldCarrier F) L →
      (HasExtensionDegree (intermediateFieldInclusion F) n ↔
        Module.finrank (IntermediateFieldCarrier F) L = n) := by
  let _ : Algebra (IntermediateFieldCarrier F) L :=
    (intermediateFieldInclusion F).toRingHom.toAlgebra
  intro hfd
  let _ : FiniteDimensional (IntermediateFieldCarrier F) L := hfd
  let j := intermediateFieldInclusion F
  have hsum (v : Fin n → L) (c : Fin n → IntermediateFieldCarrier F) :
      fieldLinearCombination j Finset.univ c v = ∑ i, c i • v i := by
    simp only [fieldLinearCombination, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, FieldEmbedding.toRingHom]
    rfl
  constructor
  · rintro ⟨v, hv⟩
    have hli : LinearIndependent (IntermediateFieldCarrier F) v := by
      apply Fintype.linearIndependent_iff.mpr
      intro c hc i
      apply hv.1 c
      rw [hsum]
      exact hc
    have hspan : Submodule.span (IntermediateFieldCarrier F) (Set.range v) = ⊤ := by
      apply top_unique
      intro x hx
      obtain ⟨c, hc⟩ := hv.2 x
      apply (Submodule.mem_span_range_iff_exists_fun
        (IntermediateFieldCarrier F)).mpr
      refine ⟨c, ?_⟩
      rw [← hsum]
      exact hc
    let B : Module.Basis (Fin n) (IntermediateFieldCarrier F) L :=
      Module.Basis.mk hli hspan.ge
    simpa using Module.finrank_eq_card_basis B
  · intro hrank
    let B : Module.Basis (Fin n) (IntermediateFieldCarrier F) L :=
      Module.finBasisOfFinrankEq (IntermediateFieldCarrier F) L hrank
    refine ⟨fun i => B i, ?_, ?_⟩
    · intro c hc i
      apply Fintype.linearIndependent_iff.mp B.linearIndependent c
      rw [← hsum]
      exact hc
    · intro x
      have hx : x ∈ Submodule.span (IntermediateFieldCarrier F)
          (Set.range fun i => B i) := by
        rw [B.span_eq]
        trivial
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun
          (IntermediateFieldCarrier F)).mp hx
      refine ⟨c, ?_⟩
      rw [hsum]
      exact hc

private theorem fixing_card_eq_relativeDegree_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (F : ExplicitIntermediateField e) :
    ∃ n : ℕ,
      HasExtensionDegree (intermediateFieldInclusion F) n ∧
        Nat.card {σ : FieldAutomorphismOver e //
          σ ∈ FixingAutomorphismSet e F.carrier} = n := by
  let _ : Algebra (IntermediateFieldCarrier F) L :=
    (intermediateFieldInclusion F).toRingHom.toAlgebra
  obtain ⟨hfd, hgalois⟩ :=
    relative_finiteDimensional_isGalois_bridge e hfin hgal F
  let _ : FiniteDimensional (IntermediateFieldCarrier F) L :=
    Classical.choice hfd
  let _ : IsGalois (IntermediateFieldCarrier F) L :=
    Classical.choice hgalois
  let n := Module.finrank (IntermediateFieldCarrier F) L
  have hdegree : HasExtensionDegree (intermediateFieldInclusion F) n :=
    (relative_hasExtensionDegree_iff_finrank_bridge F n
      (inferInstance : FiniteDimensional (IntermediateFieldCarrier F) L)).mpr rfl
  let ψ := fixingAutomorphism_relative_equiv_bridge F
  obtain ⟨φ, hφ⟩ := relativeAutomorphism_mathlibAlgEquiv_bridge F
  have hcardψ : Nat.card {σ : FieldAutomorphismOver e //
      σ ∈ FixingAutomorphismSet e F.carrier} =
      Nat.card (FieldAutomorphismOver (intermediateFieldInclusion F)) :=
    Nat.card_congr ψ
  have hcardφ : Nat.card (FieldAutomorphismOver (intermediateFieldInclusion F)) =
      Nat.card (L ≃ₐ[IntermediateFieldCarrier F] L) :=
    Nat.card_congr φ
  have hcardMathlib : Nat.card (L ≃ₐ[IntermediateFieldCarrier F] L) = n :=
    IsGalois.card_aut_eq_finrank (IntermediateFieldCarrier F) L
  exact ⟨n, hdegree, hcardψ.trans (hcardφ.trans hcardMathlib)⟩

-- A3.9b-N05：中间域与 fixing 闭包到 `L` 的扩张具有同一有限次数。
private theorem hasExtensionDegree_mathlibBasis_bridge
    {A B : Type*} [Field A] [Field B] (j : FieldEmbedding A B)
    (n : ℕ) (h : HasExtensionDegree j n) :
    letI : Algebra A B := j.toRingHom.toAlgebra
    Nonempty (Module.Basis (Fin n) A B) := by
  let _ : Algebra A B := j.toRingHom.toAlgebra
  obtain ⟨v, hv⟩ := h
  have hsum (c : Fin n → A) :
      fieldLinearCombination j Finset.univ c v = ∑ i, c i • v i := by
    simp only [fieldLinearCombination, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, FieldEmbedding.toRingHom]
    rfl
  have hli : LinearIndependent A v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    apply hv.1 c
    rw [hsum]
    exact hc
  have hspan : Submodule.span A (Set.range v) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨c, hc⟩ := hv.2 x
    apply (Submodule.mem_span_range_iff_exists_fun A).mpr
    refine ⟨c, ?_⟩
    rw [← hsum]
    exact hc
  exact ⟨Module.Basis.mk hli hspan.ge⟩

private theorem intermediate_carrier_eq_of_subset_sameDegree_bridge
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F G : ExplicitIntermediateField e) (hFG : F.carrier ⊆ G.carrier)
    (n : ℕ) (hF : HasExtensionDegree (intermediateFieldInclusion F) n)
    (hG : HasExtensionDegree (intermediateFieldInclusion G) n) :
    F.carrier = G.carrier := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let MF : IntermediateField K L :=
    { carrier := F.carrier
      zero_mem' := F.isIntermediate.1.1.1
      one_mem' := F.isIntermediate.1.1.2.1
      add_mem' := fun {a b} ha hb => F.isIntermediate.1.1.2.2.1 ha hb
      mul_mem' := fun {a b} ha hb => F.isIntermediate.1.1.2.2.2.1 ha hb
      algebraMap_mem' := fun x => F.isIntermediate.2 ⟨x, rfl⟩
      inv_mem' := fun x hx => by
        by_cases hx0 : x = 0
        · simpa [hx0] using F.isIntermediate.1.1.1
        · exact F.isIntermediate.1.2 hx hx0 }
  let MG : IntermediateField K L :=
    { carrier := G.carrier
      zero_mem' := G.isIntermediate.1.1.1
      one_mem' := G.isIntermediate.1.1.2.1
      add_mem' := fun {a b} ha hb => G.isIntermediate.1.1.2.2.1 ha hb
      mul_mem' := fun {a b} ha hb => G.isIntermediate.1.1.2.2.2.1 ha hb
      algebraMap_mem' := fun x => G.isIntermediate.2 ⟨x, rfl⟩
      inv_mem' := fun x hx => by
        by_cases hx0 : x = 0
        · simpa [hx0] using G.isIntermediate.1.1.1
        · exact G.isIntermediate.1.2 hx hx0 }
  have hle : MF ≤ MG := hFG
  let _ : Field MF := intermediateFieldCarrierField F
  let _ : Field MG := intermediateFieldCarrierField G
  let _ : Algebra MF L := (intermediateFieldInclusion F).toRingHom.toAlgebra
  let _ : Algebra MG L := (intermediateFieldInclusion G).toRingHom.toAlgebra
  let BF : Module.Basis (Fin n) MF L := Classical.choice
    (hasExtensionDegree_mathlibBasis_bridge
      (intermediateFieldInclusion F) n hF)
  let BG : Module.Basis (Fin n) MG L := Classical.choice
    (hasExtensionDegree_mathlibBasis_bridge
      (intermediateFieldInclusion G) n hG)
  let _ : FiniteDimensional MF L := Module.Finite.of_basis BF
  have hfinrankF : Module.finrank MF L = n := by
    simpa [BF] using Module.finrank_eq_card_basis BF
  have hfinrankG : Module.finrank MG L = n := by
    simpa [BG] using Module.finrank_eq_card_basis BG
  have hfields : MF = MG :=
    IntermediateField.eq_of_le_of_finrank_eq' hle
      (hfinrankF.trans hfinrankG.symm)
  exact congrArg (fun P : IntermediateField K L => (P : Set L)) hfields

-- A3.9b-N07：有限扩张中，子群与其固定域 fixing 闭包具有相同基数。
-- A3.9b-D01：本库 `H` 子类型经载体对齐等价于 Mathlib 子群子类型。
private noncomputable def subgroupSubtype_mathlibSubgroup_equiv_bridge
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    ∀ (H : Subgroup (FieldAutomorphismOver e))
      (G : Subgroup (L ≃ₐ[K] L))
      (φ : FieldAutomorphismOver e ≃ (L ≃ₐ[K] L)),
      φ '' (H : Set (FieldAutomorphismOver e)) =
          (G : Set (L ≃ₐ[K] L)) →
        H ≃ G := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  intro H G φ hG
  refine {
    toFun := fun σ => ⟨φ σ.val, ?_⟩
    invFun := fun g => ⟨φ.symm g.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · change φ σ.val ∈ (G : Set (L ≃ₐ[K] L))
    rw [← hG]
    exact ⟨σ.val, σ.property, rfl⟩
  · have hg : g.val ∈ φ '' (H : Set (FieldAutomorphismOver e)) := by
      rw [hG]
      exact g.property
    obtain ⟨σ, hσ, hφσ⟩ := hg
    have heq : φ.symm g.val = σ := by
      apply φ.injective
      simpa using hφσ.symm
    rwa [heq]
  · intro σ
    apply Subtype.ext
    exact φ.symm_apply_apply σ.val
  · intro g
    apply Subtype.ext
    exact φ.apply_symm_apply g.val

-- A3.9b-D02：fixing-fixed 子类型与 Mathlib fixingSubgroup-fixedField 对齐。
private noncomputable def fixingFixedSubtype_mathlib_equiv_bridge
    {K L : Type*} [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    ∀ (H : Subgroup (FieldAutomorphismOver e))
      (G : Subgroup (L ≃ₐ[K] L))
      (φ : FieldAutomorphismOver e ≃ (L ≃ₐ[K] L))
      (_hG : φ '' (H : Set (FieldAutomorphismOver e)) =
        (G : Set (L ≃ₐ[K] L)))
      (_hφ : ∀ σ x, φ σ x = σ.forward x),
      fixingAutomorphismSubgroup e
          (FixedFieldSet e (H : Set (FieldAutomorphismOver e))) ≃
          IntermediateField.fixingSubgroup (IntermediateField.fixedField G) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  intro H G φ hG hφ
  refine {
    toFun := fun σ => ⟨φ σ.val, ?_⟩
    invFun := fun g => ⟨φ.symm g.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxours : x ∈
        FixedFieldSet e (H : Set (FieldAutomorphismOver e)) := by
      intro ρ hρ
      have hφρ : φ ρ ∈ G := by
        change φ ρ ∈ (G : Set (L ≃ₐ[K] L))
        rw [← hG]
        exact ⟨ρ, hρ, rfl⟩
      rw [IntermediateField.mem_fixedField_iff] at hx
      rw [← hφ]
      exact hx (φ ρ) hφρ
    rw [hφ]
    exact σ.property x hxours
  · intro x hx
    have hxMathlib : x ∈ IntermediateField.fixedField G := by
      rw [IntermediateField.mem_fixedField_iff]
      intro q hq
      have hqimage : q ∈ φ '' (H : Set (FieldAutomorphismOver e)) := by
        rw [hG]
        exact hq
      obtain ⟨ρ, hρ, hφρ⟩ := hqimage
      rw [← hφρ, hφ]
      exact hx ρ hρ
    have hgfix :=
      (IntermediateField.mem_fixingSubgroup_iff
        (IntermediateField.fixedField G) g.val).mp g.property x hxMathlib
    rw [← hφ]
    simpa using hgfix
  · intro σ
    apply Subtype.ext
    exact φ.symm_apply_apply σ.val
  · intro g
    apply Subtype.ext
    exact φ.apply_symm_apply g.val

-- A3.9b-D03：复现固定点、AlgHom 与 fixingSubgroupEquiv 的原始三段等价链。
private theorem mathlib_subgroup_fixingFixed_card_eq_bridge
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (G : Subgroup (L ≃ₐ[K] L)) (hfinite : Finite G) :
    Nat.card G =
      Nat.card (IntermediateField.fixingSubgroup
        (IntermediateField.fixedField G)) := by
  let _ : Finite G := hfinite
  apply Nat.card_congr
  refine (FixedPoints.toAlgHomEquiv G L).trans ?_
  refine (algEquivEquivAlgHom (IntermediateField.fixedField G) L).toEquiv.symm.trans ?_
  exact (IntermediateField.fixingSubgroupEquiv
    (IntermediateField.fixedField G)).toEquiv.symm

-- A3.9b-D04：拼接两侧 subtype 等价与 D03 的自然数基数等式。
private theorem transport_subtype_card_eq_bridge
    {A B C D : Type*} (eAC : A ≃ C) (eBD : B ≃ D)
    (hCD : Nat.card C = Nat.card D) : Nat.card A = Nat.card B := by
  exact (Nat.card_congr eAC).trans (hCD.trans (Nat.card_congr eBD).symm)

private theorem subgroup_card_eq_fixingFixed_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    Nat.card H =
      Nat.card (fixingAutomorphismSubgroup e
        (FixedFieldSet e (H : Set (FieldAutomorphismOver e)))) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨G, φ, hG, hφ⟩ := subgroup_mathlibSubgroup_bridge e H
  let _ : FiniteDimensional K L :=
    Classical.choice (finiteFieldExtension_mathlibFiniteDimensional_bridge e hfin)
  let _ : Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L
  let hfiniteG : Finite G := inferInstance
  let eHG := subgroupSubtype_mathlibSubgroup_equiv_bridge e H G φ hG
  let eFix := fixingFixedSubtype_mathlib_equiv_bridge e H G φ hG hφ
  exact transport_subtype_card_eq_bridge eHG eFix
    (mathlib_subgroup_fixingFixed_card_eq_bridge G hfiniteG)

-- A3.9b-N08：有限扩张中，上述两个自同构子类型均为有限类型。
private theorem subgroup_and_fixingFixed_finite_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    Finite H ∧
      Finite (fixingAutomorphismSubgroup e
        (FixedFieldSet e (H : Set (FieldAutomorphismOver e)))) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let _ : FiniteDimensional K L :=
    Classical.choice (finiteFieldExtension_mathlibFiniteDimensional_bridge e hfin)
  let _ : Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L
  let φ := fieldAutomorphismOver_mathlibAlgEquiv_equiv e
  let _ : Finite (FieldAutomorphismOver e) :=
    Finite.of_equiv (L ≃ₐ[K] L) φ.symm
  exact ⟨inferInstance, inferInstance⟩

-- A3.9b-N09：有限子类型集合的包含与相同基数推出集合相等。
private theorem finite_set_eq_of_subset_card_eq_bridge
    {α : Type*} (A B : Set α) (hAB : A ⊆ B)
    (hA : Finite {x : α // x ∈ A}) (hB : Finite {x : α // x ∈ B})
    (hcard : Nat.card {x : α // x ∈ A} = Nat.card {x : α // x ∈ B}) :
    A = B := by
  let _ : Finite {x : α // x ∈ A} := hA
  let _ : Finite {x : α // x ∈ B} := hB
  have hBfinite : B.Finite :=
    Set.finite_def.mpr ⟨Fintype.ofFinite {x : α // x ∈ B}⟩
  exact hBfinite.eq_of_subset_of_card_le hAB (le_of_eq hcard.symm)

/-! ## 有限恢复的公开数值接口 -/

/-- 显式中间域的 fixing 闭包：先取逐点固定该中间域的全部基域自同构，
再取这些自同构的共同固定域。该构造仍使用集合式教材承载。

> **Entry**: abstract-algebra.field.galois-correspondence-/
noncomputable def fixingClosureIntermediateField
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) : ExplicitIntermediateField e :=
  fixingClosureExplicitIntermediate_bridge F

/-- 显式中间域与其 fixing 闭包拥有完全相同的逐点固定自同构集合。
这是固定域与 fixing 运算形成 Galois connection 后的闭包稳定性。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem fixingAutomorphismSet_eq_fixingClosure
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F : ExplicitIntermediateField e) :
    FixingAutomorphismSet e F.carrier =
      FixingAutomorphismSet e (fixingClosureIntermediateField F).carrier :=
  fixing_eq_fixingClosure_bridge F

/-- 在有限 Galois 扩张中，存在一个自然数同时表示 `L/F` 的显式扩张
次数以及逐点固定 `F` 的基域自同构数目。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_fixing_card_eq_relativeDegree
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (F : ExplicitIntermediateField e) :
    ∃ n : ℕ,
      HasExtensionDegree (intermediateFieldInclusion F) n ∧
        Nat.card {σ : FieldAutomorphismOver e //
          σ ∈ FixingAutomorphismSet e F.carrier} = n :=
  fixing_card_eq_relativeDegree_bridge e hfin hgal F

/-- 有限 Galois 扩张的全部基域自同构数目等于扩张次数。这个数值接口把
本模块已经验证过的显式自同构与 Mathlib 后端对齐封装起来，使后续的
次数—指数推论无需重复建立 `GaloisExtension` 到 `IsGalois` 的私有桥。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_automorphism_card_eq_degree
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hgal : GaloisExtension e) {d : ℕ}
    (hd : HasExtensionDegree e d) :
    Nat.card (FieldAutomorphismOver e) = d := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let B : Module.Basis (Fin d) K L :=
    Classical.choice (hasExtensionDegree_mathlibBasis_bridge e d hd)
  let _ : FiniteDimensional K L := Module.Finite.of_basis B
  let _ : IsGalois K L :=
    Classical.choice (galoisExtension_mathlibIsGalois_bridge e hgal)
  let φ := fieldAutomorphismOver_mathlibAlgEquiv_equiv e
  calc
    Nat.card (FieldAutomorphismOver e) = Nat.card (L ≃ₐ[K] L) :=
      Nat.card_congr φ
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
    _ = d := by simpa [B] using Module.finrank_eq_card_basis B

/-- 有限 Galois 扩张中，中间域及其 fixing 闭包到 `L` 的相对扩张次数
相同。证明比较两边相同的 fixing 自同构集合基数。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_intermediate_fixingClosure_sameDegree
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (hgal : GaloisExtension e) (F : ExplicitIntermediateField e) :
    ∃ n : ℕ,
      HasExtensionDegree (intermediateFieldInclusion F) n ∧
        HasExtensionDegree
          (intermediateFieldInclusion (fixingClosureIntermediateField F)) n := by
  let G := fixingClosureIntermediateField F
  obtain ⟨n, hdegreeF, hcardF⟩ :=
    finiteGalois_fixing_card_eq_relativeDegree e hfin hgal F
  obtain ⟨m, hdegreeG, hcardG⟩ :=
    finiteGalois_fixing_card_eq_relativeDegree e hfin hgal G
  have hfixing : FixingAutomorphismSet e F.carrier =
      FixingAutomorphismSet e G.carrier :=
    fixingAutomorphismSet_eq_fixingClosure F
  have hnm : n = m := by
    rw [hfixing] at hcardF
    exact hcardF.symm.trans hcardG
  have hdegreeG' : HasExtensionDegree (intermediateFieldInclusion G) n :=
    hnm.symm ▸ hdegreeG
  exact ⟨n, hdegreeF, by simpa [G] using hdegreeG'⟩

/-- 若显式中间域 `F` 包含于 `G`，且二者到目标域 `L` 的有限扩张次数
相同，则维数消去迫使二者的底层集合严格相等。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem intermediateFieldCarrier_eq_of_subset_sameDegree
    {K L : Type*} [Field K] [Field L] {e : FieldEmbedding K L}
    (F G : ExplicitIntermediateField e) (hFG : F.carrier ⊆ G.carrier)
    (n : ℕ) (hF : HasExtensionDegree (intermediateFieldInclusion F) n)
    (hG : HasExtensionDegree (intermediateFieldInclusion G) n) :
    F.carrier = G.carrier :=
  intermediate_carrier_eq_of_subset_sameDegree_bridge F G hFG n hF hG

/-- 在有限扩张中，一个显式自同构子群集合与“先取固定域、再取 fixing
自同构”所得闭包具有相同的有限基数。该结论是子群恢复的数值核心。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteExtension_subgroup_card_eq_fixingFixed
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Set (FieldAutomorphismOver e)) (hH : SubgroupSet H) :
    Nat.card {σ : FieldAutomorphismOver e // σ ∈ H} =
      Nat.card {σ : FieldAutomorphismOver e //
        σ ∈ FixingAutomorphismSet e (FixedFieldSet e H)} := by
  let H' : Subgroup (FieldAutomorphismOver e) := hH.toSubgroup H
  change Nat.card H' =
    Nat.card (fixingAutomorphismSubgroup e
      (FixedFieldSet e (H' : Set (FieldAutomorphismOver e))))
  exact subgroup_card_eq_fixingFixed_bridge e hfin H'

/-- 有限扩张中，正式自同构子群与其固定域的 fixing 正式子群基数相同。
这是数值恢复的首选课程接口；私有证明核心直接接收正式子群，并通过
显式自同构与 Mathlib `AlgEquiv` 子群的等价比较基数。旧集合接口反向
包装本定理，而不再拥有独立证明链。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteExtension_subgroup_card_eq_fixingFixed_subgroup
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    Nat.card H =
      Nat.card (fixingAutomorphismSubgroup e
        (FixedFieldSet e (H : Set (FieldAutomorphismOver e)))) := by
  exact subgroup_card_eq_fixingFixed_bridge e hfin H

-- A3.9b-14：有限 Galois 扩张中，中间域由其 fixing 自同构集合的固定域恢复。
private theorem finiteGalois_fixedFieldSet_fixingAutomorphismSet_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) (hgal : GaloisExtension e)
    (E : Set L) (hE : IntermediateFieldSet e E) :
    FixedFieldSet e (FixingAutomorphismSet e E) = E := by
  let F : ExplicitIntermediateField e := ⟨E, hE⟩
  let G := fixingClosureIntermediateField F
  obtain ⟨n, hdegreeF, hdegreeG⟩ :=
    finiteGalois_intermediate_fixingClosure_sameDegree e hfin hgal F
  have hFG : F.carrier ⊆ G.carrier := by
    exact subset_fixedFieldSet_fixingAutomorphismSet e E
  have heq : F.carrier = G.carrier :=
    intermediateFieldCarrier_eq_of_subset_sameDegree
      F G hFG n hdegreeF hdegreeG
  exact heq.symm

-- A3.9b-15：有限扩张中，正式自同构子群由其固定域恢复。
private theorem finiteExtension_fixingAutomorphismSubgroup_fixedFieldSet_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    fixingAutomorphismSubgroup e
      (FixedFieldSet e (H : Set (FieldAutomorphismOver e))) = H := by
  let B := fixingAutomorphismSubgroup e
    (FixedFieldSet e (H : Set (FieldAutomorphismOver e)))
  have hHB : (H : Set (FieldAutomorphismOver e)) ⊆
      (B : Set (FieldAutomorphismOver e)) := by
    intro σ hσ
    change σ ∈ FixingAutomorphismSet e
      (FixedFieldSet e (H : Set (FieldAutomorphismOver e)))
    exact subset_fixingAutomorphismSet_fixedFieldSet e
      (H : Set (FieldAutomorphismOver e)) hσ
  have hcard : Nat.card H = Nat.card B :=
    subgroup_card_eq_fixingFixed_bridge e hfin H
  obtain ⟨hfiniteH, hfiniteB⟩ :=
    subgroup_and_fixingFixed_finite_bridge e hfin H
  have hsets : (H : Set (FieldAutomorphismOver e)) =
      (B : Set (FieldAutomorphismOver e)) :=
    finite_set_eq_of_subset_card_eq_bridge
      (H : Set (FieldAutomorphismOver e))
      (B : Set (FieldAutomorphismOver e))
      hHB hfiniteH hfiniteB hcard
  exact Subgroup.ext (Set.ext_iff.mp hsets.symm)

/-- 有限 Galois 扩张中，每个显式中间域集合都由逐点固定它的全部
基域自同构的共同固定域严格恢复。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_fixedFieldSet_fixingAutomorphismSet
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) (hgal : GaloisExtension e)
    (E : Set L) (hE : IntermediateFieldSet e E) :
    FixedFieldSet e (FixingAutomorphismSet e E) = E :=
  finiteGalois_fixedFieldSet_fixingAutomorphismSet_bridge
    e hfin hgal E hE

/-- 在任意有限显式扩张中，自同构子群集合都由其固定域的全部 fixing
自同构严格恢复；这个方向不额外要求整个扩张是 Galois。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteExtension_fixingAutomorphismSet_fixedFieldSet
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Set (FieldAutomorphismOver e)) (hH : SubgroupSet H) :
    FixingAutomorphismSet e (FixedFieldSet e H) = H := by
  let H' : Subgroup (FieldAutomorphismOver e) := hH.toSubgroup H
  have hrecover :=
    finiteExtension_fixingAutomorphismSubgroup_fixedFieldSet_bridge
      e hfin H'
  have hcarrier := congrArg
    (fun P : Subgroup (FieldAutomorphismOver e) =>
      (P : Set (FieldAutomorphismOver e))) hrecover
  rw [fixingAutomorphismSubgroup_carrier,
    SubgroupSet.coe_toSubgroup H hH] at hcarrier
  exact hcarrier

/-- 有限扩张中，正式自同构子群由其固定域的 fixing 正式子群严格恢复。
该定理是 Consequences 与 Restriction 模块应使用的首选恢复接口；旧的
`Set` 加 `SubgroupSet` 版本仅保留作兼容边界。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteExtension_fixingAutomorphismSubgroup_fixedFieldSet
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e)
    (H : Subgroup (FieldAutomorphismOver e)) :
    fixingAutomorphismSubgroup e
      (FixedFieldSet e (H : Set (FieldAutomorphismOver e))) = H := by
  exact finiteExtension_fixingAutomorphismSubgroup_fixedFieldSet_bridge
    e hfin H

/-- 有限 Galois 扩张中，每个显式中间域由其 fixing 正式子群的固定域
恢复。该表述保留集合式中间域教材 API，同时把群一侧升级为正式
`Subgroup` 承载。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_fixedFieldSet_fixingAutomorphismSubgroup
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) (hgal : GaloisExtension e)
    (E : Set L) (hE : IntermediateFieldSet e E) :
    FixedFieldSet e
      (fixingAutomorphismSubgroup e E :
        Set (FieldAutomorphismOver e)) = E := by
  simpa only [fixingAutomorphismSubgroup_carrier] using
    finiteGalois_fixedFieldSet_fixingAutomorphismSet
      e hfin hgal E hE

/-! ## 有限 Galois 基本对应 -/

/-- A3.9b-16 的集合级 compatibility 汇总。第一个方向恢复
每个显式中间域；第二个方向恢复每个显式自同构子群，并保留第二方向
本身只需要有限性的精确数学边界。新课程代码应优先使用下方接受正式
`Subgroup` 的 `finiteGalois_fundamental_correspondence_subgroup`。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_fundamental_correspondence
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) (hgal : GaloisExtension e) :
    (∀ E : Set L, IntermediateFieldSet e E →
      FixedFieldSet e (FixingAutomorphismSet e E) = E) ∧
    (∀ H : Set (FieldAutomorphismOver e), SubgroupSet H →
      FixingAutomorphismSet e (FixedFieldSet e H) = H) := by
  constructor
  · intro E hE
    exact finiteGalois_fixedFieldSet_fixingAutomorphismSet e hfin hgal E hE
  · intro H hH
    exact finiteExtension_fixingAutomorphismSet_fixedFieldSet e hfin H hH

/-- 有限 Galois 基本对应的首选课程汇总接口。中间域仍使用本库显式集合
谓词，群一侧则直接量化 Mathlib 正式 `Subgroup`；两个恢复方向分别复用
上方正式薄接口，不建立第二套基本对应证明链。

> **Entry**: abstract-algebra.field.galois-correspondence-/
theorem finiteGalois_fundamental_correspondence_subgroup
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) (hgal : GaloisExtension e) :
    (∀ E : Set L, IntermediateFieldSet e E →
      FixedFieldSet e
        (fixingAutomorphismSubgroup e E :
          Set (FieldAutomorphismOver e)) = E) ∧
    (∀ H : Subgroup (FieldAutomorphismOver e),
      fixingAutomorphismSubgroup e
        (FixedFieldSet e (H : Set (FieldAutomorphismOver e))) = H) := by
  constructor
  · intro E hE
    exact finiteGalois_fixedFieldSet_fixingAutomorphismSubgroup
      e hfin hgal E hE
  · intro H
    exact finiteExtension_fixingAutomorphismSubgroup_fixedFieldSet
      e hfin H

end SandronesLibrary.AbstractAlgebra.FieldGaloisCorrespondence
