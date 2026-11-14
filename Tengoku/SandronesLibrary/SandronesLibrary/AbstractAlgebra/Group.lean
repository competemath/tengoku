/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# AbstractAlgebra / Group —— 群论基础（抽象代数第一学期 A1）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **abstract-algebra.group.def**（单位元与逆元唯一/消去与方程/整数幂/生成子群/子群格）✅。
* **abstract-algebra.group.coset**（左右陪集/陪集分割/Lagrange/子群阶与元素阶的整除推论）✅。
* **abstract-algebra.group.normal**（等价刻画/核与稳定构造/商群运算/商映射泛性质）✅。
* **abstract-algebra.group.index-two**（指数 2 子群必正规）✅。
* **abstract-algebra.group.hom**（复合与子群像/单满射判据/显式第一同构定理/同构不变量）✅。

> **语言说明**：Mathlib 的 `Subgroup` 是子群的正式语义载体；本文件早期引入的
> `SubgroupSet` 只保留为集合式判定法的兼容层，并由下方的无损转换桥接入正式载体。
> `GroupAxioms` 与 `GroupHomomorphism` 仍负责逐项展示教材公理。旧公开接口将在定义依赖
> 自底向上的迁移中保留为兼容层。`Module` 仍不得出现在公开签名中。
-/

open scoped BigOperators

namespace SandronesLibrary

namespace AbstractAlgebra.Group

open scoped Pointwise

/-! ### 群、子群与群同态的教材定义层 -/

/-- **群公理**：在给定单位元、乘法和逆运算后，逐项要求结合律、左右单位律及左右逆元律。
Mathlib 的 `[Group G]` 是这些数据与公理的实现打包，不是本库对群概念的定义。
> **Entry**: abstract-algebra.group.def-/
structure GroupAxioms (G : Type*) [One G] [Mul G] [Inv G] : Prop where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul : ∀ a : G, a⁻¹ * a = 1
  mul_inv : ∀ a : G, a * a⁻¹ = 1

/-- **交换群公理**：满足群公理，并且乘法交换。
> **Entry**: abstract-algebra.group.def-/
def CommutativeGroupAxioms (G : Type*) [One G] [Mul G] [Inv G] : Prop :=
  GroupAxioms G ∧ ∀ a b : G, a * b = b * a

/-- **子群集合判据**：集合包含单位元，并对乘法和逆运算封闭。
> **Entry**: abstract-algebra.group.def-/
def SubgroupSet {G : Type*} [One G] [Mul G] [Inv G] (H : Set G) : Prop :=
  1 ∈ H ∧ (∀ ⦃x y : G⦄, x ∈ H → y ∈ H → x * y ∈ H) ∧
    (∀ ⦃x : G⦄, x ∈ H → x⁻¹ ∈ H)

/-- **群同态谓词**：普通函数保持单位元、乘法和逆运算。这样可先用教材语言陈述同态，
再在证明后端把它打包成 Mathlib `MonoidHom`。
> **Entry**: abstract-algebra.group.hom-/
def GroupHomomorphism {G H : Type*} [One G] [Mul G] [Inv G]
    [One H] [Mul H] [Inv H] (f : G → H) : Prop :=
  f 1 = 1 ∧ (∀ x y : G, f (x * y) = f x * f y) ∧
    (∀ x : G, f x⁻¹ = (f x)⁻¹)

/-- **由集合生成的子群集合**：所有包含 `S` 的子群集合之交；这直接表达“包含 `S` 的
最小子群”，不依赖 Mathlib `Subgroup.closure` 作为定义。
> **Entry**: abstract-algebra.group.def-/
def generatedSubgroupSet {G : Type*} [One G] [Mul G] [Inv G] (S : Set G) : Set G :=
  {x | ∀ H : Set G, SubgroupSet H → S ⊆ H → x ∈ H}

/-- 每个 Mathlib 群实例都满足本库逐条列出的群公理。
> **Entry**: abstract-algebra.group.def-/
theorem group_has_groupAxioms (G : Type*) [Group G] : GroupAxioms G := by
  exact ⟨mul_assoc, one_mul, mul_one, (fun a => by simp), (fun a => by simp)⟩

/-- 每个 Mathlib 交换群实例都满足本库交换群公理。
> **Entry**: abstract-algebra.group.def-/
theorem commGroup_has_commutativeGroupAxioms (G : Type*) [CommGroup G] :
    CommutativeGroupAxioms G :=
  ⟨group_has_groupAxioms G, mul_comm⟩

/-- **集合判据到正式子群的直接桥**：把 `H` 对单位元、乘法和逆元的封闭性证明
直接打包成 `Subgroup G`。所得子群的承载集按定义就是 `H`，因此无需经过存在量词
或选择一个不透明的见证。
> **Entry**: abstract-algebra.group.def-/
def SubgroupSet.toSubgroup {G : Type*} [Group G]
    (H : Set G) (hH : SubgroupSet H) : Subgroup G :=
  { carrier := H
    one_mem' := hH.1
    mul_mem' := fun hx hy => hH.2.1 hx hy
    inv_mem' := fun hx => hH.2.2 hx }

/-- 直接桥不改变成员关系：在转换后的正式子群中，元素属于关系仍然是 `x ∈ H`。
> **Entry**: abstract-algebra.group.def-/
@[simp] theorem SubgroupSet.mem_toSubgroup_iff {G : Type*} [Group G]
    (H : Set G) (hH : SubgroupSet H) (x : G) :
    x ∈ SubgroupSet.toSubgroup H hH ↔ x ∈ H := by
  rfl

/-- 直接桥所得正式子群的承载集就是原集合。
> **Entry**: abstract-algebra.group.def-/
theorem SubgroupSet.coe_toSubgroup {G : Type*} [Group G]
    (H : Set G) (hH : SubgroupSet H) :
    ((SubgroupSet.toSubgroup H hH : Subgroup G) : Set G) = H := by
  rfl

end AbstractAlgebra.Group
end SandronesLibrary

namespace Subgroup

/-- 任意正式子群的承载集都满足旧的 `SubgroupSet` 封闭性判据。这是从正式载体退回
集合式判定语言的兼容桥；新接口仍应直接接收 `Subgroup G`。
> **Entry**: abstract-algebra.group.def-/
theorem subgroupSet {G : Type*} [Group G] (H : Subgroup G) :
    SandronesLibrary.AbstractAlgebra.Group.SubgroupSet (H : Set G) :=
  ⟨H.one_mem, (fun {_ _} hx hy => H.mul_mem hx hy),
    (fun {_} hx => H.inv_mem hx)⟩

end Subgroup

namespace SandronesLibrary
namespace AbstractAlgebra.Group

open scoped Pointwise

/-- 正式子群取承载集、再由直接桥打包后保持不变。
> **Entry**: abstract-algebra.group.def-/
@[simp] theorem SubgroupSet.toSubgroup_subgroupSet {G : Type*} [Group G]
    (H : Subgroup G) :
    SubgroupSet.toSubgroup (H : Set G) H.subgroupSet = H := by
  ext x
  rfl

/-- 直接桥所得子群包含于任意正式子群 `K`，恰当且仅当原集合逐点包含于 `K`。
这个通用序关系接口表明后续理论可以直接量化 `K : Subgroup G`，不必继续传播
`Set G` 与额外的 `SubgroupSet` 证明。
> **Entry**: abstract-algebra.group.def-/
theorem SubgroupSet.toSubgroup_le_iff {G : Type*} [Group G]
    (H : Set G) (hH : SubgroupSet H) (K : Subgroup G) :
    SubgroupSet.toSubgroup H hH ≤ K ↔ H ⊆ (K : Set G) := by
  rfl

/-- 任意正式子群 `K` 包含于直接桥所得子群，恰当且仅当 `K` 的承载集包含于原集合。
> **Entry**: abstract-algebra.group.def-/
theorem SubgroupSet.le_toSubgroup_iff {G : Type*} [Group G]
    (H : Set G) (hH : SubgroupSet H) (K : Subgroup G) :
    K ≤ SubgroupSet.toSubgroup H hH ↔ (K : Set G) ⊆ H := by
  rfl

/-- 本库子群集合判据与“存在底层集合恰为 `H` 的 Mathlib 子群”完全等价。
> **Entry**: abstract-algebra.group.def-/
theorem subgroupSet_iff_exists_subgroup {G : Type*} [Group G] (H : Set G) :
    SubgroupSet H ↔ ∃ K : Subgroup G, (K : Set G) = H := by
  constructor
  · intro hH
    exact ⟨hH.toSubgroup H, rfl⟩
  · rintro ⟨K, rfl⟩
    exact K.subgroupSet

/-- 打包的 Mathlib 同态满足本库逐运算群同态谓词。
> **Entry**: abstract-algebra.group.hom-/
theorem monoidHom_is_groupHomomorphism {G H : Type*} [Group G] [Group H]
    (f : G →* H) : GroupHomomorphism f :=
  ⟨f.map_one, f.map_mul, f.map_inv⟩

/-- 满足本库群同态谓词的普通函数可以打包成 Mathlib `MonoidHom`，且底层函数不变。
> **Entry**: abstract-algebra.group.hom-/
theorem groupHomomorphism_exists_monoidHom {G H : Type*} [Group G] [Group H]
    (f : G → H) (hf : GroupHomomorphism f) : ∃ F : G →* H, ⇑F = f := by
  exact ⟨{ toFun := f, map_one' := hf.1, map_mul' := hf.2.1 }, rfl⟩

/-- 由 `S` 生成的集合确实满足子群集合判据。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroupSet_is_subgroup {G : Type*} [Group G] (S : Set G) :
    SubgroupSet (generatedSubgroupSet S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro H hH hSH
    exact hH.1
  · intro x y hx hy H hH hSH
    exact hH.2.1 (hx H hH hSH) (hy H hH hSH)
  · intro x hx H hH hSH
    exact hH.2.2 (hx H hH hSH)

/-- 每个生成元都属于生成子群集合。
> **Entry**: abstract-algebra.group.def-/
theorem subset_generatedSubgroupSet {G : Type*} [Group G] (S : Set G) :
    S ⊆ generatedSubgroupSet S := by
  intro x hx H hH hSH
  exact hSH hx

/-- **生成子群的最小性**：任何包含 `S` 的子群集合都包含 `generatedSubgroupSet S`。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroupSet_least {G : Type*} [Group G] {S H : Set G}
    (hH : SubgroupSet H) (hSH : S ⊆ H) : generatedSubgroupSet S ⊆ H := by
  intro x hx
  exact hx H hH hSH

/-- 本库生成子群集合与 Mathlib `Subgroup.closure` 的底层集合相同；后者从此只作为承载桥。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroupSet_eq_mathlib_closure {G : Type*} [Group G] (S : Set G) :
    generatedSubgroupSet S = ((Subgroup.closure S : Subgroup G) : Set G) := by
  ext x
  constructor
  · intro hx
    apply hx ((Subgroup.closure S : Subgroup G) : Set G)
    · exact (subgroupSet_iff_exists_subgroup _).2 ⟨Subgroup.closure S, rfl⟩
    · exact Subgroup.subset_closure
  · intro hx H hH hSH
    obtain ⟨K, hK⟩ := (subgroupSet_iff_exists_subgroup H).1 hH
    change x ∈ Subgroup.closure S at hx
    rw [← hK]
    exact (Subgroup.closure_le K |>.mpr (by simpa [hK] using hSH)) hx

/-! ### 群公理的直接推论 -/

/-- 左单位元是唯一的：若 `e * x = x` 对所有 x 成立，则 `e = 1`。
> **Entry**: abstract-algebra.group.def-/
theorem left_identity_unique {G : Type*} [Group G] (e : G)
    (he : ∀ x : G, e * x = x) : e = 1 := by
  simpa using he 1

/-- 右单位元是唯一的。
> **Entry**: abstract-algebra.group.def-/
theorem right_identity_unique {G : Type*} [Group G] (e : G)
    (he : ∀ x : G, x * e = x) : e = 1 := by
  simpa using he 1

/-- 左逆元是唯一的：`yx=1` 蕴含 `y=x⁻¹`。
> **Entry**: abstract-algebra.group.def-/
theorem left_inverse_unique {G : Type*} [Group G] {x y : G}
    (h : y * x = 1) : y = x⁻¹ := by
  exact eq_inv_of_mul_eq_one_left h

/-- 右逆元是唯一的：`xy=1` 蕴含 `y=x⁻¹`。
> **Entry**: abstract-algebra.group.def-/
theorem right_inverse_unique {G : Type*} [Group G] {x y : G}
    (h : x * y = 1) : y = x⁻¹ := by
  exact eq_inv_of_mul_eq_one_right h

/-- 群乘法的左消去律。
> **Entry**: abstract-algebra.group.def-/
theorem group_mul_left_cancel {G : Type*} [Group G] {a x y : G}
    (h : a * x = a * y) : x = y := by
  exact mul_left_cancel h

/-- 群乘法的右消去律。
> **Entry**: abstract-algebra.group.def-/
theorem group_mul_right_cancel {G : Type*} [Group G] {a x y : G}
    (h : x * a = y * a) : x = y := by
  exact mul_right_cancel h

/-- 左乘方程 `ax=b` 的唯一解是 `x=a⁻¹b`。
> **Entry**: abstract-algebra.group.def-/
theorem solve_mul_left_iff {G : Type*} [Group G] (a x b : G) :
    a * x = b ↔ x = a⁻¹ * b := by
  constructor <;> intro h
  · rw [← h]
    group
  · rw [h]
    group

/-- 右乘方程 `xa=b` 的唯一解是 `x=ba⁻¹`。
> **Entry**: abstract-algebra.group.def-/
theorem solve_mul_right_iff {G : Type*} [Group G] (a x b : G) :
    x * a = b ↔ x = b * a⁻¹ := by
  constructor <;> intro h
  · rw [← h]
    group
  · rw [h]
    group

/-- 乘积取逆时次序反转：`(ab)⁻¹=b⁻¹a⁻¹`。
> **Entry**: abstract-algebra.group.def-/
theorem inverse_mul_reverse {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  exact mul_inv_rev a b

/-- 整数零次幂等于单位元。
> **Entry**: abstract-algebra.group.def-/
theorem zpow_zero_basic {G : Type*} [Group G] (a : G) : a ^ (0 : ℤ) = 1 := by
  exact zpow_zero a

/-- 整数一次幂等于自身。
> **Entry**: abstract-algebra.group.def-/
theorem zpow_one_basic {G : Type*} [Group G] (a : G) : a ^ (1 : ℤ) = a := by
  exact zpow_one a

/-- 同底整数幂相乘：`a^(m+n)=a^m a^n`。
> **Entry**: abstract-algebra.group.def-/
theorem zpow_add_basic {G : Type*} [Group G] (a : G) (m n : ℤ) :
    a ^ (m + n) = a ^ m * a ^ n := by
  exact zpow_add a m n

/-- 负整数幂等于对应幂的逆。
> **Entry**: abstract-algebra.group.def-/
theorem zpow_neg_basic {G : Type*} [Group G] (a : G) (n : ℤ) :
    a ^ (-n) = (a ^ n)⁻¹ := by
  exact zpow_neg a n

/-- 整数幂的幂法则：`a^(mn)=(a^m)^n`。
> **Entry**: abstract-algebra.group.def-/
theorem zpow_mul_basic {G : Type*} [Group G] (a : G) (m n : ℤ) :
    a ^ (m * n) = (a ^ m) ^ n := by
  exact zpow_mul a m n

/-- **子群判定定理**（教材核心判据）：子集 S 含单位元、对乘法与取逆封闭 ⟹ S 是子群。 
> **Entry**: abstract-algebra.group.def-/
theorem subgroup_of_closed {G : Type*} [Group G] (S : Set G)
    (h1 : 1 ∈ S) (hmul : ∀ {x y : G}, x ∈ S → y ∈ S → x * y ∈ S)
    (hinv : ∀ {x : G}, x ∈ S → x⁻¹ ∈ S) :
    ∃ H : Subgroup G, ∀ x : G, x ∈ H ↔ x ∈ S := by
  let ssm : Subsemigroup G := ⟨S, hmul⟩
  let sm : Submonoid G := ⟨ssm, h1⟩
  let H : Subgroup G := ⟨sm, hinv⟩
  refine ⟨H, ?_⟩
  intro x
  constructor <;> intro hx <;> exact hx

/-- **子群含单位元**：任何子群都包含单位元。 
> **Entry**: abstract-algebra.group.def-/
theorem subgroup_one_mem {G : Type*} [Group G] (H : Subgroup G) : 1 ∈ H := by
  exact H.one_mem

/-- **子群外延性**：成员一致的两个子群相等。 
> **Entry**: abstract-algebra.group.def-/
theorem subgroup_ext {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x : G, x ∈ H ↔ x ∈ K) : H = K := by
  exact Subgroup.ext h

/-- **平凡子群**：只含单位元的子群（最小子群）。 
> **Entry**: abstract-algebra.group.def-/
theorem subgroup_bot_eq_singleton {G : Type*} [Group G] :
    ((⊥ : Subgroup G) : Set G) = {1} := by
  ext x
  exact Subgroup.mem_bot

/-- **全子群**：整个群自身是子群（最大子群）。 
> **Entry**: abstract-algebra.group.def-/
theorem subgroup_top_eq_univ {G : Type*} [Group G] :
    ((⊤ : Subgroup G) : Set G) = Set.univ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    exact Subgroup.mem_top x

/-! ### 生成子群与子群格 -/

/-- Mathlib 打包的生成子群承载。教材公开定义是 `generatedSubgroupSet`；此对象保留给旧定理
及与 Mathlib 子群格互操作，不能再被描述为本库对生成子群的定义。
> **Entry**: abstract-algebra.group.def-/
def generatedSubgroup {G : Type*} [Group G] (S : Set G) : Subgroup G :=
  Subgroup.closure S

/-- 每个生成元都属于它们生成的子群，即 `S ⊆ ⟨S⟩`。
> **Entry**: abstract-algebra.group.def-/
theorem subset_generatedSubgroup {G : Type*} [Group G] (S : Set G) :
    S ⊆ generatedSubgroup S := by
  exact Subgroup.subset_closure

/-- **生成子群的最小性**：`⟨S⟩ ≤ H` 当且仅当 `H` 包含所有生成元。
这是从生成元定义同态、证明两个子群相等时最常用的消去原则。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroup_le_iff {G : Type*} [Group G]
    (S : Set G) (H : Subgroup G) :
    generatedSubgroup S ≤ H ↔ S ⊆ H := by
  exact Subgroup.closure_le H

/-- 扩大生成元集合只会扩大生成子群。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroup_mono {G : Type*} [Group G]
    {S T : Set G} (hST : S ⊆ T) :
    generatedSubgroup S ≤ generatedSubgroup T := by
  exact Subgroup.closure_mono hST

/-- 一个子群的底层集合重新生成出的子群仍是它自身。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroup_coe {G : Type*} [Group G] (H : Subgroup G) :
    generatedSubgroup (H : Set G) = H := by
  exact Subgroup.closure_eq H

/-- 两组生成元的并生成两个生成子群在子群格中的上确界。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroup_union {G : Type*} [Group G] (S T : Set G) :
    generatedSubgroup (S ∪ T) = generatedSubgroup S ⊔ generatedSubgroup T := by
  exact Subgroup.closure_union S T

/-- 两个子群的下确界就是它们的集合交：元素属于 `H ⊓ K` 当且仅当同时属于二者。
> **Entry**: abstract-algebra.group.def-/
theorem mem_subgroup_inf_iff {G : Type*} [Group G]
    (H K : Subgroup G) (x : G) :
    x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K := by
  exact Subgroup.mem_inf

/-- 任意族子群的下确界就是共同交集。
> **Entry**: abstract-algebra.group.def-/
theorem mem_subgroup_iInf_iff {G : Type*} [Group G]
    {ι : Sort*} (H : ι → Subgroup G) (x : G) :
    x ∈ ⨅ i, H i ↔ ∀ i, x ∈ H i := by
  exact Subgroup.mem_iInf

/-- 子群上确界的序刻画：`H ⊔ K ≤ L` 当且仅当 H、K 都包含于 L。
> **Entry**: abstract-algebra.group.def-/
theorem subgroup_sup_le_iff {G : Type*} [Group G] (H K L : Subgroup G) :
    H ⊔ K ≤ L ↔ H ≤ L ∧ K ≤ L := by
  exact sup_le_iff

/-- 子群下确界的序刻画：`L ≤ H ⊓ K` 当且仅当 L 同时包含于 H、K。
> **Entry**: abstract-algebra.group.def-/
theorem subgroup_le_inf_iff {G : Type*} [Group G] (H K L : Subgroup G) :
    L ≤ H ⊓ K ↔ L ≤ H ∧ L ≤ K := by
  exact le_inf_iff

/-- 单元素集合生成的子群就是该元素的所有整数次幂组成的子群。
> **Entry**: abstract-algebra.group.def-/
theorem generatedSubgroup_singleton_eq_zpowers {G : Type*} [Group G] (g : G) :
    generatedSubgroup ({g} : Set G) = Subgroup.zpowers g := by
  exact (Subgroup.zpowers_eq_closure g).symm

/-- 同态把由 S 生成的子群映到由 `f(S)` 生成的子群。
这使得只在生成元上指定映射成为可能。
> **Entry**: abstract-algebra.group.def-/
theorem map_generatedSubgroup {G N : Type*} [Group G] [Group N]
    (f : G →* N) (S : Set G) :
    Subgroup.map f (generatedSubgroup S) = generatedSubgroup (f '' S) := by
  exact MonoidHom.map_closure f S

/-- **左陪集元素刻画**：x ∈ aH ⟺ a⁻¹·x ∈ H（左陪集 aH = { a·h | h ∈ H }）。 
> **Entry**: abstract-algebra.group.coset-/
theorem left_coset_mem_iff {G : Type*} [Group G] (H : Subgroup G) (a x : G) :
    x ∈ a • (H : Set G) ↔ a⁻¹ * x ∈ H := by
  exact mem_leftCoset_iff (a := a)

/-- **左陪集相等判据**：aH = bH ⟺ b⁻¹·a ∈ H（两个陪集相等当且仅当代表元素差落在 H 中）。 
> **Entry**: abstract-algebra.group.coset-/
theorem left_coset_eq_iff {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    a • (H : Set G) = b • (H : Set G) ↔ b⁻¹ * a ∈ H := by
  constructor
  · intro h
    exact (leftCoset_eq_iff (s := H) (x := b) (y := a)).mp h.symm
  · intro h
    exact ((leftCoset_eq_iff (s := H) (x := b) (y := a)).mpr h).symm

/-- **自身在陪集中**：对任意 a，a ∈ aH。 
> **Entry**: abstract-algebra.group.coset-/
theorem left_coset_mem_self {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    a ∈ a • (H : Set G) := by
  exact mem_own_leftCoset (s := H.toSubmonoid) a

/-- **单位元陪集**：1H = H。 
> **Entry**: abstract-algebra.group.coset-/
theorem one_left_coset {G : Type*} [Group G] (H : Subgroup G) :
    (1 : G) • (H : Set G) = (H : Set G) := by
  exact one_leftCoset (s := (H : Set G))

/-- **右陪集元素刻画**：`x ∈ Ha` 当且仅当 `x a⁻¹ ∈ H`。
它与左陪集判据互为镜像，但在非交换群中二者不能混用。
> **Entry**: abstract-algebra.group.coset-/
theorem right_coset_mem_iff {G : Type*} [Group G] (H : Subgroup G) (a x : G) :
    x ∈ MulOpposite.op a • (H : Set G) ↔ x * a⁻¹ ∈ H := by
  exact mem_rightCoset_iff a

/-- **右陪集相等判据**：`Ha = Hb` 当且仅当 `b a⁻¹ ∈ H`。
> **Entry**: abstract-algebra.group.coset-/
theorem right_coset_eq_iff {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    MulOpposite.op a • (H : Set G) = MulOpposite.op b • (H : Set G) ↔
      b * a⁻¹ ∈ H := by
  exact _root_.rightCoset_eq_iff H

/-- 每个代表元都属于自己的右陪集 `Ha`。
> **Entry**: abstract-algebra.group.coset-/
theorem right_coset_mem_self {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    a ∈ MulOpposite.op a • (H : Set G) := by
  exact mem_own_rightCoset H.toSubmonoid a

/-- **陪集相交判据**：两个左陪集有公共元素，当且仅当它们相等。

向前方向取公共元素 `x`，则 `a⁻¹x,b⁻¹x ∈ H`，所以
`a⁻¹b = (a⁻¹x)(b⁻¹x)⁻¹ ∈ H`，由陪集相等判据得到结论。
> **Entry**: abstract-algebra.group.coset-/
theorem left_coset_inter_nonempty_iff_eq {G : Type*} [Group G]
    (H : Subgroup G) (a b : G) :
    (a • (H : Set G) ∩ b • (H : Set G)).Nonempty ↔
      a • (H : Set G) = b • (H : Set G) := by
  constructor
  · rintro ⟨x, hxa, hxb⟩
    apply (_root_.leftCoset_eq_iff H).2
    have ha : a⁻¹ * x ∈ H := (left_coset_mem_iff H a x).1 hxa
    have hb : b⁻¹ * x ∈ H := (left_coset_mem_iff H b x).1 hxb
    have hid : a⁻¹ * b = (a⁻¹ * x) * (b⁻¹ * x)⁻¹ := by group
    rw [hid]
    exact H.mul_mem ha (H.inv_mem hb)
  · intro hab
    exact ⟨a, left_coset_mem_self H a, hab ▸ left_coset_mem_self H a⟩

/-- **陪集分割的核心性质**：任意两个左陪集或者相等，或者不相交。
配合每个元素属于自己的陪集，这说明左陪集把整个群分割成等势的块。
> **Entry**: abstract-algebra.group.coset-/
theorem left_cosets_eq_or_disjoint {G : Type*} [Group G]
    (H : Subgroup G) (a b : G) :
    a • (H : Set G) = b • (H : Set G) ∨
      Disjoint (a • (H : Set G)) (b • (H : Set G)) := by
  by_cases hab : a • (H : Set G) = b • (H : Set G)
  · exact Or.inl hab
  · right
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hab ((left_coset_inter_nonempty_iff_eq H a b).1 ⟨x, hxa, hxb⟩)

/-- **陪集与子群等势**：左陪集 aH 与子群 H 的元素个数相同（陪集都是"同样大小"）。 
> **Entry**: abstract-algebra.group.coset-/
theorem leftCoset_card_eq {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    Nat.card ({x : G // x ∈ a • (H : Set G)}) = Nat.card (↥H) := by
  exact Nat.card_congr (Subgroup.leftCosetEquivSubgroup (s := H) a)

/-- **Lagrange 定理**：对有限群 G，|H| · [G:H] = |G|（子群阶整除群阶）。 
> **Entry**: abstract-algebra.group.coset-/
theorem lagrange {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card ↥H * H.index = Nat.card G := by
  exact Subgroup.card_mul_index H

/-- **Lagrange 的整除形式**：子群的阶整除群的阶。
这里使用 `Nat.card`，有限群时就是通常的有限基数；等式中的商因子正是子群指数。
> **Entry**: abstract-algebra.group.coset-/
theorem subgroup_card_dvd_group_card {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G := by
  exact ⟨H.index, (lagrange H).symm⟩

/-- **元素阶整除群阶**：有限群中每个元素生成的循环子群之阶整除群阶。
这是 Lagrange 定理应用于循环子群 `⟨x⟩` 的标准推论。
> **Entry**: abstract-algebra.group.coset-/
theorem element_order_dvd_group_order {G : Type*} [Group G] [Fintype G] (x : G) :
    orderOf x ∣ Fintype.card G := by
  exact orderOf_dvd_card

/-- **有限群中的幂公式**：对每个 `x ∈ G`，都有 `x ^ |G| = 1`。
它由元素阶整除群阶立即得到，是 Euler 与 Fermat 型合同的群论原型。
> **Entry**: abstract-algebra.group.coset-/
theorem pow_group_order_eq_one {G : Type*} [Group G] [Fintype G] (x : G) :
    x ^ Fintype.card G = 1 := by
  exact pow_card_eq_one

/-- **正规子群的共轭封闭性**：H 正规 ⟹ 对 n ∈ H、任意 g，共轭 g·n·g⁻¹ ∈ H。
  这是正规子群的定义本质（教材定义）。 
> **Entry**: abstract-algebra.group.normal-/
theorem normal_conj_mem {G : Type*} [Group G] (H : Subgroup G) (nH : H.Normal)
    (n : G) (hn : n ∈ H) (g : G) : g * n * g⁻¹ ∈ H := by
  exact nH.conj_mem n hn g

/-- **正规性的陪集刻画**：H 正规当且仅当每个元素对应的左陪集与右陪集相等，
即 `gH = Hg`。这是从陪集进入商群的关键判据。
> **Entry**: abstract-algebra.group.normal-/
theorem normal_iff_left_coset_eq_right_coset {G : Type*} [Group G]
    (H : Subgroup G) :
    H.Normal ↔ ∀ g : G, g • (H : Set G) = MulOpposite.op g • (H : Set G) := by
  exact _root_.normal_iff_eq_cosets (s := H)

/-- 群同态的核总是正规子群。
> **Entry**: abstract-algebra.group.normal-/
theorem kernel_is_normal {G N : Type*} [Group G] [Group N] (f : G →* N) :
    f.ker.Normal := by
  infer_instance

/-- 正规子群沿任意群同态的逆像仍正规。
> **Entry**: abstract-algebra.group.normal-/
theorem normal_comap {G N : Type*} [Group G] [Group N]
    (f : G →* N) (H : Subgroup N) (hH : H.Normal) :
    (Subgroup.comap f H).Normal := by
  exact hH.comap f

/-- 正规子群沿满群同态的像仍正规。满射条件确保目标群中的任意共轭元都能提升。
> **Entry**: abstract-algebra.group.normal-/
theorem normal_map_of_surjective {G N : Type*} [Group G] [Group N]
    (f : G →* N) (hf : Function.Surjective f)
    (H : Subgroup G) (hH : H.Normal) :
    (Subgroup.map f H).Normal := by
  exact hH.map f hf

/-- 两个正规子群的交仍是正规子群。
> **Entry**: abstract-algebra.group.normal-/
theorem normal_inf {G : Type*} [Group G] (H K : Subgroup G)
    (hH : H.Normal) (hK : K.Normal) : (H ⊓ K).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rw [Subgroup.mem_inf] at hn ⊢
  exact ⟨hH.conj_mem n hn.1 g, hK.conj_mem n hn.2 g⟩

/-- **正规子群的交换性**：H 正规 ⟹ a·b ∈ H ⟹ b·a ∈ H。 
> **Entry**: abstract-algebra.group.normal-/
theorem normal_mem_comm {G : Type*} [Group G] (H : Subgroup G) (nH : H.Normal)
    {a b : G} (h : a * b ∈ H) : b * a ∈ H := by
  -- 因 H 正规，共轭 b·(a·b)·b⁻¹ ∈ H；化简得 b·a ∈ H
  have h2 := nH.conj_mem (a * b) h b
  have : b * (a * b) * b⁻¹ = b * a := by
    group
  rwa [this] at h2

/-- **平凡子群正规**：只含单位元的子群是正规子群。 
> **Entry**: abstract-algebra.group.normal-/
theorem normal_bot {G : Type*} [Group G] : (⊥ : Subgroup G).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have hn1 : n = 1 := Subgroup.mem_bot.mp hn
  rw [hn1, mul_one, mul_inv_cancel]
  exact Subgroup.mem_bot.mpr rfl

/-- **全子群正规**：整个群自身是正规子群。 
> **Entry**: abstract-algebra.group.normal-/
theorem normal_top {G : Type*} [Group G] : (⊤ : Subgroup G).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  exact Subgroup.mem_top (g * n * g⁻¹)

/-- **商群投影保乘法**：自然同态 `mk : G → G⧸H` 是同态（`↑(a*b) = ↑a * ↑b`）。 
> **Entry**: abstract-algebra.group.normal-/
theorem quotient_mk_mul {G : Type*} [Group G] (H : Subgroup G) (nH : H.Normal) (a b : G) :
    QuotientGroup.mk (s := H) (a * b) =
      QuotientGroup.mk (s := H) a * QuotientGroup.mk (s := H) b := by
  exact QuotientGroup.mk_mul H a b

/-- **商群单位元**：商群的单位元是 `↑1`（H 所在的陪集）。 
> **Entry**: abstract-algebra.group.normal-/
theorem quotient_mk_one {G : Type*} [Group G] (H : Subgroup G) (nH : H.Normal) :
    QuotientGroup.mk (s := H) (1 : G) = 1 := by
  exact QuotientGroup.mk_one H

/-- **商群取逆保持**：商群中 `↑(a⁻¹) = (↑a)⁻¹`。 
> **Entry**: abstract-algebra.group.normal-/
theorem quotient_mk_inv {G : Type*} [Group G] (H : Subgroup G) (nH : H.Normal) (a : G) :
    QuotientGroup.mk (s := H) (a⁻¹) = (QuotientGroup.mk (s := H) a)⁻¹ := by
  exact QuotientGroup.mk_inv H a

/-! ### 商映射的泛性质 -/

/-- 商投影 `G → G/H` 的核恰好是 H。
> **Entry**: abstract-algebra.group.normal-/
theorem quotient_projection_kernel {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] :
    (QuotientGroup.mk' H).ker = H := by
  exact QuotientGroup.ker_mk' H

/-- **商群泛性质的存在部分**：若 `H ≤ ker f`，则 f 唯一地下降为从 `G/H` 出发的同态。
这里先构造下降后的同态；唯一性在 `quotientLift_unique` 中给出。
> **Entry**: abstract-algebra.group.normal-/
def quotientLift {G N : Type*} [Group G] [Group N]
    (H : Subgroup G) [H.Normal] (f : G →* N) (hker : H ≤ f.ker) :
    G ⧸ H →* N :=
  QuotientGroup.lift H f hker

/-- 下降同态在陪集代表元上的计算公式：`f̄(gH)=f(g)`。
> **Entry**: abstract-algebra.group.normal-/
theorem quotientLift_mk {G N : Type*} [Group G] [Group N]
    (H : Subgroup G) [H.Normal] (f : G →* N) (hker : H ≤ f.ker) (g : G) :
    quotientLift H f hker (QuotientGroup.mk' H g) = f g := by
  exact QuotientGroup.lift_mk' H hker g

/-- 下降同态与商投影复合后恢复原同态。
> **Entry**: abstract-algebra.group.normal-/
theorem quotientLift_comp_projection {G N : Type*} [Group G] [Group N]
    (H : Subgroup G) [H.Normal] (f : G →* N) (hker : H ≤ f.ker) :
    (quotientLift H f hker).comp (QuotientGroup.mk' H) = f := by
  exact QuotientGroup.lift_comp_mk' H f hker

/-- **商群泛性质的唯一性部分**：任何与商投影复合后等于 f 的同态，都等于规范下降
`quotientLift H f hker`。证明利用商投影满射，把商群元素取成某个代表元的像。
> **Entry**: abstract-algebra.group.normal-/
theorem quotientLift_unique {G N : Type*} [Group G] [Group N]
    (H : Subgroup G) [H.Normal] (f : G →* N) (hker : H ≤ f.ker)
    (q : G ⧸ H →* N) (hq : q.comp (QuotientGroup.mk' H) = f) :
    q = quotientLift H f hker := by
  apply MonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
  have hqg := DFunLike.congr_fun hq g
  change q (QuotientGroup.mk' H g) = f g at hqg
  rw [hqg, quotientLift_mk]

/-- **指数 2 子群必正规**：若 H 在 G 中的指数 [G:H] = 2（恰有两个陪集），则 H 是正规子群。
  教材经典定理：指数最小的非平凡子群必正规。 
> **Entry**: abstract-algebra.group.index-two-/
theorem normal_of_index_two {G : Type*} [Group G] (H : Subgroup G) (hH : H.index = 2) :
    H.Normal := by
  exact Subgroup.normal_of_index_eq_two hH

/-- **同态核元素刻画**：x 在核中 ⟺ f(x) = 1（核 = 映到单位元的元素集）。 
> **Entry**: abstract-algebra.group.hom-/
theorem hom_mem_ker {G M : Type*} [Group G] [MulOneClass M] (f : G →* M) (x : G) :
    x ∈ f.ker ↔ f x = 1 := by
  exact MonoidHom.mem_ker (f := f)

/-- 恒等同态在每个元素上的值就是该元素本身。
> **Entry**: abstract-algebra.group.hom-/
theorem hom_id_apply {G : Type*} [Group G] (x : G) :
    MonoidHom.id G x = x := by rfl

/-- 复合同态逐点满足 `(g ∘ f)(x)=g(f(x))`。
> **Entry**: abstract-algebra.group.hom-/
theorem hom_comp_apply {G N P : Type*} [Group G] [Group N] [Group P]
    (g : N →* P) (f : G →* N) (x : G) :
    g.comp f x = g (f x) := by rfl

/-- 子群逆像的元素刻画：`x ∈ f⁻¹(H)` 当且仅当 `f(x) ∈ H`。
> **Entry**: abstract-algebra.group.hom-/
theorem hom_mem_comap {G N : Type*} [Group G] [Group N]
    (f : G →* N) (H : Subgroup N) (x : G) :
    x ∈ Subgroup.comap f H ↔ f x ∈ H := by rfl

/-- 子群像的元素刻画：`y ∈ f(H)` 当且仅当存在 `x ∈ H` 使 `f(x)=y`。
> **Entry**: abstract-algebra.group.hom-/
theorem hom_mem_map {G N : Type*} [Group G] [Group N]
    (f : G →* N) (H : Subgroup G) (y : N) :
    y ∈ Subgroup.map f H ↔ ∃ x, x ∈ H ∧ f x = y := by
  rfl

/-- 复合同态的核是后一同态之核沿前一同态的逆像。
> **Entry**: abstract-algebra.group.hom-/
theorem hom_ker_comp {G N P : Type*} [Group G] [Group N] [Group P]
    (g : N →* P) (f : G →* N) :
    (g.comp f).ker = Subgroup.comap f g.ker := by
  rfl

/-- 复合同态的像是前一同态像在后一同态下的像。
> **Entry**: abstract-algebra.group.hom-/
theorem hom_range_comp {G N P : Type*} [Group G] [Group N] [Group P]
    (g : N →* P) (f : G →* N) :
    (g.comp f).range = Subgroup.map g f.range := by
  exact MonoidHom.range_comp g f

/-- **同态值域元素刻画**：y 在值域中 ⟺ 存在 x 使 f(x) = y。 
> **Entry**: abstract-algebra.group.hom-/
theorem hom_mem_range {G N : Type*} [Group G] [Group N] (f : G →* N) (y : N) :
    y ∈ f.range ↔ ∃ x : G, f x = y := by
  exact MonoidHom.mem_range (f := f)

/-- **同态保单位元**：f(1) = 1。 
> **Entry**: abstract-algebra.group.hom-/
theorem hom_map_one {G M : Type*} [Group G] [Group M] (f : G →* M) : f 1 = 1 := by
  exact f.map_one

/-- **同态保乘法**：f(a·b) = f(a)·f(b)。 
> **Entry**: abstract-algebra.group.hom-/
theorem hom_map_mul {G M : Type*} [Group G] [Monoid M] (f : G →* M) (a b : G) :
    f (a * b) = f a * f b := by
  exact f.map_mul a b

/-- **同态保逆**：f(a⁻¹) = (f a)⁻¹。 
> **Entry**: abstract-algebra.group.hom-/
theorem hom_map_inv {G N : Type*} [Group G] [Group N] (f : G →* N) (a : G) :
    f a⁻¹ = (f a)⁻¹ := by
  -- f a⁻¹ · f a = f(a⁻¹·a) = f 1 = 1，故 f a⁻¹ = (f a)⁻¹
  apply eq_inv_of_mul_eq_one_left
  calc
    f a⁻¹ * f a = f (a⁻¹ * a) := by rw [f.map_mul]
    _ = f 1 := by rw [inv_mul_cancel]
    _ = 1 := by rw [f.map_one]

/-- **单射 ⟺ 核平凡**：群同态 f 是单射当且仅当其核只含单位元。 
> **Entry**: abstract-algebra.group.hom-/
theorem hom_injective_iff_ker_bot {G M : Type*} [Group G] [MulOneClass M] (f : G →* M) :
    f.ker = ⊥ ↔ Function.Injective f := by
  exact MonoidHom.ker_eq_bot_iff f

/-- **满射 ⟺ 值域为全群**：群同态 f 是满射当且仅当其值域是整个 N。 
> **Entry**: abstract-algebra.group.hom-/
theorem hom_surjective_iff_range_top {G N : Type*} [Group G] [Group N] (f : G →* N) :
    f.range = ⊤ ↔ Function.Surjective f := by
  exact MonoidHom.range_eq_top (f := f)

/-- 双射群同态可规范升级为群同构。
> **Entry**: abstract-algebra.group.hom-/
noncomputable def homEquivOfBijective {G N : Type*} [Group G] [Group N]
    (f : G →* N) (hf : Function.Bijective f) : G ≃* N :=
  MulEquiv.ofBijective f hf

/-- **第一同构定理的显式形式**：群同态 f 诱导规范同构 `G/ker(f) ≃ im(f)`。
与只陈述“存在某个同构”相比，这个定义可以直接用于后续计算。
> **Entry**: abstract-algebra.group.hom-/
noncomputable def firstIsomorphism {G N : Type*} [Group G] [Group N]
    (f : G →* N) : G ⧸ f.ker ≃* f.range :=
  QuotientGroup.quotientKerEquivRange f

/-- 第一同构定理的规范同构把 `x ker(f)` 送到值域中的 `f(x)`。
> **Entry**: abstract-algebra.group.hom-/
theorem firstIsomorphism_apply_mk {G N : Type*} [Group G] [Group N]
    (f : G →* N) (x : G) :
    firstIsomorphism f (QuotientGroup.mk' f.ker x) =
      ⟨f x, ⟨x, rfl⟩⟩ := by
  rfl

/-- **同态基本定理（第一同构定理）**：G/ker(f) ≅ im(f)。
  商群 G/ker f 与 f 的值域同构。 
> **Entry**: abstract-algebra.group.hom-/
theorem first_isomorphism_theorem {G N : Type*} [Group G] [Group N] (f : G →* N) :
    Nonempty (G ⧸ f.ker ≃* f.range) := by
  exact ⟨firstIsomorphism f⟩

/-- 群同构保持元素阶。
> **Entry**: abstract-algebra.group.hom-/
theorem mulEquiv_preserves_order {G N : Type*} [Group G] [Group N]
    (e : G ≃* N) (x : G) :
    orderOf (e x) = orderOf x := by
  exact e.orderOf_eq x

/-- 群同构保持群的基数。
> **Entry**: abstract-algebra.group.hom-/
theorem mulEquiv_preserves_card {G N : Type*} [Group G] [Group N]
    (e : G ≃* N) : Nat.card G = Nat.card N := by
  exact Nat.card_congr e.toEquiv

end AbstractAlgebra.Group

end SandronesLibrary
