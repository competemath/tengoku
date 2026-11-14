/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.SetTheory.Cardinal.Regular
import Tengoku.Seed.SetTheory.Cardinal.Continuum
import Tengoku.Seed.SetTheory.Cardinal.SchroederBernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / CardinalTheory —— 基数理论基础

本文件当前条目：

* **settheory.cardinal.equinumerous**：以双射定义两个类型等势。
* **settheory.cardinal.comparison**：以单射定义一个类型的基数不大于另一个类型。
* **settheory.cardinal.cantor-bernstein**：双向单射推出等势。
* **settheory.cardinal.cantor-theorem**：任何类型都不与其幂集等势。
* **settheory.cardinal.addition**：以不交并定义基数加法。
* **settheory.cardinal.multiplication**：以笛卡尔积定义基数乘法。
* **settheory.cardinal.exponentiation**：以函数空间定义基数幂。
* **settheory.cardinal.finite-set**：有限类型是与某个标准有限集 `Fin n` 等势的类型。
* **settheory.cardinal.aleph-hierarchy**：`aleph` 依次枚举无限基数。
* **settheory.cardinal.beth-hierarchy**：`beth` 从可数无穷出发反复取幂集大小。
* **settheory.cardinal.cardinal-cofinality**：用基数的初始序数定义其共尾性。
* **settheory.cardinal.regular-singular**：按共尾性是否等于自身区分正则与奇异基数。
* **settheory.cardinal.konig-theorem**：逐坐标严格较小推出基数和严格小于基数积。
* **settheory.cardinal.classical-choice-wellordering**：经典环境中选择函数与良序化原则可用。
* **settheory.cardinal.continuum-hypothesis**：连续统假设的基数等式陈述及独立性边界。
-/

namespace SandronesLibrary.SetTheory.CardinalTheory

open Function

/--
> **Entry**: settheory.cardinal.equinumerous
> **一句话**: 两个类型等势，定义为它们之间存在双射。
> **依赖**: 无
> **mathlib**: `Equiv`-/
def Equinumerous (α β : Type*) : Prop :=
  Nonempty (α ≃ β)

/--
@isnad1 id=iff.0h2v.s4.409f0c196c8a from=translated src=- shape=103837ea vocab=30e6e532
-/
theorem equinumerous_iff_exists_bijective {α β : Type*} :
    Equinumerous α β ↔ ∃ f : α → β, Bijective f := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e, e.bijective⟩
  · rintro ⟨f, hf⟩
    exact ⟨Equiv.ofBijective f hf⟩

/--
> **Entry**: settheory.cardinal.comparison
> **一句话**: `α` 的基数不大于 `β`，定义为存在从 `α` 到 `β` 的单射。
> **依赖**: `settheory.cardinal.equinumerous`
> **mathlib**: `Function.Injective`-/
def CardinalLE (α β : Type*) : Prop :=
  ∃ f : α → β, Injective f

/--
@isnad1 id=and.1h2v.s3.be14cacf62ce from=translated src=- shape=68bf42e7 vocab=6b04f120
-/
theorem equinumerous_implies_both_le {α β : Type*} (h : Equinumerous α β) :
    CardinalLE α β ∧ CardinalLE β α := by
  rcases h with ⟨e⟩
  exact ⟨⟨e, e.injective⟩, ⟨e.symm, e.symm.injective⟩⟩

/--
@isnad1 id=cardinal.0h1v.s2.11aed31b3d7f from=translated src=- shape=7743fad5 vocab=406f7295
-/
theorem cardinalLE_refl (α : Type*) : CardinalLE α α :=
  ⟨id, fun _ _ h => h⟩

/--
@isnad1 id=cardinal.2h3v.s4.132b28c51e33 from=translated src=- shape=a8128290 vocab=406f7295
-/
theorem cardinalLE_trans {α β γ : Type*} (hαβ : CardinalLE α β)
    (hβγ : CardinalLE β γ) : CardinalLE α γ := by
  rcases hαβ with ⟨f, hf⟩
  rcases hβγ with ⟨g, hg⟩
  exact ⟨g ∘ f, hg.comp hf⟩

/--
> **Entry**: settheory.cardinal.cantor-bernstein
> **一句话**: 若 `α` 可单射进 `β`，且 `β` 可单射进 `α`，则二者等势。
> **依赖**: `settheory.cardinal.equinumerous`、`settheory.cardinal.comparison`
> **mathlib**: `Embedding.schroeder_bernstein`、`Equiv.ofBijective`
@isnad1 id=equinume.2h2v.s3.9e5568f9a9e0 from=translated src=- shape=2cf804e2 vocab=6b04f120
-/
theorem cantor_bernstein {α β : Type*} (hαβ : CardinalLE α β) (hβα : CardinalLE β α) :
    Equinumerous α β := by
  rcases hαβ with ⟨f, hf⟩
  rcases hβα with ⟨g, hg⟩
  obtain ⟨h, hh⟩ := Embedding.schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h hh⟩

/--
@isnad1 id=equinume.2h2v.s3.9e5568f9a9e0 from=translated src=- shape=2cf804e2 vocab=6b04f120
-/
theorem cardinalLE_antisymm {α β : Type*} (hαβ : CardinalLE α β)
    (hβα : CardinalLE β α) : Equinumerous α β :=
  cantor_bernstein hαβ hβα

/-- 严格基数比较：可单射进入对方，但对方不能单射回来。-/
def CardinalLT (α β : Type*) : Prop :=
  CardinalLE α β ∧ ¬ CardinalLE β α

/-- 对函数 `f : α → Set α`，对角集合在每个 `x` 处故意与 `f x` 的成员资格相反。-/
def diagonalSet {α : Type*} (f : α → Set α) : Set α :=
  {x | x ∉ f x}

/--
> **Entry**: settheory.cardinal.cantor-theorem
> **一句话**: 不存在从任意类型 `α` 到其幂集 `Set α` 的满射，故幂集严格更大。
> **依赖**: `settheory.cardinal.comparison`
> **mathlib**: 无（本库显式对角线证明）
@isnad1 id=not.0h2v.s3.9e8cdb16e7ae from=translated src=- shape=39bfb020 vocab=c84bcf0e
-/
theorem cantor_no_surjection {α : Type*} (f : α → Set α) : ¬ Surjective f := by
  intro hf
  -- 思路：若 f 枚举了所有子集，对角集合 D 也应等于某个 f a。
  obtain ⟨a, ha⟩ := hf (diagonalSet f)
  by_cases hD : a ∈ diagonalSet f
  · -- 若 a∈D，按 D 的定义有 a∉f(a)，但 f(a)=D 又给 a∈f(a)。
    have hnot : a ∉ f a := hD
    exact hnot (ha ▸ hD)
  · -- 若 a∉D，按 D 的定义有 a∈f(a)，再由 f(a)=D 得 a∈D。
    have hmem : a ∈ f a := by
      simpa [diagonalSet] using hD
    exact hD (ha ▸ hmem)

/--
@isnad1 id=not.0h1v.s2.cec87491a844 from=translated src=- shape=73307998 vocab=67103dfc
-/
theorem cantor_not_equinumerous (α : Type*) : ¬ Equinumerous α (Set α) := by
  rintro ⟨e⟩
  exact cantor_no_surjection e e.surjective

/--
@isnad1 id=cardinal.0h1v.s2.afc1775ae6e1 from=translated src=- shape=62bbbf5d vocab=57d145c4
-/
theorem cardinalLE_powerSet (α : Type*) : CardinalLE α (Set α) := by
  exact ⟨fun x => {x}, Set.singleton_injective⟩

/--
@isnad1 id=not.0h1v.s2.4f3753f3c5c5 from=translated src=- shape=881d7051 vocab=57d145c4
-/
theorem not_cardinalLE_powerSet_reverse (α : Type*) : ¬ CardinalLE (Set α) α := by
  intro h
  exact cantor_not_equinumerous α (cantor_bernstein (cardinalLE_powerSet α) h)

/--
@isnad1 id=cardinal.0h1v.s2.d254b32f76e0 from=translated src=- shape=62bbbf5d vocab=bcde7b94
-/
theorem cantor_strictly_smaller_powerSet (α : Type*) : CardinalLT α (Set α) :=
  ⟨cardinalLE_powerSet α, not_cardinalLE_powerSet_reverse α⟩

universe u v w

/-- 两类对象先贴上左右标签再合并；标签保证原来相同的表示也不会混为一项。-/
def CardinalSum (α : Type u) (β : Type v) : Type (max u v) :=
  Sum α β

/--
> **Entry**: settheory.cardinal.addition
> **一句话**: 两个基数之和，是给两边元素加上不同标签后所得不交并的大小。
> **依赖**: `settheory.cardinal.equinumerous`
> **mathlib**: `Equiv.sumCongr`
@isnad1 id=equinume.1h3v.s4.792cdd23560e from=translated src=- shape=2bcdb681 vocab=cc8a0258
-/
theorem cardinalSum_respects_equinumerous {α : Type u} {α' : Type v} {β : Type w}
    (h : Equinumerous α α') : Equinumerous (CardinalSum α β) (CardinalSum α' β) := by
  rcases h with ⟨e⟩
  exact ⟨Equiv.sumCongr e (Equiv.refl β)⟩

/-- 一个乘法对象是一对 `(a,b)`，即同时选择一个 `α` 元素和一个 `β` 元素。-/
def CardinalProduct (α : Type u) (β : Type v) : Type (max u v) :=
  α × β

/--
> **Entry**: settheory.cardinal.multiplication
> **一句话**: 两个基数之积，是相应两个类型的笛卡尔积的大小。
> **依赖**: `settheory.cardinal.equinumerous`
> **mathlib**: `Equiv.prodCongr`
@isnad1 id=equinume.1h3v.s4.18ed7a0d3fe1 from=translated src=- shape=2bcdb681 vocab=78e7389a
-/
theorem cardinalProduct_respects_equinumerous {α : Type u} {α' : Type v} {β : Type w}
    (h : Equinumerous α α') :
    Equinumerous (CardinalProduct α β) (CardinalProduct α' β) := by
  rcases h with ⟨e⟩
  exact ⟨Equiv.prodCongr e (Equiv.refl β)⟩

/-- `α` 的大小的 `β` 次幂由函数 `β → α` 组成：每个 `β` 位置独立选择一个 `α` 值。-/
def CardinalPower (α : Type u) (β : Type v) : Type (max u v) :=
  β → α

/--
> **Entry**: settheory.cardinal.exponentiation
> **一句话**: 基数幂 `|α|^|β|` 是从 `β` 到 `α` 的全部函数所成类型的大小。
> **依赖**: `settheory.cardinal.equinumerous`
> **mathlib**: `Equiv.arrowCongr`
@isnad1 id=equinume.1h3v.s4.f40c7084e05f from=translated src=- shape=2bcdb681 vocab=abf19991
-/
theorem cardinalPower_respects_equinumerous {α : Type u} {α' : Type v} {β : Type w}
    (h : Equinumerous α α') : Equinumerous (CardinalPower α β) (CardinalPower α' β) := by
  rcases h with ⟨e⟩
  exact ⟨Equiv.arrowCongr (Equiv.refl β) e⟩

/--
> **Entry**: settheory.cardinal.finite-set
> **一句话**: 一个类型有限，是指其元素能与 `0,1,…,n-1` 对应，某个自然数 `n` 即其大小。
> **依赖**: `settheory.cardinal.equinumerous`
> **mathlib**: `Fin`-/
def FiniteByEnumeration (α : Type u) : Prop :=
  ∃ n : ℕ, Equinumerous α (Fin n)

/--
@isnad1 id=ex.1h1v.s3.05f602fd2e88 from=translated src=- shape=e211c314 vocab=a303778c
-/
theorem finiteByEnumeration_has_finite_bound {α : Type u} (h : FiniteByEnumeration α) :
    ∃ n : ℕ, CardinalLE α (Fin n) := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, (equinumerous_implies_both_le hn).1⟩

/-- `AlephLevel o` 是按序数 `o` 编号的第 `o` 个无限基数。-/
noncomputable def AlephLevel (o : Ordinal) : Cardinal :=
  Cardinal.aleph o

/--
> **Entry**: settheory.cardinal.aleph-hierarchy
> **一句话**: `aleph` 层级从可数无穷开始，每个后继层取严格更大的下一个基数。
> **依赖**: `settheory.cardinal.finite-set`
> **mathlib**: `Cardinal.aleph_zero`、`Cardinal.aleph_succ`
@isnad1 id=and.0h1v.s5.ae743ab9e916 from=translated src=- shape=8aba7ef6 vocab=c73e9295
-/
theorem alephLevel_zero_and_successor (o : Ordinal) :
    AlephLevel 0 = Cardinal.aleph0 ∧
      Order.succ (AlephLevel o) = AlephLevel (o + 1) := by
  exact ⟨Cardinal.aleph_zero, Cardinal.succ_aleph o⟩

/-- `BethLevel o` 记录从 `ℵ₀` 开始反复取幂集所得的基数层级。-/
noncomputable def BethLevel (o : Ordinal) : Cardinal :=
  Cardinal.beth o

/--
> **Entry**: settheory.cardinal.beth-hierarchy
> **一句话**: `beth 0=aleph0`，而每个后继层是上一层的幂集大小 `2^κ`。
> **依赖**: `settheory.cardinal.exponentiation`、`settheory.cardinal.aleph-hierarchy`
> **mathlib**: `Cardinal.beth_zero`、`Cardinal.beth_succ`
@isnad1 id=and.0h1v.s5.f675b4c47b22 from=translated src=- shape=f7e28d44 vocab=1686c238
-/
theorem bethLevel_zero_and_successor (o : Ordinal) :
    BethLevel 0 = Cardinal.aleph0 ∧
      BethLevel (Order.succ o) = 2 ^ BethLevel o := by
  exact ⟨Cardinal.beth_zero, Cardinal.beth_succ o⟩

/-- 一个基数的共尾性，是代表它的最小序数 `c.ord` 的共尾性。-/
noncomputable def CardinalCofinality (c : Cardinal) : Cardinal :=
  c.ord.cof

/--
> **Entry**: settheory.cardinal.cardinal-cofinality
> **一句话**: 基数共尾性不超过原基数；它测量需要多长的递增序列才能逼近该基数。
> **依赖**: `settheory.ordinal.cofinality`
> **mathlib**: `Cardinal.cof_ord_le`
@isnad1 id=le.0h1v.s3.3d9213ff43bf from=translated src=- shape=a365602c vocab=46d063af
-/
theorem cardinalCofinality_le (c : Cardinal) : CardinalCofinality c ≤ c := by
  exact Ordinal.cof_ord_le c

/-- 无限基数正则，表示其共尾性就是自身。-/
def RegularCardinal (c : Cardinal) : Prop :=
  Cardinal.aleph0 ≤ c ∧ CardinalCofinality c = c

/-- 无限基数奇异，表示其共尾性严格小于自身。-/
def SingularCardinal (c : Cardinal) : Prop :=
  Cardinal.aleph0 ≤ c ∧ CardinalCofinality c < c

/--
> **Entry**: settheory.cardinal.regular-singular
> **一句话**: 无限基数按共尾性等于自身或严格小于自身，分别称为正则或奇异。
> **依赖**: `settheory.cardinal.cardinal-cofinality`
> **mathlib**: `Cardinal.isRegular_aleph0`
@isnad1 id=regularc.0h0v.s1.b9e375df9b6e from=translated src=- shape=49959d42 vocab=ce6e40e9
-/
theorem aleph0_is_regular : RegularCardinal Cardinal.aleph0 := by
  exact ⟨le_rfl, Cardinal.isRegular_aleph0.cof_ord⟩

/--
@isnad1 id=not.1h1v.s3.ec48f72880f4 from=translated src=- shape=58f8d12c vocab=e4bcc969
-/
theorem regular_not_singular {c : Cardinal} (h : RegularCardinal c) :
    ¬ SingularCardinal c := by
  rintro ⟨_, hs⟩
  exact hs.ne (h.2)

/--
@isnad1 id=or.1h1v.s3.db99976641a5 from=translated src=- shape=f81efce2 vocab=b176704c
-/
theorem infinite_regular_or_singular {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) :
    RegularCardinal c ∨ SingularCardinal c := by
  rcases (cardinalCofinality_le c).lt_or_eq with hlt | heq
  · exact Or.inr ⟨hc, hlt⟩
  · exact Or.inl ⟨hc, heq⟩

/--
> **Entry**: settheory.cardinal.konig-theorem
> **一句话**: 若每个 `κᵢ` 都严格小于相应的 `λᵢ`，则所有 `κᵢ` 的和严格小于所有 `λᵢ` 的积。
> **依赖**: `settheory.cardinal.addition`、`settheory.cardinal.multiplication`
> **mathlib**: `Cardinal.sum_lt_prod`
@isnad1 id=lt.1h3v.s5.aa5cd8bfe209 from=translated src=- shape=b1558420 vocab=4610d473
-/
theorem konig_theorem {ι : Type u} (κ μ : ι → Cardinal.{v})
    (h : ∀ i, κ i < μ i) : Cardinal.sum κ < Cardinal.prod μ := by
  exact Cardinal.sum_lt_prod κ μ h

/-- König 定理的共尾性推论：无限基数的这个幂严格大于它自身。
@isnad1 id=lt.1h1v.s4.e016570f57e8 from=translated src=- shape=03fc70e0 vocab=cef2b6cd
-/
theorem cardinal_lt_power_cofinality {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) :
    c < c ^ CardinalCofinality c := by
  exact Cardinal.lt_power_cof_ord hc

/-- 一个集合族的选择原则：每个纤维非空时，可以同时从每个纤维选出一个元素。-/
def ChoiceFor {ι : Type u} (A : ι → Type v) : Prop :=
  (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i)

/-- 一个类型可良序化，表示其上存在某个良序关系。-/
def WellOrderable (α : Type u) : Prop :=
  ∃ r : α → α → Prop, IsWellOrder α r

/--
> **Entry**: settheory.cardinal.classical-choice-wellordering
> **一句话**: 在 Lean 的经典基础中，任意非空集合族有选择函数，任意类型均可良序化。
> **依赖**: 无（Lean 经典基础直接提供选择与良序关系）
> **mathlib**: `Classical.choice`、`WellOrderingRel`
@isnad1 id=and.0h3v.s3.eb992617b40b from=translated src=- shape=7a29f6c3 vocab=cd7cb9fb
-/
theorem choice_and_wellOrder_available {ι : Type u} (A : ι → Type v) (α : Type w) :
    ChoiceFor A ∧ WellOrderable α := by
  constructor
  · intro h
    exact ⟨fun i => Classical.choice (h i)⟩
  · exact ⟨WellOrderingRel, inferInstance⟩

/-- 连续统假设：自然数幂集的大小恰为第一个不可数基数。-/
def ContinuumHypothesis : Prop :=
  BethLevel (1 : Ordinal.{0}) = AlephLevel (1 : Ordinal.{0})

/--
> **Entry**: settheory.cardinal.continuum-hypothesis
> **一句话**: CH 断言 `2^ℵ₀=ℵ₁`；本库只登记陈述，不声称在 ZFC 内证明或反驳它。
> **依赖**: `settheory.cardinal.aleph-hierarchy`、`settheory.cardinal.beth-hierarchy`
> **mathlib**: `Cardinal.beth_one`
@isnad1 id=iff.0h0v.s5.3466496b23e0 from=translated src=- shape=13c1fdb5 vocab=8e8776d9
-/
theorem continuumHypothesis_iff :
    ContinuumHypothesis ↔
      2 ^ Cardinal.aleph0 = Cardinal.aleph (1 : Ordinal.{0}) := by
  change Cardinal.beth 1 = Cardinal.aleph 1 ↔
    2 ^ Cardinal.aleph0 = Cardinal.aleph 1
  rw [Cardinal.beth_one, Cardinal.two_power_aleph0]

end SandronesLibrary.SetTheory.CardinalTheory
