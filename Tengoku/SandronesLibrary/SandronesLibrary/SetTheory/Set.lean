/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Set —— 集合语言（大一预备）

本文件当前条目：

* **settheory.set.ext**（外延性原理）：两个集合相等 ⟺ 元素完全相同。
* **settheory.set.subset.definition**（子集的逐元素刻画）：
  `A ⊆ B` 当且仅当 `A` 的每个元素都属于 `B`。
* **settheory.set.subset.trans / antisymm / empty-subset**：
  包含关系的传递性、反对称性与空集最小性。
* **settheory.set.operations.inter-distrib**（交对并的分配律）：
  `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`，依赖 `settheory.set.ext`。
* **settheory.set.operations.complement-union**（德摩根律之一）：
  `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`。
* **settheory.set.operations.complement-inter**（德摩根律之二）：
  `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`。
* **settheory.set.operations.diff-inter-complement**（差集与补集）：
  `A \ B = A ∩ Bᶜ`。
-/

namespace SandronesLibrary

namespace SetTheory.Set

/--
> **Entry**: settheory.set.ext
> **一句话**: 两个集合相等当且仅当它们的元素完全相同（外延性原理）。
> **直觉**: 集合由它的元素唯一决定——"集合相等"永远可以退化为"逐元素检查"。
> **依赖**: 无（直接使用 mathlib 的 `Set.ext`）
> **mathlib**: `Set.ext`
@isnad1 id=iff.0h3v.s5.c4a136a48907 from=translated src=- shape=2d9db661 vocab=a4f200f1
-/
theorem set_ext {α : Type*} (A B : Set α) : A = B ↔ ∀ x : α, x ∈ A ↔ x ∈ B := by
  -- 思路：这是集合语言的地基，等价关系 "A = B" 与 "逐元素互属" 互推。
  constructor
  · -- (⇒) 若 A = B，则任意 x 属于 A 当且仅当属于 B（相等的定义）。
    intro h x
    subst h
    exact Iff.rfl
  · -- (⇐) 若元素完全相同，由外延公理（mathlib 的 Set.ext）直接得到相等。
    intro h
    exact Set.ext h

/--
> **Entry**: settheory.set.operations.inter-distrib
> **一句话**: 交对并的分配律：`A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`。
> **直觉**: 集合恒等式 = "把集合语言翻译成命题逻辑，再翻译回来"。
>   外延性把等式化成逐元素判断，逻辑层的分配律自动完成其余工作。
> **依赖**: `settheory.set.ext`
> **mathlib**: `Set.inter_union_distrib_left`
@isnad1 id=eq.0h4v.s5.60b04fd9db20 from=translated src=- shape=6925cec3 vocab=be3e25d8
-/
theorem inter_distrib_left {α : Type*} (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  -- 思路（思维脉络）：目标是一个集合等式。第一反应永远是用外延性（Set.ext）
  -- 把 "集合相等" 降维成 "任意元素的双向属于"。之后每一步只是命题逻辑。
  ext x
  constructor
  · -- (⇒) x ∈ A 且 x ∈ B∪C：分 x ∈ B 或 x ∈ C 两路，各自汇入左侧某一支。
    rintro ⟨hxA, hxBC⟩
    rcases hxBC with hxB | hxC
    · exact Or.inl ⟨hxA, hxB⟩
    · exact Or.inr ⟨hxA, hxC⟩
  · -- (⇐) x ∈ (A∩B) ∪ (A∩C)：无论在哪一支，x 都属于 A，且属于 B 或 C 之一。
    rintro (⟨hxA, hxB⟩ | ⟨hxA, hxC⟩)
    · exact ⟨hxA, Or.inl hxB⟩
    · exact ⟨hxA, Or.inr hxC⟩

/--
> **Entry**: settheory.set.subset.definition
> **一句话**: `A ⊆ B` 当且仅当 `A` 的每个元素都属于 `B`。
> **直觉**: 子集不是额外的代数结构；它就是一个逐元素的全称命题。
> **依赖**: 无
> **mathlib**: 无（`Set.Subset` 的定义展开）
@isnad1 id=iff.0h3v.s5.522b96ba9cc2 from=translated src=- shape=8ccc5ba7 vocab=6641aca1
-/
theorem subset_iff_forall_mem {α : Type*} (A B : Set α) :
    A ⊆ B ↔ ∀ x : α, x ∈ A → x ∈ B := by
  -- `A ⊆ B` 在 Lean 中定义为右侧的逐元素函数类型，因此两边定义相同。
  rfl

/--
> **Entry**: settheory.set.subset.trans
> **一句话**: 集合包含关系是传递的：A ⊆ B 且 B ⊆ C ⇒ A ⊆ C。
> **直觉**: "子集"链可以一路延伸——元素属于 A 就属于 B，属于 B 就属于 C。
> **依赖**: 无
> **mathlib**: `Set.Subset.trans`
@isnad1 id=le.2h4v.s5.9101181de213 from=translated src=- shape=dfa7b16b vocab=9cb0124d
-/
theorem subset_trans {α : Type*} {A B C : Set α} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  -- 思路：展开 A ⊆ C 为逐元素判断；x ∈ A 经 hAB 得 x ∈ B，再经 hBC 得 x ∈ C。
  intro x hxA
  exact hBC (hAB hxA)

/--
> **Entry**: settheory.set.subset.antisymm
> **一句话**: 双向包含推出相等：A ⊆ B 且 B ⊆ A ⇒ A = B（包含关系的反对称性）。
> **直觉**: 外延性原理的"包含形式"——两边互相装下对方，就是同一个集合。
> **依赖**: `settheory.set.ext`
> **mathlib**: `Set.Subset.antisymm`
@isnad1 id=eq.2h3v.s4.3846df1ef5b3 from=translated src=- shape=24bfee2c vocab=9cb0124d
-/
theorem subset_antisymm {α : Type*} (A B : Set α) (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  -- 思路：用外延性（settheory.set.ext）把"相等"降到逐元素双向属于；
  -- 两个方向正是手里的两条包含。
  apply (set_ext A B).2
  intro x
  constructor
  · intro hxA
    exact hAB hxA
  · intro hxB
    exact hBA hxB

/--
> **Entry**: settheory.set.empty-subset
> **一句话**: 空集是任何集合的子集：∅ ⊆ A。
> **直觉**: "没有一个元素需要检查"，所以条件空真（vacuous truth）。
> **依赖**: 无
> **mathlib**: `Set.empty_subset`
@isnad1 id=le.0h2v.s4.306142e74d95 from=translated src=- shape=bb6dcd58 vocab=b0a1a931
-/
theorem empty_subset {α : Type*} (A : Set α) : (∅ : Set α) ⊆ A := by
  -- 思路：x ∈ ∅ 是不可能的（x ∈ ∅ 定义上就是 False），无事可证。
  intro x hx
  exact False.elim hx

/--
> **Entry**: settheory.set.operations.complement-union
> **一句话**: 德摩根律（之一）：并集的补集 = 补集的交集：`(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`。
> **直觉**: "既不属于 A 也不属于 B" 就是 "不属于 A 且不属于 B"——取补把 ∪ 换成 ∩。
> **依赖**: 无
> **mathlib**: `Set.compl_union`
@isnad1 id=eq.0h3v.s5.2df7e97143a9 from=translated src=- shape=be87d72e vocab=005029cb
-/
theorem complement_union {α : Type*} (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  -- 思路（构造性）：外延性把等式降到逐元素判断。
  --   x ∈ (A∪B)ᶜ ⟺ ¬(x∈A ∨ x∈B)；
  --   直觉主义下 ¬(P∨Q) = ¬P ∧ ¬Q 是对称可证的，
  --   全程只用 Or/And 消解，不依赖排中律或选择公理。
  ext x
  constructor
  · intro hx
    constructor
    · intro hxA
      exact hx (Or.inl hxA)
    · intro hxB
      exact hx (Or.inr hxB)
  · rintro ⟨hxA, hxB⟩ hx
    rcases hx with hx | hx
    · exact hxA hx
    · exact hxB hx

/--
> **Entry**: settheory.set.operations.complement-inter
> **一句话**: 德摩根律（之二）：交集的补集 = 补集的并集：`(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`。
> **直觉**: "不属于 A 或不属于 B"（不是"同时属于 A 与 B"）——取补把 ∩ 换成 ∪。
> **依赖**: 无
> **mathlib**: `Set.compl_inter`
@isnad1 id=eq.0h3v.s5.37cf132f7ddf from=translated src=- shape=be87d72e vocab=005029cb
-/
theorem complement_inter {α : Type*} (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  -- 思路（经典，必要）：这是德摩根的另一半，正向方向
  --   ¬(x∈A ∧ x∈B) ⟹ ¬(x∈A) ∨ ¬(x∈B) 在直觉主义逻辑里不可证
  --   （它等价于对 x∈A 的排中律），因此这条在构造性形式化下
  --   必然依赖 Classical.choice，无法像 complement-union 那样改写。
  rw [Set.compl_inter]

/--
> **Entry**: settheory.set.operations.diff-inter-complement
> **一句话**: 差集可以写作"属于 A 且不属于 B"：`A \ B = A ∩ Bᶜ`。
> **直觉**: 差集 A∖B 就是"从 A 里划掉 B 的部分"，翻译成交集与补集的语言。
> **依赖**: 无
> **mathlib**: `Set.diff_eq`
@isnad1 id=eq.0h3v.s4.cf48e940b1b3 from=translated src=- shape=a95f84b8 vocab=61490da6
-/
theorem diff_inter_complement {α : Type*} (A B : Set α) : A \ B = A ∩ Bᶜ := by
  -- 思路：mathlib 把差集直接定义为 `s \ t = s ∩ tᶜ`，这就是定义本身。
  exact Set.sdiff_eq A B

end SetTheory.Set

end SandronesLibrary
