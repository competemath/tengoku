/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Relations —— 等价关系与商集（浅层，支撑实数构造）

本文件当前条目：

* **settheory.set.relations.equivalence-class-eq**：等价类相等 ⟺ 元素等价
  （`⟦x⟧ = ⟦y⟧ ↔ x ≈ y`）。
* **settheory.set.relations.quotient-surj**：商映射满射。

> 深度说明：这里只铺"够用"的商集基础——实数用有理数柯西序列的等价类构造时，
> 需要的就是 `Quotient`、`Quotient.eq` 与商映射的满射性。深层的商集理论
> （分划与等价类的对应、商结构的一般理论）留给抽象代数阶段。
-/

namespace SandronesLibrary

namespace SetTheory.Relations

/--
> **Entry**: settheory.set.relations.equivalence-class-eq
> **一句话**: 两个元素的等价类相等，当且仅当它们等价：⟦x⟧ = ⟦y⟧ ↔ x ≈ y。
> **直觉**: 商集就是把"等价的元素钉成同一个点"——钉到一起 ⟺ 本来就等价。
> **依赖**: 无（直接使用 mathlib 的 Quotient.eq，即商集的定义本质）
> **mathlib**: `Quotient.eq`-/
theorem equivalence_class_eq {α : Type*} (s : Setoid α) (x y : α) :
    Quotient.mk s x = Quotient.mk s y ↔ s x y := by
  -- 思路：这不是"要证明的结论"，而是商集构造的消元公理本身（Quotient.eq）。
  -- 商类型 Quotient s 的定义保证：两个商值相等 ⟺ 底下元素按 s 等价。
  exact Quotient.eq

/--
> **Entry**: settheory.set.relations.quotient-surj
> **一句话**: 商映射 π : x ↦ ⟦x⟧ 是满射。
> **直觉**: 商集没有"多余"元素——每个商元素都来自原集合的某个代表元。
> **依赖**: 无
> **mathlib**: `Quotient.mk_surjective`-/
theorem quotient_surjective {α : Type*} (s : Setoid α) :
    Function.Surjective (Quotient.mk s) := by
  -- 思路：展开"满射"即 ∀ q, ∃ x, ⟦x⟧ = q。商类型的任何元素 q 由某个 x 生成
  -- （商类型的定义/归纳原理），所以存在性自动成立。
  exact Quotient.mk_surjective

end SetTheory.Relations

end SandronesLibrary
