/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Function —— 函数语言（大一预备）

本文件当前条目：

* **settheory.function.inj-comp**（单射的复合）：`f` 与 `g` 单射 ⇒ `g ∘ f` 单射。
* **settheory.function.surj-comp**（满射的复合）：`f` 与 `g` 满射 ⇒ `g ∘ f` 满射。
* **settheory.function.inject-surject.bijective-iff-inverse**（双射与可逆）：
  `f` 双射 ⟺ 存在逆映射 `g`（左右同时回收）。
-/

namespace SandronesLibrary

namespace SetTheory.Function

/--
> **Entry**: settheory.function.inj-comp
> **一句话**: 两个单射的复合仍是单射。
> **直觉**: "复合不漏信息"：g 的注入性保证 f 的结果不塌缩，f 的注入性保证源头不塌缩。
> **依赖**: 无（单射/复合的直接定义展开）
> **mathlib**: `Function.Injective.comp`
@isnad1 id=injectiv.2h5v.s5.e0a24fdcc0da from=translated src=- shape=6c2e57d7 vocab=8527eb15
-/
theorem injective_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  -- 思路：展开单射定义。假设 (g∘f) a = (g∘f) b，即 g (f a) = g (f b)。
  -- 用 hg 把等式"剥掉一层"得 f a = f b，再用 hf 剥掉第二层得 a = b。
  intro a b h
  apply hf
  apply hg
  exact h

/--
> **Entry**: settheory.function.surj-comp
> **一句话**: 两个满射的复合仍是满射。
> **直觉**: "复合不漏目标"：先由 g 的满射性找到"中间人" b，再由 f 的满射性找到源头 a。
> **依赖**: `settheory.function.inj-comp`（仅作同族引用的示范，本证明本身不依赖它）
> **mathlib**: `Function.Surjective.comp`
@isnad1 id=surjecti.2h5v.s5.71765c431587 from=translated src=- shape=6c2e57d7 vocab=8eaf3503
-/
theorem surjective_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) := by
  -- 思路：目标 ∀ c, ∃ a, (g∘f) a = c。
  -- 从"终点"往回走：hg 给出 b 使 g b = c；hf 给出 a 使 f a = b；组合即得。
  intro c
  rcases hg c with ⟨b, hb⟩
  rcases hf b with ⟨a, ha⟩
  -- 组合：(g∘f) a = g (f a) = g b = c。`simpa` 负责展开复合记号 `Function.comp`。
  exact ⟨a, by simpa [Function.comp] using (congrArg g ha).trans hb⟩

/--
> **Entry**: settheory.function.image-preimage.preimage-union
> **一句话**: 原像保并：f⁻¹[B ∪ C] = f⁻¹[B] ∪ f⁻¹[C]。
> **直觉**: 在集合语言里"f⁻¹"是唯一对并、交都"全通"的操作；而像 f[-] 只保并不保交。
>   这正是分析里总用"原像"来描述开集/闭集的原因。
> **依赖**: `settheory.set.ext`
> **mathlib**: `Set.preimage_union`
@isnad1 id=eq.0h5v.s5.8a1ce8c90282 from=translated src=- shape=6bebd5aa vocab=2db70e6e
-/
theorem preimage_union {α β : Type*} (f : α → β) (B C : Set β) :
    f ⁻¹' (B ∪ C) = f ⁻¹' B ∪ f ⁻¹' C := by
  -- 思路：先用外延性降到元素层；用 mem_preimage 把 x ∈ f⁻¹'S 改成 f x ∈ S；
  -- 剩下的"属于并"两边都是同一个 Or，逐位组装即可。
  ext x
  constructor
  · intro h
    rcases h with hfB | hfC
    · exact Or.inl hfB
    · exact Or.inr hfC
  · rintro (hB | hC)
    · exact Or.inl hB
    · exact Or.inr hC

/--
> **Entry**: settheory.function.image-preimage.preimage-inter
> **一句话**: 原像保交：f⁻¹[B ∩ C] = f⁻¹[B] ∩ f⁻¹[C]。
> **直觉**: 与保并同理——"f x 同时落入 B 与 C" ⇔ 逐坐标都在原像里。
> **依赖**: `settheory.set.ext`
> **mathlib**: `Set.preimage_inter`
@isnad1 id=eq.0h5v.s5.27b07b7cfa2e from=translated src=- shape=6bebd5aa vocab=6258e94e
-/
theorem preimage_inter {α β : Type*} (f : α → β) (B C : Set β) :
    f ⁻¹' (B ∩ C) = f ⁻¹' B ∩ f ⁻¹' C := by
  -- 思路：与 preimage_union 完全平行的结构，只是 Or 换成 And。
  ext x
  constructor
  · rintro ⟨hfB, hfC⟩
    exact ⟨hfB, hfC⟩
  · rintro ⟨hfB, hfC⟩
    exact ⟨hfB, hfC⟩

/--
> **Entry**: settheory.function.inject-surject.bijective-iff-inverse
> **一句话**: 双射 ⟺ 有逆映射：`f` 双射恰有 `g` 满足 `g ∘ f = id` 且 `f ∘ g = id`。
> **直觉**: 双射 = "碰撞不会发生（单射）+ 目标全覆盖（满射）"，
>   两者合在一起恰好让"往回走"的映射存在且唯一。
> **依赖**: 无
> **mathlib**: `Function.bijective_iff_has_inverse`
@isnad1 id=iff.0h3v.s5.c39ace72ae65 from=translated src=- shape=dbb3ddeb vocab=932d8695
-/
theorem bijective_iff_inverse {α β : Type*} (f : α → β) :
    Function.Bijective f ↔
      ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  -- 思路（思维脉络）：教科书论证分两步——
  --   ⇐：有左右逆 ⟹ 单射（左逆回收）与满射（右逆回投）分别成立，故双射；
  --   ⇒：双射给每个 b 唯一"原型" g(b)，构造出的 g 同时是左逆与右逆。
  -- 这里是可直接引用的 mathlib 完整对应（含构造细节），故 `exact` 一步到位。
  exact Function.bijective_iff_has_inverse

end SetTheory.Function

end SandronesLibrary
