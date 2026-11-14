/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Cardinal —— 可数性（分析用到的部分）

本文件当前条目：

* **settheory.cardinal.countable-def**：可数定义 = 可嵌入自然数。
* **settheory.cardinal.countable-rat**：有理数可数。
* **settheory.cardinal.uncountable-real**：实数不可数（Cantor 对角线）。
* **settheory.cardinal.countable-union**：可数个可数集的并仍可数。

> 深度说明：这里只做"分析会用到的可数性"（有理数可数、实数不可数、可数并）。
> 基数算术（不可数基数的比较、选择公理下的基数运算）留给抽象代数/集合论阶段。
-/

namespace SandronesLibrary

namespace SetTheory.Cardinal

/--
> **Entry**: settheory.cardinal.countable-def
> **一句话**: 集合可数 ⟺ 存在到 ℕ 的单射（元素可以被自然数"编号"）。
> **直觉**: 能逐个数过来的集合就是可数的；"编号"即单射，保证一个元素只有一个号码。
> **依赖**: 无（mathlib 对 Countable 的定义本身）
> **mathlib**: `countable_iff_exists_injective`-/
theorem countable_iff_injective_nat (α : Type*) :
    Countable α ↔ ∃ f : α → ℕ, Function.Injective f := by
  -- 思路：这是 mathlib 中 Countable 的可操作刻画。若单射 f 存在，
  -- 就按 f 的像把 α 一一列出来；反过来可数集本身给一个 ℕ 方向的枚举。
  exact countable_iff_exists_injective α

/--
> **Entry**: settheory.cardinal.countable-rat
> **一句话**: 有理数集是可数的。
> **直觉**: 分数 p/q 用两个自然数 (p,q) 编码，两个 ℕ 可以配对成一个 ℕ——于是可数。
> **依赖**: 无（mathlib 实例）
> **mathlib**: `Countable ℚ`（实例）-/
theorem countable_rat : Countable ℚ := by
  -- 思路：mathlib 已构造好实例（Cantor 配对 + 分数编码）。数学直觉是：
  -- ℚ 可以沿"分子分母绝对值之和"（高度）逐层枚举，每层有限个，合起来可数。
  infer_instance

/--
> **Entry**: settheory.cardinal.uncountable-real
> **一句话**: 实数集不可数。
> **直觉**: Cantor 对角线：把 [0,1) 的实数排成任何"可数名单"，总能构造一个
>   不在名单里的新实数（在每一位上故意挑一个不同的数字）。
> **依赖**: 无（mathlib 实例）
> **mathlib**: `Uncountable ℝ`（实例）、`not_countable`-/
theorem uncountable_real : ¬ Countable ℝ := by
  -- 思路：直接引用 mathlib 的不可数实例。数学证明（对角线）在叙述层讲，
  -- 因为"名单缺一个"的构造论证在形式化里很长，且 mathlib 已把它做成实例。
  exact not_countable

/--
> **Entry**: settheory.cardinal.countable-union
> **一句话**: 可数个可数集的并仍可数。
> **直觉**: 把每个集合里"第 m 个元素"放到"第 n 个集合"的 (n, m) 位置上，
>   再用配对把 (n,m) 编码成自然数——合并起来仍可枚举。
> **依赖**: 无
> **mathlib**: `Set.countable_iUnion`-/
theorem countable_iUnion {ι α : Type*} [Countable ι] (s : ι → Set α)
    (hs : ∀ i : ι, (s i).Countable) : (⋃ i, s i).Countable := by
  -- 思路：这是"可数个可数集的并可数"的集合形式。数学上靠的是
  -- "配对 ℕ×ℕ 仍可数"（同 countable-rat 的编码直觉）。
  exact Set.countable_iUnion hs

end SetTheory.Cardinal

end SandronesLibrary
