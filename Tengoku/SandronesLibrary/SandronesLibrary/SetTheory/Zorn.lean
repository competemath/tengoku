/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Zorn —— Zorn 引理与极大元（选择公理族基础）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **settheory.zorn.zorn**（Zorn 引理：偏序集每条链有上界 ⟹ 含极大元）。
* **settheory.zorn.chain**（链的定义/极大元）。

> **语言说明**：Zorn 引理是数学公理级工具（等价于选择公理），承载极大理想存在性、
> 向量空间基存在性、Tychonoff 定理等。mathlib 的 `IsChain`/`BddAbove`/`IsMax` 可直接使用。
-/

namespace SandronesLibrary

namespace SetTheory.Zorn

/-- **极大元**：m 是极大元 ⟺ 没有比 m 更大的元素。 
> **Entry**: settheory.zorn.zorn-/
theorem isMax_def {X : Type*} [LE X] (m : X) :
    IsMax m ↔ ∀ a : X, m ≤ a → a ≤ m := by
  rfl

/-- **Zorn 引理**（教材形式）：非空偏序集中，若每条链都有上界，则存在极大元。
  等价于选择公理，是证明极大理想/基存在性的公理级工具。 
> **Entry**: settheory.zorn.zorn-/
theorem zorn_lemma {X : Type*} [Preorder X] [Nonempty X]
    (h : ∀ c : Set X, IsChain (fun x y : X => x ≤ y) c → BddAbove c) :
    ∃ m : X, IsMax m := by
  exact zorn_le h

/-- **Zorn 引理（子集族版，⊆ 序）**：子集族 S 中每条 ⊆ 链有上界 ⟹ S 含极大元。
  极大理想/极大子空间存在的直接工具。 
> **Entry**: settheory.zorn.zorn-/
theorem zorn_subset_lemma {X : Type*} (S : Set (Set X))
    (h : ∀ c ⊆ S, IsChain (fun s1 s2 : Set X => s1 ⊆ s2) c →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) :
    ∃ m : Set X, Maximal (fun s : Set X => s ∈ S) m := by
  exact zorn_subset S h

/-- **Zorn 引理（反包含序）**：子集族 S 中每条 ⊇ 链有下界 ⟹ S 含极小元。 
> **Entry**: settheory.zorn.zorn-/
theorem zorn_superset_lemma {X : Type*} (S : Set (Set X))
    (h : ∀ c ⊆ S, IsChain (fun s1 s2 : Set X => s1 ⊆ s2) c →
      ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
    ∃ m : Set X, Minimal (fun s : Set X => s ∈ S) m := by
  exact zorn_superset S h

end SetTheory.Zorn

end SandronesLibrary
