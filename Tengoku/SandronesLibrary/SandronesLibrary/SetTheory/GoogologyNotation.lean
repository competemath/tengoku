/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.Nat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoogologyNotation —— Conway 链式箭头与 TREE 的定义入口

本文件只建立有限对象及其可核查的定义接口：

* **settheory.googology.conway-chain**：任意有限正整数链的语法，以及长度不超过二时的求值；
* **settheory.googology.tree-function**：有限标号根树、拓扑嵌入、坏序列和 TREE 最大长度关系。

这里没有声称已经实现 Conway 任意长链的递归求值，也没有证明 TREE 最大长度存在，
更没有给出 `TREE(3)` 的数值或未经形式化的大小比较。
-/

namespace SandronesLibrary.SetTheory.GoogologyNotation

/-- Conway 链式箭头的有限语法：一个非空有限自然数列表，且每一项都为正。-/
structure ConwayChain where
  entries : List ℕ
  nonempty : entries ≠ []
  positive : ∀ n ∈ entries, 0 < n
deriving Repr

/-- 当前可执行的受限 Conway 链：一项链或两项链。-/
inductive ConwayShortChain where
  | singleton (a : ℕ)
  | pair (a b : ℕ)
deriving DecidableEq, Repr

/-- 受限链满足 Conway 记号通常采用的正整数输入约定。-/
def ConwayShortChain.Valid : ConwayShortChain → Prop
  | .singleton a => 0 < a
  | .pair a b => 0 < a ∧ 0 < b

/-- 把受限链忘掉“长度不超过二”的信息，得到一般有限链语法。-/
def ConwayShortChain.toChain (c : ConwayShortChain) (h : c.Valid) : ConwayChain :=
  match c with
  | .singleton a =>
      { entries := [a]
        nonempty := by simp
        positive := by
          intro n hn
          have hn' : n = a := by simpa using hn
          subst n
          simpa [ConwayShortChain.Valid] using h }
  | .pair a b =>
      { entries := [a, b]
        nonempty := by simp
        positive := by
          have hab : 0 < a ∧ 0 < b := by
            simpa [ConwayShortChain.Valid] using h
          intro n hn
          have hn' : n = a ∨ n = b := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using hn
          rcases hn' with rfl | rfl
          · exact hab.1
          · exact hab.2 }

/-- Conway 一项链求值为该项本身，两项链 `a → b` 求值为 `a ^ b`。-/
def ConwayShortChain.eval : ConwayShortChain → ℕ
  | .singleton a => a
  | .pair a b => a ^ b

/--
> **Entry**: settheory.googology.conway-chain
> **一句话**: Conway 链式箭头先由有限正整数链组成；本条只对一项与两项链给出总求值。
> **依赖**: 无
> **mathlib**: 无（本库显式语法与受限求值）
@isnad1 id=and.0h2v.s4.7620eb9b9f5d from=translated src=- shape=ef9beafb vocab=4a7af76e
-/
theorem conwayShortChain_equations (a b : ℕ) :
    ConwayShortChain.eval (.singleton a) = a ∧
      ConwayShortChain.eval (.pair a b) = a ^ b := by
  exact ⟨rfl, rfl⟩

/--
有限 `colors` 标号根树的树序表示。`u ≤ₜ v`（即 `ancestor u v`）表示 `u` 是 `v`
的祖先。根固定编号为 `0`；任一顶点的祖先组成一条链，这正是“树而非一般偏序”的条件。-/
structure FiniteLabeledRootedTree (colors : ℕ) where
  vertexCount : ℕ
  hasVertex : 0 < vertexCount
  label : Fin vertexCount → Fin colors
  ancestor : Fin vertexCount → Fin vertexCount → Prop
  ancestor_refl : ∀ v, ancestor v v
  ancestor_trans : ∀ {u v w}, ancestor u v → ancestor v w → ancestor u w
  ancestor_antisymm : ∀ {u v}, ancestor u v → ancestor v u → u = v
  root_ancestor : ∀ v, ancestor ⟨0, hasVertex⟩ v
  ancestors_comparable :
    ∀ {u v w}, ancestor u w → ancestor v w → ancestor u v ∨ ancestor v u

/--
一棵有限标号根树到另一棵的拓扑嵌入证书。顶点映射是单射，保持根与标号，并且
双向保持祖先关系；因此边可以被目标树中的路径拉长，但不同分支不会被压到同一分支。-/
structure TreeTopologicalEmbedding {colors : ℕ}
    (source target : FiniteLabeledRootedTree colors) where
  toFun : Fin source.vertexCount → Fin target.vertexCount
  injective : Function.Injective toFun
  map_root : toFun ⟨0, source.hasVertex⟩ = ⟨0, target.hasVertex⟩
  map_label : ∀ v, target.label (toFun v) = source.label v
  map_ancestor : ∀ u v, target.ancestor (toFun u) (toFun v) ↔ source.ancestor u v

/-- `source` 可拓扑嵌入 `target`。-/
def TreeEmbeds {colors : ℕ}
    (source target : FiniteLabeledRootedTree colors) : Prop :=
  Nonempty (TreeTopologicalEmbedding source target)

/--
长度为 `length` 的 TREE 候选序列：第 `i` 棵树至多有 `i+1` 个顶点，而且任何较早的树
都不能拓扑嵌入任何较晚的树。这里 `Fin length` 从零编号，所以出现 `i+1`。-/
structure TreeBadSequence (colors length : ℕ) where
  tree : Fin length → FiniteLabeledRootedTree colors
  size_bound : ∀ i, (tree i).vertexCount ≤ i.val + 1
  bad : ∀ i j, i < j → ¬ TreeEmbeds (tree i) (tree j)

/-- 对给定标号数 `colors`，存在长度为 `length` 的合格坏序列。-/
def IsTREEAdmissible (colors length : ℕ) : Prop :=
  Nonempty (TreeBadSequence colors length)

/-- `value` 是所有可实现坏序列长度中的最大者；这是 TREE 值的关系式定义入口。-/
def IsTREEValue (colors value : ℕ) : Prop :=
  IsTREEAdmissible colors value ∧
    ∀ length, IsTREEAdmissible colors length → length ≤ value

/--
> **Entry**: settheory.googology.tree-function
> **一句话**: TREE 值是满足逐项大小限制且不含向后拓扑嵌入的有限标号树序列的最大长度。
> **依赖**: 无
> **mathlib**: 无（本库显式有限树、嵌入与坏序列定义）
@isnad1 id=iff.0h2v.s4.1b5e6f05db02 from=translated src=- shape=039a4e2f vocab=18d671c8
-/
theorem treeValue_iff (colors value : ℕ) :
    IsTREEValue colors value ↔
      IsTREEAdmissible colors value ∧
        ∀ length, IsTREEAdmissible colors length → length ≤ value := by
  rfl

end SandronesLibrary.SetTheory.GoogologyNotation
