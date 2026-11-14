/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.Group

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 群的第二、第三同构定理与对应定理

本文件完成群论中第一同构定理之后的三项标准结果。

* 第二同构定理比较 `H/(H ∩ N)` 与由 `H`、正规子群 `N` 共同生成的子群模 `N`；
* 第三同构定理说明先模 `N` 再模 `M/N`，等价于直接模 `M`；
* 对应定理把 `G/N` 的子群与 `G` 中包含 `N` 的子群作保序一一对应。

这里的 `H ⊔ N` 是子群格中的上确界；当 `N` 正规时，它就是通常教材记作 `HN`
的集合乘积。对应定理不仅保持包含关系，也保持正规性。
-/

namespace SandronesLibrary

namespace AbstractAlgebra.Group

/-- **第二同构定理**：若 `N ◁ G`，则
`H/(H ∩ N) ≃ (H ∨ N)/N`。

右端分母写作 `N.subgroupOf (H ⊔ N)`，表示把 `N` 看成 `H ⊔ N` 的子群；
左端同理把 `H ∩ N` 表示为 `N.subgroupOf H`。
> **Entry**: abstract-algebra.group.iso-theorems-/
noncomputable def secondIsomorphism {G : Type*} [Group G]
    (H N : Subgroup G) [N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  QuotientGroup.quotientInfEquivProdNormalQuotient H N

/-- **第三同构定理**：若 `N ≤ M` 且 `N,M ◁ G`，则
`(G/N)/(M/N) ≃ G/M`。

`M.map (QuotientGroup.mk' N)` 正是商群 `G/N` 中的子群 `M/N`。
> **Entry**: abstract-algebra.group.iso-theorems-/
def thirdIsomorphism {G : Type*} [Group G]
    (N M : Subgroup G) [N.Normal] [M.Normal] (h : N ≤ M) :
    (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M :=
  QuotientGroup.quotientQuotientEquivQuotient N M h

/-- 第三同构的规范映射按 `xN ↦ xM` 工作：二重商中的代表元 `x` 被送到
它模 `M` 的陪集。这也明确了上述同构并非任意选取的同构。
> **Entry**: abstract-algebra.group.iso-theorems
@isnad1 id=eq.1h4v.s11.01537929e6fc from=translated src=- shape=1aca8fb8 vocab=dccf44a4
-/
theorem thirdIsomorphism_apply_mk_mk {G : Type*} [Group G]
    (N M : Subgroup G) [N.Normal] [M.Normal] (h : N ≤ M) (x : G) :
    thirdIsomorphism N M h
        (QuotientGroup.mk' (M.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N x)) =
      QuotientGroup.mk' M x := by
  exact QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk N M h x

/-- **对应定理（子群格定理）**：若 `N ◁ G`，则 `G/N` 的子群与 `G` 中
包含 `N` 的子群保序一一对应。

正向映射取商映射下的原像，逆向映射取商映射下的像；`OrderIso` 同时记录双射性
以及两个方向均保持包含关系。
> **Entry**: abstract-algebra.group.iso-theorems-/
def subgroupCorrespondence {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] :
    Subgroup (G ⧸ N) ≃o { H : Subgroup G // N ≤ H } :=
  QuotientGroup.comapMk'OrderIso N

/-- 对应定理的正向映射是沿规范商映射 `G → G/N` 取原像。
> **Entry**: abstract-algebra.group.iso-theorems
@isnad1 id=eq.0h3v.s8.eec2b47db68f from=translated src=- shape=e0afba6d vocab=31afa1ea
-/
theorem subgroupCorrespondence_apply {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (K : Subgroup (G ⧸ N)) :
    (subgroupCorrespondence N K : Subgroup G) =
      Subgroup.comap (QuotientGroup.mk' N) K := by
  rfl

/-- 对应定理的逆向映射把包含 `N` 的子群沿商映射送入 `G/N`。
> **Entry**: abstract-algebra.group.iso-theorems
@isnad1 id=eq.0h3v.s9.c548f0873ad0 from=translated src=- shape=3ac3625e vocab=9c20317b
-/
theorem subgroupCorrespondence_symm_apply {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (H : { H : Subgroup G // N ≤ H }) :
    (subgroupCorrespondence N).symm H =
      Subgroup.map (QuotientGroup.mk' N) H.1 := by
  rfl

/-- 对应定理保持正规性的正向部分：商群中的正规子群取原像后仍正规。
> **Entry**: abstract-algebra.group.iso-theorems
@isnad1 id=normal.0h3v.s6.f22289a18e34 from=translated src=- shape=10709b0b vocab=e6366e62
-/
theorem subgroupCorrespondence_normal_forward {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (K : Subgroup (G ⧸ N)) [hK : K.Normal] :
    (Subgroup.comap (QuotientGroup.mk' N) K).Normal := by
  exact hK.comap (QuotientGroup.mk' N)

/-- 对应定理保持正规性的逆向部分：`G` 中包含 `N` 的正规子群经商映射
取像后仍是 `G/N` 的正规子群。（正规性的结论本身不需要再次使用包含关系。）
> **Entry**: abstract-algebra.group.iso-theorems
@isnad1 id=normal.0h3v.s5.717a6b804d2b from=translated src=- shape=7b58f055 vocab=eca8bb73
-/
theorem subgroupCorrespondence_normal_backward {G : Type*} [Group G]
    (N H : Subgroup G) [N.Normal] [hH : H.Normal] :
    (Subgroup.map (QuotientGroup.mk' N) H).Normal := by
  exact hH.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end AbstractAlgebra.Group

end SandronesLibrary
