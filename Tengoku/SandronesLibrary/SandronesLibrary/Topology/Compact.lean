/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topology / Compact —— 紧致性与分离公理（点集拓扑第一学期 T2）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **topology.compact.def**（紧致有限覆盖定义/有限子覆盖抽取/连续像紧/有限并紧）✅。
* **topology.compact.closed-bdd**（闭区间紧）✅。
* **topology.compact.finite**（T2 中紧集闭/紧集交闭）✅。
* **topology.compact.tychonoff**（Tychonoff 定理：紧集的积紧）✅。

> **语言说明**：点集拓扑阶段（§Phase4）mathlib 的 `IsCompact`/`CompactSpace`/`T1Space`/
> `T2Space`/`NormalSpace` 等**教材结构可直接出现在签名**。
-/

namespace SandronesLibrary

namespace Topology.Compact

/-- **有限子覆盖抽取**：紧集的开覆盖存在有限子覆盖。 
> **Entry**: topology.compact.def
@isnad1 id=ex.3h4v.s6.5139d3cac12c from=translated src=- shape=fa802b9a vocab=1dea05d3
-/
theorem compact_elim_finite_subcover {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s) {ι : Type*} (U : ι → Set X) (hUo : ∀ i : ι, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i := by
  exact hs.elim_finite_subcover U hUo hsU

/-- **连续像紧**：紧集的连续像是紧集。 
> **Entry**: topology.compact.def
@isnad1 id=iscompac.2h4v.s5.7c536d887add from=translated src=- shape=8ccdb3e2 vocab=46fd50e7
-/
theorem compact_image_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsCompact s) {f : X → Y} (hf : Continuous f) : IsCompact (f '' s) := by
  exact hs.image hf

/-- **紧集的有限并仍紧**。 
> **Entry**: topology.compact.def
@isnad1 id=iscompac.2h3v.s4.fdca9499a849 from=translated src=- shape=0540dca0 vocab=24153e3e
-/
theorem compact_union {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := by
  exact hs.union ht

/-- **单点集紧**。 
> **Entry**: topology.compact.def
@isnad1 id=iscompac.0h2v.s4.0bb24cb75918 from=translated src=- shape=28391ba4 vocab=50541fde
-/
theorem compact_singleton {X : Type*} [TopologicalSpace X] (x : X) : IsCompact ({x} : Set X) := by
  -- 教材：单点集的任意开覆盖 {Uᵢ} 中，含 x 的那个 Uᵢ 即构成有限子覆盖
  rw [isCompact_iff_finite_subcover]
  intro ι U hUo hsub
  have hx : x ∈ ⋃ i : ι, U i := hsub (by simp)
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  refine ⟨{i}, ?_⟩
  intro y hy
  have hyx : y = x := by simpa using hy
  rw [hyx]
  exact Set.mem_biUnion (by simp) hxi

/-- **闭区间紧**（Heine-Borel 的基础）：ℝ 上闭区间 [a,b] 紧。 
> **Entry**: topology.compact.closed-bdd
@isnad1 id=iscompac.0h2v.s4.167d279ebe72 from=translated src=- shape=dc04ab9d vocab=80a90528
-/
theorem compact_Icc {a b : ℝ} : IsCompact (Set.Icc a b) := by
  exact isCompact_Icc

/-- **T2 中紧集是闭集**：Hausdorff 空间中紧集必闭。 
> **Entry**: topology.compact.finite
@isnad1 id=isclosed.1h2v.s4.0f2b5571f9f3 from=translated src=- shape=b36b1524 vocab=9d491f8d
-/
theorem compact_isClosed_of_t2 {X : Type*} [TopologicalSpace X] [T2Space X] {s : Set X}
    (hs : IsCompact s) : IsClosed s := by
  exact hs.isClosed

/-- **T2 中紧集的交仍紧**：Hausdorff 空间中两个紧集的交紧。 
> **Entry**: topology.compact.finite
@isnad1 id=iscompac.2h3v.s5.25ba551c75ba from=translated src=- shape=536dba1b vocab=bdf0ad83
-/
theorem compact_inter_of_t2 {X : Type*} [TopologicalSpace X] [T2Space X] {s t : Set X}
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∩ t) := by
  exact hs.inter ht

/-- **Tychonoff 定理**：任意族紧集的积是紧集（紧致的乘积保持性）。
  这是拓扑学核心定理（等价于选择公理）。 
> **Entry**: topology.compact.tychonoff
@isnad1 id=iscompac.1h3v.s6.dade04d6d692 from=translated src=- shape=108eab6b vocab=dd8cfe94
-/
theorem tychonoff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {s : ∀ i, Set (X i)} (hs : ∀ i, IsCompact (s i)) :
    IsCompact { x : ∀ i, X i | ∀ i, x i ∈ s i } := by
  exact isCompact_pi_infinite hs

/-- **Tychonoff 定理（Set.pi 版）**：∏ᵢ sᵢ 紧 ⟸ 每个 sᵢ 紧。 
> **Entry**: topology.compact.tychonoff
@isnad1 id=iscompac.1h3v.s5.245722190a39 from=translated src=- shape=6a5e606d vocab=c4939965
-/
theorem tychonoff_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {s : ∀ i, Set (X i)} (hs : ∀ i, IsCompact (s i)) : IsCompact (Set.pi Set.univ s) := by
  exact isCompact_univ_pi hs

/-- **紧空间的积是紧空间**：每个因子紧 ⟹ 积空间紧（CompactSpace 形式）。 
> **Entry**: topology.compact.tychonoff
@isnad1 id=compacts.0h2v.s5.4fee567cb490 from=translated src=- shape=277a5259 vocab=3c5a36c1
-/
theorem compact_space_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i) := by
  infer_instance

end Topology.Compact

end SandronesLibrary
