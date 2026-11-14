/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topology / Separation —— 分离公理（点集拓扑第一学期 T2）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **topology.separations**（T1 单点闭/T2 极限唯一/T2 邻域分离/正则判据）✅。
* **topology.separations.urysohn**（Urysohn 引理）✅。

> **语言说明**：点集拓扑阶段（§Phase4）mathlib 的 `T1Space`/`T2Space`/`RegularSpace`/
> `NormalSpace` 等**教材结构可直接出现在签名**。
-/

namespace SandronesLibrary

namespace Topology.Separation

/-- **T1 空间中单点集是闭集**：T1 公理等价于"每个单点集闭"（教材核心）。 
> **Entry**: topology.separations
@isnad1 id=isclosed.0h2v.s4.b0df5769bcfb from=translated src=- shape=2ac7ae37 vocab=02c7339a
-/
theorem t1_singleton_closed {X : Type*} [TopologicalSpace X] [T1Space X] (x : X) :
    IsClosed ({x} : Set X) := by
  exact isClosed_singleton

/-- **T2（Hausdorff）中极限唯一**：Hausdorff 空间中收敛滤子的极限唯一。 
> **Entry**: topology.separations
@isnad1 id=eq.2h6v.s5.eb025654eb0d from=translated src=- shape=3c642c6b vocab=0902b733
-/
theorem t2_tendsto_unique {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {f : Y → X} {l : Filter Y} [l.NeBot] {a b : X}
    (ha : Filter.Tendsto f l (nhds a)) (hb : Filter.Tendsto f l (nhds b)) : a = b := by
  exact tendsto_nhds_unique ha hb

/-- **T2 ⟺ 不同点邻域不相交**：X Hausdorff ⟺ 任意两不同点的邻域滤子不相交。 
> **Entry**: topology.separations
@isnad1 id=iff.0h1v.s5.3971d872c890 from=translated src=- shape=6f6898b0 vocab=09cf07f8
-/
theorem t2_iff_disjoint_nhds {X : Type*} [TopologicalSpace X] :
    T2Space X ↔ Pairwise fun x y : X => Disjoint (nhds x) (nhds y) := by
  exact t2Space_iff_disjoint_nhds

/-- **正则空间的判据**：RegularSpace ⟺ 闭集与外部点可用不相交邻域分离。 
> **Entry**: topology.separations
@isnad1 id=iff.0h1v.s5.1724812bd9d9 from=translated src=- shape=7a44b3e5 vocab=66338ade
-/
theorem regular_iff_closed_nhds {X : Type*} [TopologicalSpace X] :
    RegularSpace X ↔ ∀ {s : Set X} {a : X}, IsClosed s → a ∉ s →
      Disjoint (nhdsSet s) (nhds a) := by
  exact regularSpace_iff X

/-- **T2 ⟹ T1**：Hausdorff 空间是 T1 空间（分离公理层级）。
@isnad1 id=t1space.0h1v.s3.ea6594dcc2ad from=translated src=- shape=c612a321 vocab=39b2eac4
-/
theorem t2_implies_t1 {X : Type*} [TopologicalSpace X] [T2Space X] :
    T1Space X := by
  infer_instance

/-- **T1 单点闭 ⟺ T1**：每个单点集闭 ⟺ 空间是 T1。 
> **Entry**: topology.separations
@isnad1 id=iff.0h1v.s4.940033d85572 from=translated src=- shape=0c25707f vocab=02c7339a
-/
theorem t1_iff_singleton_closed {X : Type*} [TopologicalSpace X] :
    T1Space X ↔ ∀ x : X, IsClosed ({x} : Set X) := by
  constructor
  · intro h x
    exact isClosed_singleton
  · intro h
    -- 构造 T1Space：需要每个点 {x} 闭
    exact ⟨fun x => h x⟩

/-- **Urysohn 引理**：正规空间中两个不相交闭集 s、t 可用连续函数分离——
  存在连续 f : X → ℝ 使 f=0 在 s、f=1 在 t、值域 ⊆ [0,1]。 
> **Entry**: topology.separations.urysohn
@isnad1 id=ex.3h3v.s7.310b378273a2 from=translated src=- shape=1927cc35 vocab=13008ac7
-/
theorem urysohn_lemma {X : Type*} [TopologicalSpace X] [NormalSpace X] {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), Set.EqOn (⇑f) 0 s ∧ Set.EqOn (⇑f) 1 t ∧ ∀ x : X, (f x : ℝ) ∈ Set.Icc 0 1 := by
  exact exists_continuous_zero_one_of_isClosed hs ht hd

end Topology.Separation

end SandronesLibrary
