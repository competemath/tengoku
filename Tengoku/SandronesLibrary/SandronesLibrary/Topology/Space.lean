/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topology / Space —— 拓扑空间基础（点集拓扑第一学期 T1）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **topology.space.def**（开闭集公理/开⟺补闭）✅。
* **topology.space.neighborhood**（开集是邻域）✅。
* **topology.space.continuous**（连续⟺开集原像/处处点连续/保极限/恒等/常/复合）✅。
* **topology.space.homeo**（同胚双向连续/双射/保开集）✅。
* **topology.space.subspace**（子空间嵌入/限制/投影/子空间开集刻画）✅。
* **topology.space.connected**（连续像连通/区间连通/同胚保连通）✅。

> **语言说明**：点集拓扑阶段（§Phase4）mathlib 的 `TopologicalSpace`/`IsOpen`/`IsClosed`/
> `Continuous`/`Homeomorph` 等**教材结构可直接出现在签名**（学到什么用什么）。
-/

namespace SandronesLibrary

namespace Topology.Space

/-- **开集公理：空集开**。
@isnad1 id=isopen.0h1v.s3.5f65a4ee23e8 from=translated src=- shape=b8471119 vocab=7a6972fc
-/
theorem topo_isOpen_empty {X : Type*} [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  exact isOpen_empty

/-- **开集公理：全集开**。
@isnad1 id=isopen.0h1v.s3.d4dc7c70017c from=translated src=- shape=84bfdc15 vocab=00690ed6
-/
theorem topo_isOpen_univ {X : Type*} [TopologicalSpace X] : IsOpen (Set.univ : Set X) := by
  exact isOpen_univ

/-- **开集公理：有限交开**：两个开集的交仍开（可归纳到有限个）。 
> **Entry**: topology.space.def
@isnad1 id=isopen.2h3v.s4.2f69c2c84a9d from=translated src=- shape=0540dca0 vocab=86624b91
-/
theorem topo_isOpen_inter {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  exact IsOpen.inter hs ht

/-- **开集公理：任意并开**：一族开集的并仍开。 
> **Entry**: topology.space.def
@isnad1 id=isopen.1h3v.s5.a3b88606af56 from=translated src=- shape=64831ca3 vocab=1980925f
-/
theorem topo_isOpen_iUnion {X : Type*} {ι : Type*} [TopologicalSpace X]
    {f : ι → Set X} (h : ∀ i : ι, IsOpen (f i)) : IsOpen (⋃ i, f i) := by
  exact isOpen_iUnion h

/-- **闭集公理：任意交闭**：一族闭集的交仍闭。 
> **Entry**: topology.space.def
@isnad1 id=isclosed.1h3v.s5.af0b8aecb488 from=translated src=- shape=64831ca3 vocab=04856a1c
-/
theorem topo_isClosed_iInter {X : Type*} {ι : Type*} [TopologicalSpace X]
    {f : ι → Set X} (h : ∀ i : ι, IsClosed (f i)) : IsClosed (⋂ i, f i) := by
  exact isClosed_iInter h

/-- **闭集公理：有限并闭**：两个闭集的并仍闭。 
> **Entry**: topology.space.def
@isnad1 id=isclosed.2h3v.s4.81c63b641bf2 from=translated src=- shape=0540dca0 vocab=d51bf742
-/
theorem topo_isClosed_union {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t) := by
  exact IsClosed.union hs ht

/-- **开 ⟺ 补闭**：s 开 ⟺ s 的补集闭。 
> **Entry**: topology.space.def
@isnad1 id=iff.0h2v.s4.448a654d538b from=translated src=- shape=8072668f vocab=084ddb49
-/
theorem topo_isOpen_iff_isClosed_compl {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsOpen s ↔ IsClosed sᶜ := by
  exact isClosed_compl_iff.symm

/-- **连续 ⟺ 开集原像开**（教材定义）：f 连续 ⟺ 每个开集的原像是开集。 
> **Entry**: topology.space.continuous
@isnad1 id=iff.0h3v.s5.67e196f074bf from=translated src=- shape=90a889fa vocab=b2283c1d
-/
theorem topo_continuous_iff_isOpen_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ s : Set Y, IsOpen s → IsOpen (f ⁻¹' s) := by
  exact continuous_def

/-- **连续函数开集原像开**：f 连续 ⟹ 开集的原像是开集。 
> **Entry**: topology.space.continuous
@isnad1 id=isopen.2h4v.s5.e28542f33b32 from=translated src=- shape=086a41b9 vocab=b2283c1d
-/
theorem topo_continuous_isOpen_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsOpen s) : IsOpen (f ⁻¹' s) := by
  exact Continuous.isOpen_preimage hf s hs

/-- **连续 ⟺ 处处点连续**：f 连续 ⟺ 在每个点都连续。 
> **Entry**: topology.space.continuous
@isnad1 id=iff.0h3v.s4.7edd326feb76 from=translated src=- shape=40286d02 vocab=8b3078f8
-/
theorem topo_continuous_iff_continuousAt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} : Continuous f ↔ ∀ x : X, ContinuousAt f x := by
  exact continuous_iff_continuousAt

/-- **恒等映射连续**。 
> **Entry**: topology.space.continuous
@isnad1 id=continuo.0h1v.s3.182d82a29a9b from=translated src=- shape=746c6e19 vocab=9883ef1b
-/
theorem topo_continuous_id {X : Type*} [TopologicalSpace X] : Continuous (id : X → X) := by
  exact continuous_id

/-- **常函数连续**。 
> **Entry**: topology.space.continuous
@isnad1 id=continuo.0h3v.s4.c9c826646a15 from=translated src=- shape=e5f2b370 vocab=e04c2faa
-/
theorem topo_continuous_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    Continuous (fun _ : X => y) := by
  exact continuous_const

/-- **连续函数的复合连续**。 
> **Entry**: topology.space.continuous
@isnad1 id=continuo.2h5v.s5.c91be1fe2bc2 from=translated src=- shape=d23617fe vocab=8db66b84
-/
theorem topo_continuous_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hg : Continuous g) (hf : Continuous f) : Continuous (g ∘ f) := by
  exact hg.comp hf

/-- **连续 ⟹ 收敛穿过**：f 连续且 xₙ → x，则 f(xₙ) → f(x)（滤子语言）。 
> **Entry**: topology.space.continuous
@isnad1 id=tendsto.1h4v.s5.6d3cf9948054 from=translated src=- shape=3a29c1e1 vocab=536538d6
-/
theorem topo_continuous_tendsto {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (x : X) : Filter.Tendsto f (nhds x) (nhds (f x)) := by
  exact hf.tendsto x

/-- **开集是其中每点的邻域**：开集含 x ⟹ x 的邻域。 
> **Entry**: topology.space.neighborhood
@isnad1 id=mem.2h3v.s5.fba5aa0aeabe from=translated src=- shape=836977f5 vocab=6c3c8507
-/
theorem topo_isOpen_mem_nhds {X : Type*} [TopologicalSpace X] {x : X} {s : Set X}
    (hs : IsOpen s) (hx : x ∈ s) : s ∈ nhds x := by
  exact hs.mem_nhds hx

/-- **同胚的定义性质：双射且双向连续**：同胚 h 是连续双射，其逆也连续。 
> **Entry**: topology.space.homeo
@isnad1 id=continuo.0h3v.s5.6d5d8998d185 from=translated src=- shape=bb88c798 vocab=0ce7fef3
-/
theorem homeomorph_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Continuous h := by
  exact h.continuous

/-- **同胚的逆连续**：同胚的逆映射也是同胚（双向连续）。 
> **Entry**: topology.space.homeo
@isnad1 id=continuo.0h3v.s5.51457234282a from=translated src=- shape=7688f674 vocab=30776c29
-/
theorem homeomorph_invFun_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Continuous h.symm := by
  exact h.symm.continuous

/-- **同胚是双射**。 
> **Entry**: topology.space.homeo
@isnad1 id=bijectiv.0h3v.s5.b2f989009c45 from=translated src=- shape=bb88c798 vocab=d0d61277
-/
theorem homeomorph_bijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Function.Bijective h := by
  exact h.bijective

/-- **同胚保开集**：同胚把开集映成开集（且只把开集映成开集）。 
> **Entry**: topology.space.homeo
@isnad1 id=iff.0h4v.s5.427f9023c293 from=translated src=- shape=8b31a2ae vocab=3c04be13
-/
theorem homeomorph_isOpen_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {s : Set X} : IsOpen (h '' s) ↔ IsOpen s := by
  exact h.isOpen_image

/-- **连续像连通**：连通集的连续像仍连通。 
> **Entry**: topology.space.connected
@isnad1 id=isconnec.2h4v.s5.9778dc410f81 from=translated src=- shape=1df96a34 vocab=6980b5b3
-/
theorem isConnected_image_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsConnected s) {f : X → Y} (hf : ContinuousOn f s) :
    IsConnected (f '' s) := by
  exact hs.image f hf

/-- **闭区间连通**：ℝ 上闭区间 [a,b] 连通。 
> **Entry**: topology.space.connected
@isnad1 id=isconnec.1h2v.s4.b1c0dc31a290 from=translated src=- shape=89ce0792 vocab=dfd19614
-/
theorem topo_isConnected_Icc {a b : ℝ} (h : a ≤ b) : IsConnected (Set.Icc a b) := by
  exact isConnected_Icc h

/-- **开区间连通**：ℝ 上开区间连通。 
> **Entry**: topology.space.connected
@isnad1 id=isprecon.0h2v.s4.c1180564b922 from=translated src=- shape=dc04ab9d vocab=f83ead72
-/
theorem topo_isPreconnected_Ioo {a b : ℝ} : IsPreconnected (Set.Ioo a b) := by
  exact isPreconnected_Ioo

/-- **同胚保持连通**：同胚像连通 ⟺ 原像连通。 
> **Entry**: topology.space.connected
@isnad1 id=iff.0h4v.s5.50c14fb2c944 from=translated src=- shape=f09ec903 vocab=c32f5b1d
-/
theorem homeomorph_isConnected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (h : X ≃ₜ Y) : IsConnected (h '' s) ↔ IsConnected s := by
  exact h.isConnected_image

/-- **子空间嵌入连续**：子空间到原空间的包含映射连续。 
> **Entry**: topology.space.subspace
@isnad1 id=continuo.0h2v.s5.c39b40399e36 from=translated src=- shape=ed0620de vocab=e902aca1
-/
theorem topo_continuous_subtype_val {X : Type*} [TopologicalSpace X] {p : X → Prop} :
    Continuous (Subtype.val : {x : X // p x} → X) := by
  exact continuous_subtype_val

/-- **子空间限制连续**：f 连续 ⟹ 限制到子空间仍连续。 
> **Entry**: topology.space.subspace
@isnad1 id=continuo.1h4v.s5.d841125ef786 from=translated src=- shape=f9e88ebb vocab=e00f3041
-/
theorem topo_continuous_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (s : Set X) : Continuous (s.domRestrict f) := by
  exact ContinuousOn.domRestrict (Continuous.continuousOn hf)

/-- **连续函数的投影分量连续**：f : X → Y×Z 连续 ⟹ 各分量连续。 
> **Entry**: topology.space.subspace
@isnad1 id=continuo.0h2v.s4.8a9f738c5fe6 from=translated src=- shape=8c105144 vocab=5f876d3c
-/
theorem topo_continuous_fst {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    Continuous (Prod.fst : X × Y → X) := by
  exact continuous_fst

/-- **积空间投影连续**：积空间到各因子的投影连续。 
> **Entry**: topology.space.subspace
@isnad1 id=continuo.0h2v.s4.82b1968fa146 from=translated src=- shape=575b335c vocab=50889723
-/
theorem topo_continuous_snd {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    Continuous (Prod.snd : X × Y → Y) := by
  exact continuous_snd

/-- **子空间开集刻画（诱导拓扑）**：U 在子空间 s 中开 ⟺ 存在 X 中开集 V 使 U = V ∩ s。 
> **Entry**: topology.space.subspace
@isnad1 id=iff.0h3v.s6.80e3f98496ac from=translated src=- shape=bb02d94e vocab=00ffd1ef
-/
theorem topo_isOpen_subtype_iff {X : Type*} [TopologicalSpace X] {s : Set X} (U : Set s) :
    IsOpen U ↔ ∃ V : Set X, IsOpen V ∧ Subtype.val ⁻¹' V = U := by
  exact isOpen_induced_iff (f := Subtype.val)

end Topology.Space

end SandronesLibrary
