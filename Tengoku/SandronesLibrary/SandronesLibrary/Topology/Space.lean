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

/-- **开集公理：空集开**。-/
theorem topo_isOpen_empty {X : Type*} [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  exact isOpen_empty

/-- **开集公理：全集开**。-/
theorem topo_isOpen_univ {X : Type*} [TopologicalSpace X] : IsOpen (Set.univ : Set X) := by
  exact isOpen_univ

/-- **开集公理：有限交开**：两个开集的交仍开（可归纳到有限个）。 
> **Entry**: topology.space.def-/
theorem topo_isOpen_inter {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  exact IsOpen.inter hs ht

/-- **开集公理：任意并开**：一族开集的并仍开。 
> **Entry**: topology.space.def-/
theorem topo_isOpen_iUnion {X : Type*} {ι : Type*} [TopologicalSpace X]
    {f : ι → Set X} (h : ∀ i : ι, IsOpen (f i)) : IsOpen (⋃ i, f i) := by
  exact isOpen_iUnion h

/-- **闭集公理：任意交闭**：一族闭集的交仍闭。 
> **Entry**: topology.space.def-/
theorem topo_isClosed_iInter {X : Type*} {ι : Type*} [TopologicalSpace X]
    {f : ι → Set X} (h : ∀ i : ι, IsClosed (f i)) : IsClosed (⋂ i, f i) := by
  exact isClosed_iInter h

/-- **闭集公理：有限并闭**：两个闭集的并仍闭。 
> **Entry**: topology.space.def-/
theorem topo_isClosed_union {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t) := by
  exact IsClosed.union hs ht

/-- **开 ⟺ 补闭**：s 开 ⟺ s 的补集闭。 
> **Entry**: topology.space.def-/
theorem topo_isOpen_iff_isClosed_compl {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsOpen s ↔ IsClosed sᶜ := by
  exact isClosed_compl_iff.symm

/-- **连续 ⟺ 开集原像开**（教材定义）：f 连续 ⟺ 每个开集的原像是开集。 
> **Entry**: topology.space.continuous-/
theorem topo_continuous_iff_isOpen_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ s : Set Y, IsOpen s → IsOpen (f ⁻¹' s) := by
  exact continuous_def

/-- **连续函数开集原像开**：f 连续 ⟹ 开集的原像是开集。 
> **Entry**: topology.space.continuous-/
theorem topo_continuous_isOpen_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsOpen s) : IsOpen (f ⁻¹' s) := by
  exact Continuous.isOpen_preimage hf s hs

/-- **连续 ⟺ 处处点连续**：f 连续 ⟺ 在每个点都连续。 
> **Entry**: topology.space.continuous-/
theorem topo_continuous_iff_continuousAt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} : Continuous f ↔ ∀ x : X, ContinuousAt f x := by
  exact continuous_iff_continuousAt

/-- **恒等映射连续**。 
> **Entry**: topology.space.continuous-/
theorem topo_continuous_id {X : Type*} [TopologicalSpace X] : Continuous (id : X → X) := by
  exact continuous_id

/-- **常函数连续**。 
> **Entry**: topology.space.continuous-/
theorem topo_continuous_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    Continuous (fun _ : X => y) := by
  exact continuous_const

/-- **连续函数的复合连续**。 
> **Entry**: topology.space.continuous-/
theorem topo_continuous_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hg : Continuous g) (hf : Continuous f) : Continuous (g ∘ f) := by
  exact hg.comp hf

/-- **连续 ⟹ 收敛穿过**：f 连续且 xₙ → x，则 f(xₙ) → f(x)（滤子语言）。 
> **Entry**: topology.space.continuous-/
theorem topo_continuous_tendsto {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (x : X) : Filter.Tendsto f (nhds x) (nhds (f x)) := by
  exact hf.tendsto x

/-- **开集是其中每点的邻域**：开集含 x ⟹ x 的邻域。 
> **Entry**: topology.space.neighborhood-/
theorem topo_isOpen_mem_nhds {X : Type*} [TopologicalSpace X] {x : X} {s : Set X}
    (hs : IsOpen s) (hx : x ∈ s) : s ∈ nhds x := by
  exact hs.mem_nhds hx

/-- **同胚的定义性质：双射且双向连续**：同胚 h 是连续双射，其逆也连续。 
> **Entry**: topology.space.homeo-/
theorem homeomorph_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Continuous h := by
  exact h.continuous

/-- **同胚的逆连续**：同胚的逆映射也是同胚（双向连续）。 
> **Entry**: topology.space.homeo-/
theorem homeomorph_invFun_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Continuous h.symm := by
  exact h.symm.continuous

/-- **同胚是双射**。 
> **Entry**: topology.space.homeo-/
theorem homeomorph_bijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Function.Bijective h := by
  exact h.bijective

/-- **同胚保开集**：同胚把开集映成开集（且只把开集映成开集）。 
> **Entry**: topology.space.homeo-/
theorem homeomorph_isOpen_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {s : Set X} : IsOpen (h '' s) ↔ IsOpen s := by
  exact h.isOpen_image

/-- **连续像连通**：连通集的连续像仍连通。 
> **Entry**: topology.space.connected-/
theorem isConnected_image_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsConnected s) {f : X → Y} (hf : ContinuousOn f s) :
    IsConnected (f '' s) := by
  exact hs.image f hf

/-- **闭区间连通**：ℝ 上闭区间 [a,b] 连通。 
> **Entry**: topology.space.connected-/
theorem topo_isConnected_Icc {a b : ℝ} (h : a ≤ b) : IsConnected (Set.Icc a b) := by
  exact isConnected_Icc h

/-- **开区间连通**：ℝ 上开区间连通。 
> **Entry**: topology.space.connected-/
theorem topo_isPreconnected_Ioo {a b : ℝ} : IsPreconnected (Set.Ioo a b) := by
  exact isPreconnected_Ioo

/-- **同胚保持连通**：同胚像连通 ⟺ 原像连通。 
> **Entry**: topology.space.connected-/
theorem homeomorph_isConnected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (h : X ≃ₜ Y) : IsConnected (h '' s) ↔ IsConnected s := by
  exact h.isConnected_image

/-- **子空间嵌入连续**：子空间到原空间的包含映射连续。 
> **Entry**: topology.space.subspace-/
theorem topo_continuous_subtype_val {X : Type*} [TopologicalSpace X] {p : X → Prop} :
    Continuous (Subtype.val : {x : X // p x} → X) := by
  exact continuous_subtype_val

/-- **子空间限制连续**：f 连续 ⟹ 限制到子空间仍连续。 
> **Entry**: topology.space.subspace-/
theorem topo_continuous_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (s : Set X) : Continuous (s.domRestrict f) := by
  exact ContinuousOn.domRestrict (Continuous.continuousOn hf)

/-- **连续函数的投影分量连续**：f : X → Y×Z 连续 ⟹ 各分量连续。 
> **Entry**: topology.space.subspace-/
theorem topo_continuous_fst {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    Continuous (Prod.fst : X × Y → X) := by
  exact continuous_fst

/-- **积空间投影连续**：积空间到各因子的投影连续。 
> **Entry**: topology.space.subspace-/
theorem topo_continuous_snd {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    Continuous (Prod.snd : X × Y → Y) := by
  exact continuous_snd

/-- **子空间开集刻画（诱导拓扑）**：U 在子空间 s 中开 ⟺ 存在 X 中开集 V 使 U = V ∩ s。 
> **Entry**: topology.space.subspace-/
theorem topo_isOpen_subtype_iff {X : Type*} [TopologicalSpace X] {s : Set X} (U : Set s) :
    IsOpen U ↔ ∃ V : Set X, IsOpen V ∧ Subtype.val ⁻¹' V = U := by
  exact isOpen_induced_iff (f := Subtype.val)

end Topology.Space

end SandronesLibrary
