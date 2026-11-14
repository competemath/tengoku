/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Topology.Continuous
import Tengoku.Seed.Topology.Homeomorph.Defs
import Tengoku.Seed.Topology.Neighborhoods

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mathlib 基础拓扑接口的教材含义

Mathlib 的 `TopologicalSpace`、`IsOpen`、`Continuous` 与 `Homeomorph` 和本课程采用的教材定义
语义一致，因此直接作为本条目的正式公开承载。文件开头的定理逐项展开它们的教材含义，而不再
包装一套平行结构。

下方旧 `TextbookTopology` 层级仅作为既有 SandronesLibrary 声明的冻结兼容层保留。新的拓扑学
开发必须直接使用 Mathlib 承载。

当前条目：

* `topology.foundation.structure`.
-/

open Set Function
open scoped Topology

namespace SandronesLibrary.Topology

variable {X Y : Type*}

/-- Mathlib 的拓扑结构恰好给出教材中的开集公理：全集是开集，两个开集之交仍开，任意族开集之并
仍开。空集则可看作空集合族的并。

> **Entry**: topology.foundation.structure-/
theorem topologicalSpace_open_axioms [TopologicalSpace X] :
    IsOpen (Set.univ : Set X) ∧
      (∀ s t : Set X, IsOpen s → IsOpen t → IsOpen (s ∩ t)) ∧
      ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → IsOpen (⋃₀ S) := by
  exact ⟨isOpen_univ, fun _ _ hs ht ↦ hs.inter ht,
    fun _ hS ↦ isOpen_sUnion hS⟩

/-- 函数连续，当且仅当每个开集的原像仍是开集。这条定理公开展示 Mathlib 的 `Continuous`
谓词所采用的教材定义。-/
theorem continuous_iff_preimage_open [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    _root_.Continuous f ↔ ∀ u : Set Y, _root_.IsOpen u → _root_.IsOpen (f ⁻¹' u) := by
  exact _root_.continuous_def

/-- 等价地，函数连续当且仅当每个闭集的原像仍闭。证明通过取补集从开集原像刻画推出。-/
theorem continuous_iff_preimage_closed [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    _root_.Continuous f ↔
      ∀ s : Set Y, _root_.IsClosed s → _root_.IsClosed (f ⁻¹' s) := by
  constructor
  · intro hf s hs
    exact hs.preimage hf
  · intro h
    rw [continuous_iff_preimage_open]
    intro u hu
    have hclosed : _root_.IsClosed (uᶜ) := hu.isClosed_compl
    have hpre := h (uᶜ) hclosed
    have hopen := hpre.isOpen_compl
    simpa only [preimage_compl, compl_compl] using hopen

/-- 集合是 `x` 的邻域，当且仅当它包含某个含 `x` 的开集。因此，属于 Mathlib 的邻域滤子正是
教材中的邻域概念。-/
theorem mem_nhds_iff_exists_open [TopologicalSpace X] (x : X) (s : Set X) :
    s ∈ 𝓝 x ↔ ∃ u : Set X, _root_.IsOpen u ∧ x ∈ u ∧ u ⊆ s := by
  rw [_root_.mem_nhds_iff]
  constructor
  · rintro ⟨u, hus, hu, hxu⟩
    aesop
  · rintro ⟨u, hu, hxu, hus⟩
    exact ⟨u, hus, hu, hxu⟩

/-- 两空间之间存在同胚，当且仅当存在一个集合等价，且其正向与逆向映射都连续。因此 Mathlib 的
`Homeomorph` 只是把教材中的数据打包起来，没有改变数学含义。-/
theorem nonempty_homeomorph_iff_exists_equiv [TopologicalSpace X] [TopologicalSpace Y] :
    Nonempty (X ≃ₜ Y) ↔
      ∃ e : X ≃ Y, _root_.Continuous (e : X → Y) ∧
        _root_.Continuous (e.symm : Y → X) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toEquiv, e.continuous, e.symm.continuous⟩
  · rintro ⟨e, he, he'⟩
    exact ⟨{ toEquiv := e, continuous_toFun := he, continuous_invFun := he' }⟩

/-- 旧的显式拓扑载体，仅用于保证已经提交的 SandronesLibrary 模块在 M2 迁移期间继续编译。
新声明必须使用 `TopologicalSpace`。-/
structure TextbookTopology (X : Type*) where
  /-- 指定哪些子集是开集的谓词。-/
  IsOpen : Set X → Prop
  /-- 全集是开集。-/
  isOpen_univ : IsOpen univ
  /-- 两个开集的交仍是开集。-/
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- 任意一族开集的并仍是开集。-/
  isOpen_sUnion : ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → IsOpen (⋃₀ S)

namespace TextbookTopology

variable {X Y Z : Type*}

/-- 空集是开集，因为它是空集合族的并。-/
theorem isOpen_empty (τ : TextbookTopology X) : τ.IsOpen ∅ := by
  rw [← sUnion_empty]
  exact τ.isOpen_sUnion ∅ (by simp)

/-- 两个开集的并仍是开集。-/
theorem isOpen_union (τ : TextbookTopology X) {s t : Set X}
    (hs : τ.IsOpen s) (ht : τ.IsOpen t) : τ.IsOpen (s ∪ t) := by
  rw [← sUnion_pair]
  exact τ.isOpen_sUnion {s, t} (by simpa using And.intro hs ht)

/-- 集合的补集为开集时，称该集合为闭集。-/
def IsClosed (τ : TextbookTopology X) (s : Set X) : Prop :=
  τ.IsOpen sᶜ

/-- 空集是闭集。-/
theorem isClosed_empty (τ : TextbookTopology X) : τ.IsClosed ∅ := by
  change τ.IsOpen (∅ : Set X)ᶜ
  simpa using τ.isOpen_univ

/-- 全集是闭集。-/
theorem isClosed_univ (τ : TextbookTopology X) : τ.IsClosed univ := by
  change τ.IsOpen (univ : Set X)ᶜ
  simpa using τ.isOpen_empty

/-- 两个闭集的并仍是闭集。-/
theorem isClosed_union (τ : TextbookTopology X) {s t : Set X}
    (hs : τ.IsClosed s) (ht : τ.IsClosed t) : τ.IsClosed (s ∪ t) := by
  change τ.IsOpen (s ∪ t)ᶜ
  rw [compl_union]
  exact τ.isOpen_inter _ _ hs ht

/-- 两个闭集的交仍是闭集。-/
theorem isClosed_inter (τ : TextbookTopology X) {s t : Set X}
    (hs : τ.IsClosed s) (ht : τ.IsClosed t) : τ.IsClosed (s ∩ t) := by
  change τ.IsOpen (s ∩ t)ᶜ
  rw [compl_inter]
  exact τ.isOpen_union hs ht

/-- 若集合包含某个含 `x` 的开集，则称它为 `x` 的邻域。-/
def IsNeighborhood (τ : TextbookTopology X) (x : X) (s : Set X) : Prop :=
  ∃ u, τ.IsOpen u ∧ x ∈ u ∧ u ⊆ s

/-- 若每个开集的原像仍开，则称映射连续。-/
def Continuous (τX : TextbookTopology X) (τY : TextbookTopology Y) (f : X → Y) : Prop :=
  ∀ v, τY.IsOpen v → τX.IsOpen (f ⁻¹' v)

/-- 连续映射把闭集拉回为闭集。-/
theorem Continuous.isClosed_preimage {τX : TextbookTopology X} {τY : TextbookTopology Y}
    {f : X → Y} (hf : Continuous τX τY f) {s : Set Y} (hs : τY.IsClosed s) :
    τX.IsClosed (f ⁻¹' s) := by
  change τX.IsOpen (f ⁻¹' s)ᶜ
  rw [← preimage_compl]
  exact hf _ hs

/-- 连续性也可以等价地用闭集原像仍闭来检验。-/
theorem continuous_iff_isClosed_preimage {τX : TextbookTopology X}
    {τY : TextbookTopology Y} {f : X → Y} :
    Continuous τX τY f ↔ ∀ s, τY.IsClosed s → τX.IsClosed (f ⁻¹' s) := by
  constructor
  · intro hf s hs
    exact hf.isClosed_preimage hs
  · intro hf s hs
    have hclosed : τY.IsClosed sᶜ := by
      change τY.IsOpen (sᶜ)ᶜ
      simpa using hs
    have hpre := hf sᶜ hclosed
    change τX.IsOpen ((f ⁻¹' sᶜ)ᶜ) at hpre
    simpa only [preimage_compl, compl_compl] using hpre

/-- 恒等映射连续。-/
theorem continuous_id (τ : TextbookTopology X) : Continuous τ τ id := by
  intro v hv
  simpa using hv

/-- 每个常值映射都连续。-/
theorem continuous_const (τX : TextbookTopology X) (τY : TextbookTopology Y) (y : Y) :
    Continuous τX τY (fun _ : X ↦ y) := by
  intro v hv
  by_cases hy : y ∈ v
  · have hpre : (fun _ : X ↦ y) ⁻¹' v = univ := by ext; simp [hy]
    rw [hpre]
    exact τX.isOpen_univ
  · have hpre : (fun _ : X ↦ y) ⁻¹' v = ∅ := by ext; simp [hy]
    rw [hpre]
    exact τX.isOpen_empty

/-- 连续映射的复合仍连续。-/
theorem Continuous.comp {τX : TextbookTopology X} {τY : TextbookTopology Y}
    {τZ : TextbookTopology Z} {f : X → Y} {g : Y → Z}
    (hg : Continuous τY τZ g) (hf : Continuous τX τY f) :
    Continuous τX τZ (g ∘ f) := by
  intro w hw
  change τX.IsOpen (f ⁻¹' (g ⁻¹' w))
  exact hf _ (hg _ hw)

/-- 旧的显式同胚载体；新声明应使用 Mathlib 的 `Homeomorph`。-/
structure Homeomorphism (τX : TextbookTopology X) (τY : TextbookTopology Y) where
  toEquiv : X ≃ Y
  continuous_toFun : Continuous τX τY toEquiv
  continuous_invFun : Continuous τY τX toEquiv.symm

end TextbookTopology

end SandronesLibrary.Topology
