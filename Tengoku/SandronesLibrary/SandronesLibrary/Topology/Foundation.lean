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

> **Entry**: topology.foundation.structure
@isnad1 id=and.0h1v.s6.1a2ea24d112f from=translated src=- shape=52161c1a vocab=75e8fe9b
-/
theorem topologicalSpace_open_axioms [TopologicalSpace X] :
    IsOpen (Set.univ : Set X) ∧
      (∀ s t : Set X, IsOpen s → IsOpen t → IsOpen (s ∩ t)) ∧
      ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → IsOpen (⋃₀ S) := by
  exact ⟨isOpen_univ, fun _ _ hs ht ↦ hs.inter ht,
    fun _ hS ↦ isOpen_sUnion hS⟩

/-- 函数连续，当且仅当每个开集的原像仍是开集。这条定理公开展示 Mathlib 的 `Continuous`
谓词所采用的教材定义。
@isnad1 id=iff.0h3v.s5.67e196f074bf from=translated src=- shape=90a889fa vocab=b2283c1d
-/
theorem continuous_iff_preimage_open [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    _root_.Continuous f ↔ ∀ u : Set Y, _root_.IsOpen u → _root_.IsOpen (f ⁻¹' u) := by
  exact _root_.continuous_def

/-- 等价地，函数连续当且仅当每个闭集的原像仍闭。证明通过取补集从开集原像刻画推出。
@isnad1 id=iff.0h3v.s5.b73d8025156f from=translated src=- shape=90a889fa vocab=461939aa
-/
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
教材中的邻域概念。
@isnad1 id=iff.0h3v.s5.7d9ca1bcb5e6 from=translated src=- shape=8d0bf6e3 vocab=2bc3408b
-/
theorem mem_nhds_iff_exists_open [TopologicalSpace X] (x : X) (s : Set X) :
    s ∈ 𝓝 x ↔ ∃ u : Set X, _root_.IsOpen u ∧ x ∈ u ∧ u ⊆ s := by
  rw [_root_.mem_nhds_iff]
  constructor
  · rintro ⟨u, hus, hu, hxu⟩
    aesop
  · rintro ⟨u, hu, hxu, hus⟩
    exact ⟨u, hus, hu, hxu⟩

/-- 两空间之间存在同胚，当且仅当存在一个集合等价，且其正向与逆向映射都连续。因此 Mathlib 的
`Homeomorph` 只是把教材中的数据打包起来，没有改变数学含义。
@isnad1 id=iff.0h2v.s6.98bbf16f7160 from=translated src=- shape=60ecdd51 vocab=a52b4b7b
-/
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

/-- 空集是开集，因为它是空集合族的并。
@isnad1 id=isopen.0h2v.s3.93b54ac43308 from=translated src=- shape=59c48716 vocab=cc72eae8
-/
theorem isOpen_empty (τ : TextbookTopology X) : τ.IsOpen ∅ := by
  rw [← sUnion_empty]
  exact τ.isOpen_sUnion ∅ (by simp)

/-- 两个开集的并仍是开集。
@isnad1 id=isopen.2h4v.s4.b0b4688ff377 from=translated src=- shape=80e5bfc8 vocab=7a9b946f
-/
theorem isOpen_union (τ : TextbookTopology X) {s t : Set X}
    (hs : τ.IsOpen s) (ht : τ.IsOpen t) : τ.IsOpen (s ∪ t) := by
  rw [← sUnion_pair]
  exact τ.isOpen_sUnion {s, t} (by simpa using And.intro hs ht)

/-- 集合的补集为开集时，称该集合为闭集。-/
def IsClosed (τ : TextbookTopology X) (s : Set X) : Prop :=
  τ.IsOpen sᶜ

/-- 空集是闭集。
@isnad1 id=isclosed.0h2v.s3.a27f17931045 from=translated src=- shape=59c48716 vocab=d04bafe8
-/
theorem isClosed_empty (τ : TextbookTopology X) : τ.IsClosed ∅ := by
  change τ.IsOpen (∅ : Set X)ᶜ
  simpa using τ.isOpen_univ

/-- 全集是闭集。
@isnad1 id=isclosed.0h2v.s3.5f199a0194cc from=translated src=- shape=c82d8647 vocab=fa9cfc77
-/
theorem isClosed_univ (τ : TextbookTopology X) : τ.IsClosed univ := by
  change τ.IsOpen (univ : Set X)ᶜ
  simpa using τ.isOpen_empty

/-- 两个闭集的并仍是闭集。
@isnad1 id=isclosed.2h4v.s4.afdf504ae08c from=translated src=- shape=80e5bfc8 vocab=55b0de2d
-/
theorem isClosed_union (τ : TextbookTopology X) {s t : Set X}
    (hs : τ.IsClosed s) (ht : τ.IsClosed t) : τ.IsClosed (s ∪ t) := by
  change τ.IsOpen (s ∪ t)ᶜ
  rw [compl_union]
  exact τ.isOpen_inter _ _ hs ht

/-- 两个闭集的交仍是闭集。
@isnad1 id=isclosed.2h4v.s4.208c89bdc0e6 from=translated src=- shape=80e5bfc8 vocab=cafccb25
-/
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

/-- 连续映射把闭集拉回为闭集。
@isnad1 id=isclosed.2h6v.s5.d4ffc355606b from=translated src=- shape=7bdcef22 vocab=8728d819
-/
theorem Continuous.isClosed_preimage {τX : TextbookTopology X} {τY : TextbookTopology Y}
    {f : X → Y} (hf : Continuous τX τY f) {s : Set Y} (hs : τY.IsClosed s) :
    τX.IsClosed (f ⁻¹' s) := by
  change τX.IsOpen (f ⁻¹' s)ᶜ
  rw [← preimage_compl]
  exact hf _ hs

/-- 连续性也可以等价地用闭集原像仍闭来检验。
@isnad1 id=iff.0h5v.s5.01929f7b71a7 from=translated src=- shape=4fbd55a8 vocab=8728d819
-/
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

/-- 恒等映射连续。
@isnad1 id=continuo.0h2v.s3.6ec26b9ab901 from=translated src=- shape=d2645466 vocab=d3aac8a5
-/
theorem continuous_id (τ : TextbookTopology X) : Continuous τ τ id := by
  intro v hv
  simpa using hv

/-- 每个常值映射都连续。
@isnad1 id=continuo.0h5v.s4.aa703e6eff83 from=translated src=- shape=ffc0a18d vocab=c120a97c
-/
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

/-- 连续映射的复合仍连续。
@isnad1 id=continuo.2h8v.s5.4fae5c93c5fd from=translated src=- shape=b730ce08 vocab=db7e08a9
-/
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
