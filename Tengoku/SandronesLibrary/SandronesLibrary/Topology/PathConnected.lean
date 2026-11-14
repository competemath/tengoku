/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Path
import Tengoku.Seed.Topology.Connected.PathConnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Path connectedness

The relation of being joined by a path, path components, and path connected subsets are built
from Sandrone paths and Sandrone subspace topologies.

Current entry:

* `topology.connectedness.path-components-foundation`.
-/

open Set

namespace SandronesLibrary.Topology

variable {X Y : Type*}

/-- Mathlib 的 `Joined x y` 按定义就是存在一条从 `x` 到 `y` 的道路。

> **Entry**: topology.connectedness.path-components-foundation
@isnad1 id=iff.0h3v.s4.f9f450c162ae from=translated src=- shape=3002910a vocab=5be37d80
-/
theorem joined_iff_nonempty_path [TopologicalSpace X] (x y : X) :
    _root_.Joined x y ↔ Nonempty (_root_.Path x y) :=
  Iff.rfl

/-- 子集道路连通，当且仅当它非空，且任意两个属于该集合的点都能由一条始终留在集合内的道路
连接。`JoinedIn` 显式记录“道路不离开子集”，避免与环境空间中的可连接性混淆。
@isnad1 id=iff.0h2v.s5.31ac4405f108 from=translated src=- shape=3bc8ad0a vocab=336bd3d2
-/
theorem isPathConnected_iff_nonempty_joinedIn [TopologicalSpace X] (s : Set X) :
    _root_.IsPathConnected s ↔ s.Nonempty ∧
      ∀ x ∈ s, ∀ y ∈ s, _root_.JoinedIn s x y := by
  exact _root_.isPathConnected_iff

/-- 连续映射保持道路连通性；像集中的连接道路由原集合中的道路经 `Path.map` 得到。
@isnad1 id=ispathco.2h4v.s5.1d4ce46f983f from=translated src=- shape=8ccdb3e2 vocab=bf553e6e
-/
theorem isPathConnected_image [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : _root_.IsPathConnected s) {f : X → Y}
    (hf : _root_.Continuous f) : _root_.IsPathConnected (f '' s) :=
  hs.image hf

end SandronesLibrary.Topology

namespace SandronesLibrary.Topology.TextbookTopology

variable {X : Type*} (tau : TextbookTopology X)

/-- Two points are joined when a Sandrone path connects them.

> **Entry**: topology.connectedness.path-components-foundation-/
def Joined (a b : X) : Prop := Nonempty (Path tau a b)

/-- Every point is joined to itself by the constant path.
@isnad1 id=joined.0h3v.s3.0868b7ee1013 from=translated src=- shape=e99b0604 vocab=a19237e6
-/
theorem joined_refl (a : X) : Joined tau a a :=
  Nonempty.intro (Path.refl tau a)

/-- Reversing a path reverses the joined relation.
@isnad1 id=joined.1h4v.s4.a12075d1bf47 from=translated src=- shape=ecc8ce2b vocab=a19237e6
-/
theorem Joined.symm {a b : X} (h : Joined tau a b) : Joined tau b a := by
  obtain ⟨gamma⟩ := h
  exact ⟨gamma.symm⟩

/-- Concatenating paths makes the joined relation transitive.
@isnad1 id=joined.2h5v.s4.6caed1b0f8cc from=translated src=- shape=3608e606 vocab=a19237e6
-/
theorem Joined.trans {a b c : X} (hab : Joined tau a b) (hbc : Joined tau b c) :
    Joined tau a c := by
  obtain ⟨gamma⟩ := hab
  obtain ⟨delta⟩ := hbc
  exact ⟨gamma.trans delta⟩

/-- Being joined by a path is an equivalence relation.
@isnad1 id=equivale.0h2v.s3.47017e51ff70 from=translated src=- shape=16be0546 vocab=30ffff32
-/
theorem joined_equivalence : Equivalence (Joined tau) :=
  ⟨joined_refl tau, fun {_ _} h ↦ Joined.symm tau h,
    fun {_ _ _} h k ↦ Joined.trans tau h k⟩

/-- The path component of `a` is its equivalence class under the joined relation.-/
def pathComponent (a : X) : Set X := {b | Joined tau a b}

/--
@isnad1 id=iff.0h4v.s4.ee1f9c039975 from=translated src=- shape=86464f5d vocab=ca4d3494
-/
theorem mem_pathComponent_iff (a b : X) : b ∈ pathComponent tau a ↔ Joined tau a b :=
  Iff.rfl

/-- A subset is path connected when it is nonempty and any two of its points can be joined by a
path in its Sandrone subspace topology.-/
def IsPathConnected (s : Set X) : Prop :=
  s.Nonempty ∧ ∀ a b : s, Joined (subspace s tau) a b

/-- Every singleton is path connected in its subspace topology.
@isnad1 id=ispathco.0h3v.s4.4975ea509c0b from=translated src=- shape=b3bec09e vocab=96180b39
-/
theorem isPathConnected_singleton (a : X) : IsPathConnected tau {a} := by
  refine ⟨⟨a, by simp⟩, ?_⟩
  intro x y
  have hxy : x = y := by
    apply Subtype.ext
    exact x.2.trans y.2.symm
  subst y
  exact joined_refl (subspace {a} tau) x

/-- A continuous map sends joined points to joined points.
@isnad1 id=joined.2h7v.s5.b2bfcb3aae12 from=translated src=- shape=6cf43f42 vocab=3f706d85
-/
theorem Joined.map {Y : Type*} {τX : TextbookTopology X} {τY : TextbookTopology Y}
    {a b : X} {f : X → Y} (h : Joined τX a b) (hf : Continuous τX τY f) :
    Joined τY (f a) (f b) := by
  obtain ⟨gamma⟩ := h
  exact ⟨gamma.map f hf⟩

/-- The image of a path connected set under a continuous map is path connected in its subspace
topology.
@isnad1 id=ispathco.2h6v.s5.d61763f04324 from=translated src=- shape=432445e5 vocab=cf9e8df4
-/
theorem IsPathConnected.image {Y : Type*} {τX : TextbookTopology X}
    {τY : TextbookTopology Y} {s : Set X} {f : X → Y} (hs : IsPathConnected τX s)
    (hf : Continuous τX τY f) : IsPathConnected τY (f '' s) := by
  obtain ⟨x, hx⟩ := hs.1
  refine ⟨⟨f x, x, hx, rfl⟩, ?_⟩
  rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
  let lift : s → f '' s := fun z ↦ ⟨f z, z, z.2, rfl⟩
  have hlift : Continuous (subspace s τX) (subspace (f '' s) τY) lift := by
    apply continuous_subtype_mk
    exact hf.comp (continuous_subtype_val s τX)
  exact Joined.map (hs.2 ⟨x, hx⟩ ⟨y, hy⟩) hlift

/-- The base point belongs to its own path component.
@isnad1 id=mem.0h3v.s4.54dc674a1ddd from=translated src=- shape=57626d8f vocab=57ea9b45
-/
theorem self_mem_pathComponent (a : X) : a ∈ pathComponent tau a :=
  joined_refl tau a

/-- Joined points determine the same path component.
@isnad1 id=eq.1h4v.s4.265cfe46e15b from=translated src=- shape=e4118a6e vocab=3612d2ba
-/
theorem pathComponent_eq_of_joined {a b : X} (h : Joined tau a b) :
    pathComponent tau a = pathComponent tau b := by
  ext x
  constructor
  · intro hax
    exact Joined.trans tau (Joined.symm tau h) hax
  · intro hbx
    exact Joined.trans tau h hbx

/-- Two path components are equal exactly when their base points are joined.
@isnad1 id=iff.0h4v.s4.08a34800a6fb from=translated src=- shape=5702177f vocab=3612d2ba
-/
theorem pathComponent_eq_iff_joined (a b : X) :
    pathComponent tau a = pathComponent tau b ↔ Joined tau a b := by
  constructor
  · intro h
    change b ∈ pathComponent tau a
    rw [h]
    exact self_mem_pathComponent tau b
  · exact pathComponent_eq_of_joined tau

/-- Path components which meet are equal.
@isnad1 id=eq.1h4v.s5.625453f77ed5 from=translated src=- shape=8eb0f375 vocab=26c45882
-/
theorem pathComponent_eq_of_mem_inter {a b : X}
    (h : (pathComponent tau a ∩ pathComponent tau b).Nonempty) :
    pathComponent tau a = pathComponent tau b := by
  obtain ⟨x, hax, hbx⟩ := h
  apply pathComponent_eq_of_joined tau
  exact Joined.trans tau hax (Joined.symm tau hbx)

/-- A continuous map sends a path component into the path component of the image point.
@isnad1 id=le.1h6v.s5.a19147ab4ba3 from=translated src=- shape=dff8e5c5 vocab=35fef122
-/
theorem image_pathComponent_subset {Y : Type*} {τY : TextbookTopology Y} {f : X → Y}
    (hf : Continuous tau τY f) (a : X) :
    f '' pathComponent tau a ⊆ pathComponent τY (f a) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Joined.map hx hf

end SandronesLibrary.Topology.TextbookTopology
