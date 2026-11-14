/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Foundation
import Tengoku.Seed.Topology.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic constructions of textbook topologies

This file constructs induced, subspace, and product topologies from the open-set axioms developed
in `Topology.Foundation`.

Current entry:

* `topology.foundation.constructions`.
-/

open Set Function

namespace SandronesLibrary.Topology

variable {X Y Z : Type*}

/-- Mathlib 的诱导拓扑恰好把目标空间的开集沿映射拉回；这就是教材中由映射诱导拓扑的定义。

> **Entry**: topology.foundation.constructions
@isnad1 id=iff.0h5v.s5.9c71521c6b0c from=translated src=- shape=f1fe6e75 vocab=2e642c59
-/
theorem isOpen_induced_iff_exists (f : X → Y) (τY : TopologicalSpace Y) (s : Set X) :
    @_root_.IsOpen X (TopologicalSpace.induced f τY) s ↔
      ∃ v : Set Y, @_root_.IsOpen Y τY v ∧ f ⁻¹' v = s := by
  exact @isOpen_induced_iff X Y τY s f

/-- 映射到子空间连续，当且仅当忘掉值域的成员证明后，映射到环境空间连续。这同时说明 subtype
上的 Mathlib 拓扑就是包含映射诱导的教材子空间拓扑。
@isnad1 id=iff.0h4v.s5.e8228d011dba from=translated src=- shape=76d0272c vocab=84e34fda
-/
theorem continuous_subtype_iff [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (f : Y → s) :
    _root_.Continuous f ↔ _root_.Continuous (fun y ↦ (f y : X)) := by
  exact Topology.IsInducing.subtypeVal.continuous_iff

/-- 积空间中的集合开，当且仅当其中每一点都包含在某个仍位于该集合内的开矩形中。这是教材的
积拓扑局部基刻画。
@isnad1 id=iff.0h3v.s6.211899ad0a2d from=translated src=- shape=117bfbb7 vocab=88179e04
-/
theorem isOpen_prod_iff_rectangles [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set (X × Y)) :
    _root_.IsOpen s ↔ ∀ x y, (x, y) ∈ s →
      ∃ u : Set X, ∃ v : Set Y,
        _root_.IsOpen u ∧ _root_.IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ×ˢ v ⊆ s := by
  exact _root_.isOpen_prod_iff

/-- 到积空间的映射连续，当且仅当两个坐标映射都连续；正向由连续投影复合得到，反向由
Mathlib 的 `Continuous.prodMk` 组装。
@isnad1 id=iff.0h5v.s5.51e017f4cbfb from=translated src=- shape=20132665 vocab=94af3156
-/
theorem continuous_prod_mk_iff [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : Z → X) (g : Z → Y) :
    _root_.Continuous (fun z ↦ (f z, g z)) ↔
      _root_.Continuous f ∧ _root_.Continuous g := by
  constructor
  · intro h
    exact ⟨_root_.continuous_fst.comp h, _root_.continuous_snd.comp h⟩
  · rintro ⟨hf, hg⟩
    exact hf.prodMk hg

end SandronesLibrary.Topology

namespace SandronesLibrary.Topology.TextbookTopology

variable {X Y Z : Type*}

/-- The topology induced on `X` by a map `f : X → Y`: its open sets are exactly preimages of open
sets of `Y`.

> **Entry**: topology.foundation.constructions-/
def induced (f : X → Y) (τY : TextbookTopology Y) : TextbookTopology X where
  IsOpen s := ∃ v, τY.IsOpen v ∧ f ⁻¹' v = s
  isOpen_univ := ⟨univ, τY.isOpen_univ, preimage_univ⟩
  isOpen_inter s t hs ht := by
    obtain ⟨u, hu, rfl⟩ := hs
    obtain ⟨v, hv, rfl⟩ := ht
    exact ⟨u ∩ v, τY.isOpen_inter u v hu hv, preimage_inter⟩
  isOpen_sUnion S hS := by
    classical
    let V : Set (Set Y) := {v | τY.IsOpen v ∧ f ⁻¹' v ∈ S}
    refine ⟨⋃₀ V, τY.isOpen_sUnion V (fun v hv ↦ hv.1), ?_⟩
    ext x
    simp only [mem_preimage, mem_sUnion]
    constructor
    · rintro ⟨v, ⟨hvopen, hvS⟩, hxv⟩
      exact ⟨f ⁻¹' v, hvS, hxv⟩
    · rintro ⟨s, hsS, hxs⟩
      obtain ⟨v, hvopen, rfl⟩ := hS s hsS
      exact ⟨v, ⟨hvopen, hsS⟩, hxs⟩

/-- The subspace topology is induced by the inclusion map.-/
def subspace (s : Set X) (τX : TextbookTopology X) : TextbookTopology s :=
  induced Subtype.val τX

/-- Open sets in a subspace are precisely preimages of ambient open sets.
@isnad1 id=iff.0h4v.s6.53b4e407bd42 from=translated src=- shape=686abaee vocab=bbc15486
-/
theorem isOpen_subspace_iff (s : Set X) (τX : TextbookTopology X) (u : Set s) :
    (subspace s τX).IsOpen u ↔ ∃ v, τX.IsOpen v ∧ Subtype.val ⁻¹' v = u :=
  Iff.rfl

/-- The inclusion of a subspace into its ambient space is continuous.
@isnad1 id=continuo.0h3v.s4.a689a903684f from=translated src=- shape=48155e44 vocab=1bf55576
-/
theorem continuous_subtype_val (s : Set X) (τX : TextbookTopology X) :
    Continuous (subspace s τX) τX (Subtype.val : s → X) := by
  intro v hv
  exact ⟨v, hv, rfl⟩

/-- A continuous map whose values lie in a subset is continuous as a map into the corresponding
subspace.
@isnad1 id=continuo.2h6v.s6.7ba1e0b1f2eb from=translated src=- shape=50a91859 vocab=b3764cf4
-/
theorem continuous_subtype_mk {τY : TextbookTopology Y} {τX : TextbookTopology X}
    {s : Set X} {f : Y → X} (hf : Continuous τY τX f) (hs : ∀ y, f y ∈ s) :
    Continuous τY (subspace s τX) (fun y ↦ ⟨f y, hs y⟩) := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact hf v hv

/-- The product topology: every point of an open set lies in an open rectangle contained in it.

> **Entry**: topology.foundation.constructions-/
def product (τX : TextbookTopology X) (τY : TextbookTopology Y) :
    TextbookTopology (X × Y) where
  IsOpen w := ∀ p ∈ w, ∃ u v, τX.IsOpen u ∧ τY.IsOpen v ∧ p ∈ u ×ˢ v ∧ u ×ˢ v ⊆ w
  isOpen_univ := by
    intro p hp
    exact ⟨univ, univ, τX.isOpen_univ, τY.isOpen_univ, by simp, by simp⟩
  isOpen_inter s t hs ht := by
    intro p hp
    obtain ⟨u₁, v₁, hu₁, hv₁, hp₁, hsub₁⟩ := hs p hp.1
    obtain ⟨u₂, v₂, hu₂, hv₂, hp₂, hsub₂⟩ := ht p hp.2
    refine ⟨u₁ ∩ u₂, v₁ ∩ v₂, τX.isOpen_inter _ _ hu₁ hu₂,
      τY.isOpen_inter _ _ hv₁ hv₂, ?_, ?_⟩
    · exact ⟨⟨hp₁.1, hp₂.1⟩, ⟨hp₁.2, hp₂.2⟩⟩
    · intro q hq
      exact ⟨hsub₁ ⟨hq.1.1, hq.2.1⟩, hsub₂ ⟨hq.1.2, hq.2.2⟩⟩
  isOpen_sUnion S hS := by
    intro p hp
    obtain ⟨w, hwS, hpw⟩ := hp
    obtain ⟨u, v, hu, hv, hp', hsub⟩ := hS w hwS p hpw
    exact ⟨u, v, hu, hv, hp', fun q hq ↦ ⟨w, hwS, hsub hq⟩⟩

/-- An open rectangle is open in the product topology.
@isnad1 id=isopen.2h6v.s5.3bc1455394db from=translated src=- shape=a5d2e8ee vocab=551b0f8f
-/
theorem isOpen_prod {τX : TextbookTopology X} {τY : TextbookTopology Y}
    {u : Set X} {v : Set Y} (hu : τX.IsOpen u) (hv : τY.IsOpen v) :
    (product τX τY).IsOpen (u ×ˢ v) := by
  intro p hp
  exact ⟨u, v, hu, hv, hp, Subset.rfl⟩

/-- The first projection from a product is continuous.
@isnad1 id=continuo.0h4v.s4.dacf99221d24 from=translated src=- shape=e4b1908d vocab=a9a5bbf8
-/
theorem continuous_fst (τX : TextbookTopology X) (τY : TextbookTopology Y) :
    Continuous (product τX τY) τX Prod.fst := by
  intro u hu
  have hpre : Prod.fst ⁻¹' u = u ×ˢ (univ : Set Y) := by ext; simp
  rw [hpre]
  exact isOpen_prod hu τY.isOpen_univ

/-- The second projection from a product is continuous.
@isnad1 id=continuo.0h4v.s4.6f65b9056f0e from=translated src=- shape=d61ebf0a vocab=295bfdf6
-/
theorem continuous_snd (τX : TextbookTopology X) (τY : TextbookTopology Y) :
    Continuous (product τX τY) τY Prod.snd := by
  intro v hv
  have hpre : Prod.snd ⁻¹' v = (univ : Set X) ×ˢ v := by ext; simp
  rw [hpre]
  exact isOpen_prod τX.isOpen_univ hv

/-- A map into a product is continuous when both of its coordinate maps are continuous.
@isnad1 id=continuo.2h8v.s5.2a6f19e64b52 from=translated src=- shape=ba0b5daa vocab=4977c89f
-/
theorem continuous_prod_mk {W : Type*} {τW : TextbookTopology W}
    {τX : TextbookTopology X} {τY : TextbookTopology Y} {f : W → X} {g : W → Y}
    (hf : Continuous τW τX f) (hg : Continuous τW τY g) :
    Continuous τW (product τX τY) (fun w ↦ (f w, g w)) := by
  intro s hs
  let S : Set (Set W) := {u | τW.IsOpen u ∧ u ⊆ (fun w ↦ (f w, g w)) ⁻¹' s}
  have hopen : τW.IsOpen (⋃₀ S) :=
    τW.isOpen_sUnion S (fun u hu ↦ hu.1)
  have heq : (⋃₀ S) = (fun w ↦ (f w, g w)) ⁻¹' s := by
    ext w
    constructor
    · rintro ⟨u, hu, hwu⟩
      exact hu.2 hwu
    · intro hw
      obtain ⟨u, v, hu, hv, hwuv, huv⟩ := hs (f w, g w) hw
      let q := f ⁻¹' u ∩ g ⁻¹' v
      have hqopen : τW.IsOpen q := τW.isOpen_inter _ _ (hf u hu) (hg v hv)
      have hqsub : q ⊆ (fun z ↦ (f z, g z)) ⁻¹' s := by
        intro z hz
        exact huv hz
      exact ⟨q, ⟨hqopen, hqsub⟩, hwuv⟩
  rw [← heq]
  exact hopen

end SandronesLibrary.Topology.TextbookTopology
