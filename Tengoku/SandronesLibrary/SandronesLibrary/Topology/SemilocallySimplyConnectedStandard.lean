/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringLiftingCriterionStandard
import Tengoku.Seed.Topology.Homotopy.LocallyContractible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 半局部单连通空间

本模块冻结覆盖空间分类所需的半局部单连通定义：每一点都具有一个开邻域，使该邻域 inclusion 诱导的
基本群同态之像为底群。点态性质是唯一主定义，全局性质是逐点取得该证书的 Prop-valued class。

当前条目：

* `topology.covering.semilocally-simply-connected-standard`。

小邻域中所有基环路在全空间里平凡只作为等价展开，不建立第二个 predicate。两个强假设桥是普通
theorem，不注册全局 instance。本文件不构造道路类商、覆盖图或 universal cover。
-/

open Topology Filter

namespace SandronesLibrary.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- `X` 在 `x` 半局部单连通：某个含 `x` 的开邻域 inclusion 在基本群上的像为底群。

> **Entry**: topology.covering.semilocally-simply-connected-standard-/
def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ (U : Set X) (_hU : IsOpen U) (hx : x ∈ U),
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩).range = ⊥

/-- 每一点都半局部单连通的空间。-/
class SemilocallySimplyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop where
  semilocallySimplyConnectedAt : ∀ x : X, SemilocallySimplyConnectedAt x

/-- 点态主定义等价于：某个开邻域中的每个基环路映入全空间后都为平凡类。-/
theorem semilocallySimplyConnectedAt_iff_exists_open_loops (x : X) :
    SemilocallySimplyConnectedAt x ↔
      ∃ (U : Set X) (_hU : IsOpen U) (hx : x ∈ U),
        ∀ q : FundamentalGroup U ⟨x, hx⟩,
          FundamentalGroup.map
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩ q = 1 := by
  constructor
  · rintro ⟨U, hU, hx, hrange⟩
    refine ⟨U, hU, hx, fun q => ?_⟩
    have hmem : FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩ q ∈
        (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩).range :=
      ⟨q, rfl⟩
    rw [hrange] at hmem
    simpa using hmem
  · rintro ⟨U, hU, hx, hloops⟩
    refine ⟨U, hU, hx, le_antisymm ?_ bot_le⟩
    rintro g ⟨q, rfl⟩
    simp [hloops q]

/-- 全局 class 等价于逐点取得开邻域，并使其中所有基环路映入全空间后平凡。-/
theorem semilocallySimplyConnectedSpace_iff_forall_exists_open_loops :
    SemilocallySimplyConnectedSpace X ↔
      ∀ x : X, ∃ (U : Set X) (_hU : IsOpen U) (hx : x ∈ U),
        ∀ q : FundamentalGroup U ⟨x, hx⟩,
          FundamentalGroup.map
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩ q = 1 := by
  constructor
  · intro h x
    exact (semilocallySimplyConnectedAt_iff_exists_open_loops x).mp
      (h.semilocallySimplyConnectedAt x)
  · intro h
    exact ⟨fun x => (semilocallySimplyConnectedAt_iff_exists_open_loops x).mpr (h x)⟩

/-- 强局部可缩空间半局部单连通；该推导暂不注册为 instance。-/
theorem semilocallySimplyConnectedSpace_of_stronglyLocallyContractible
    [StronglyLocallyContractibleSpace X] :
    SemilocallySimplyConnectedSpace X := by
  constructor
  intro x
  obtain ⟨S, ⟨hSnhds, hScontractible⟩, _⟩ :=
    (contractible_basis x).mem_iff.mp (Filter.univ_mem : Set.univ ∈ 𝓝 x)
  obtain ⟨U, hUS, hUopen, hxU⟩ := mem_nhds_iff.mp hSnhds
  refine ⟨U, hUopen, hxU, le_antisymm ?_ bot_le⟩
  rintro g ⟨q, rfl⟩
  let iUS : C(U, S) := ContinuousMap.inclusion hUS
  let iSX : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iUX : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let _ : ContractibleSpace S := hScontractible
  have hq : FundamentalGroup.map iUS ⟨x, hxU⟩ q = 1 := Subsingleton.elim _ _
  have hq' : Path.Homotopic.Quotient.map q iUS =
      Path.Homotopic.Quotient.refl (iUS ⟨x, hxU⟩) := hq
  have hi : iSX.comp iUS = iUX := by ext; rfl
  have hcomp : Path.Homotopic.Quotient.map q (iSX.comp iUS) =
      Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.map q iUS) iSX :=
    Path.Homotopic.Quotient.map_comp
  change FundamentalGroup.map iUX ⟨x, hxU⟩ q = 1
  rw [← hi, FundamentalGroup.map_apply, hcomp, ← FundamentalGroup.map_apply, hq']
  rfl

/-- 单连通空间半局部单连通；该推导暂不注册为 instance。-/
theorem semilocallySimplyConnectedSpace_of_simplyConnected
    [SimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace X := by
  constructor
  intro x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, le_antisymm ?_ bot_le⟩
  rintro g ⟨q, rfl⟩
  change FundamentalGroup.map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.univ, X)) ⟨x, Set.mem_univ x⟩ q = 1
  exact Subsingleton.elim _ _

end SandronesLibrary.Topology
