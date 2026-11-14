/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Topology.Covering.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 覆盖映射与均匀覆盖邻域

本模块直接采用 Mathlib `IsEvenlyCovered` 与 `IsCoveringMap` 作为教材概念的正式承载，展开开邻域上的
离散纤维乘积图，并记录覆盖映射的基础拓扑性质。

当前条目：

* `topology.covering.definition-standard`。

Mathlib 的 carrier 不要求覆盖映射满射，因而允许空纤维；采用教材常见的满射约定时必须另加
`Function.Surjective p`。本文件不另造覆盖空间 structure，也不包含道路或同伦提升。
-/

open Set Bundle Topology

namespace SandronesLibrary.Topology

universe u v w

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]

/-- Mathlib 的均匀覆盖点承载展开为离散 fiber 类型，以及该点某个开邻域上的乘积同胚图。

> **Entry**: topology.covering.definition-standard-/
theorem isEvenlyCovered_iff_exists_open_product
    (p : E → X) (x : X) (I : Type w) [TopologicalSpace I] :
    IsEvenlyCovered p x I ↔
      DiscreteTopology I ∧
        ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsOpen (p ⁻¹' U) ∧
          ∃ H : p ⁻¹' U ≃ₜ U × I, ∀ e, (H e).1.1 = p e :=
  Iff.rfl

/-- Mathlib 的覆盖映射承载恰好要求每个基点都被均匀覆盖，并以该点的实际集合论 fiber 作为离散
索引。-/
theorem isCoveringMap_iff_every_point_evenlyCovered (p : E → X) :
    IsCoveringMap p ↔ ∀ x, IsEvenlyCovered p x (p ⁻¹' {x}) :=
  Iff.rfl

/-- 覆盖映射在每个基点提供显式开乘积邻域；Mathlib carrier 允许 fiber 为空。-/
theorem coveringMap_exists_open_product_neighborhood
    {p : E → X} (hp : IsCoveringMap p) (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsOpen (p ⁻¹' U) ∧
      ∃ H : p ⁻¹' U ≃ₜ U × (p ⁻¹' {x}), ∀ e, (H e).1.1 = p e :=
  (hp x).2

/-- 覆盖映射的每个 fiber 都带离散拓扑。-/
theorem coveringMap_discreteTopology_fiber
    {p : E → X} (hp : IsCoveringMap p) (x : X) :
    DiscreteTopology (p ⁻¹' {x}) :=
  (hp x).discreteTopology_fiber

/-- 标准覆盖映射承载同时推出连续性、开映射性和局部同胚性质。-/
theorem coveringMap_continuous_and_isOpenMap_and_isLocalHomeomorph
    {p : E → X} (hp : IsCoveringMap p) :
    Continuous p ∧ IsOpenMap p ∧ IsLocalHomeomorph p :=
  ⟨hp.continuous, hp.isOpenMap, hp.isLocalHomeomorph⟩

/-- 在许多教材额外采用的满射约定下，覆盖映射还是商映射。-/
theorem coveringMap_isQuotientMap_of_surjective
    {p : E → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    IsQuotientMap p :=
  hp.isQuotientMap hsurj

end SandronesLibrary.Topology
