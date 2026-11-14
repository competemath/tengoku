/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Topology.Path

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 道路的子空间余域限制

本文件把环境空间中值域包含于集合 `S` 的道路视为 subtype `S` 中的道路，并给出强制转换回环境
空间的逐点计算规则。该构造只依赖道路连续性和 subtype 拓扑，不属于 van Kampen 专用理论。

当前条目：

* `topology.homotopy.path-cod-restrict`。
-/

open Set
open scoped unitInterval

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 将值域位于 `S` 的道路视为 subtype `S` 中、具有指定端点成员证明的道路。

> **Entry**: topology.homotopy.path-cod-restrict-/
def pathCodRestrict {x y : X} (S : Set X) (p : Path x y)
    (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) :
    Path (⟨x, hx⟩ : S) ⟨y, hy⟩ where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := by ext; exact p.source
  target' := by ext; exact p.target

@[simp] theorem pathCodRestrict_coe {x y : X} (S : Set X) (p : Path x y)
    (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S)
    (t : unitInterval) :
    ((pathCodRestrict S p hx hy hp t : S) : X) = p t :=
  rfl

end SandronesLibrary.Topology
