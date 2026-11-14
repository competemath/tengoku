/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringHomotopyLiftStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 覆盖映射的 monodromy

本模块直接复用 Mathlib `IsCoveringMap.monodromy` 与基本群作用，不重定义 fiber transport。新增的课程
桥把代表道路的 monodromy 值明确识别为 C2 标准道路提升的终点，并把基环路提升闭合识别为初始
fiber 点在 monodromy 下不动。

当前条目：

* `topology.covering.monodromy-standard`。

道路复合采用 Mathlib `Path.trans` 的先左后右约定，故 `monodromy (gamma.trans gamma') e` 等于先
应用 `gamma` 再应用 `gamma'`；逆道路给出反向 fiber transport。提升判据另置 C4b 文件。
-/

open scoped unitInterval

namespace SandronesLibrary.Topology

universe u v

variable {E : Type u} {X : Type v}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/-- 代表道路的 monodromy 值就是从指定 fiber 点出发的标准提升终点。

> **Entry**: topology.covering.monodromy-standard-/
theorem coveringMap_monodromy_mk_eq_pathLift_endpoint
    (cov : IsCoveringMap p) {x y : X} (gamma : Path x y) (e : p ⁻¹' {x}) :
    cov.monodromy ⟦gamma⟧ e =
      ⟨coveringMapPathLift cov gamma e.1 e.2 1,
        coveringMapPathLift_endpoint_mem_fiber cov gamma e.1 e.2⟩ := by
  rfl

/-- 基环路的标准提升闭合，当且仅当 monodromy 固定指定的初始 fiber 点。-/
theorem coveringMap_pathLift_closed_iff_monodromy_fixed
    (cov : IsCoveringMap p) {x : X} (gamma : Path x x) (e : p ⁻¹' {x}) :
    coveringMapPathLift cov gamma e.1 e.2 1 = e.1 ↔
      cov.monodromy ⟦gamma⟧ e = e := by
  rw [coveringMap_monodromy_mk_eq_pathLift_endpoint]
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congr_arg Subtype.val h

end SandronesLibrary.Topology
