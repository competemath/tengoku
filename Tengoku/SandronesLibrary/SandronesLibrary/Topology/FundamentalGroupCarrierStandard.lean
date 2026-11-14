/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathHomotopyQuotientStandard
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 基本群胚与基本群的标准承载

本文件解释 Mathlib 基本群胚的对象、态射和基点自同态群，并记录它们与标准道路同伦商之间的
定义性对应。本批只处理承载，不开放群运算或函子性。

当前条目：

* `topology.fundamental-group.carrier-standard`。
-/

open CategoryTheory

namespace SandronesLibrary.Topology

universe u

variable {X : Type u}

/-- 基本群胚的对象只是空间点的包装；标准等价把由 `x` 构造的对象严格还原为 `x`。

> **Entry**: topology.fundamental-group.carrier-standard-/
theorem fundamentalGroupoid_equiv_mk_apply (x : X) :
    FundamentalGroupoid.equiv X (FundamentalGroupoid.mk x) = x :=
  rfl

variable [TopologicalSpace X]
variable {x y : X}

/-- 基本群胚中从 `x` 到 `y` 的态射类型定义性地就是从 `x` 到 `y` 的道路同伦商。-/
theorem fundamentalGroupoid_hom_eq_pathHomotopyQuotient :
    (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
      Path.Homotopic.Quotient x y :=
  rfl

/-- 基点 `x` 处基本群的底层类型定义性地就是基点环路的道路同伦商。-/
theorem fundamentalGroup_eq_loopHomotopyQuotient :
    FundamentalGroup X x = Path.Homotopic.Quotient x x :=
  rfl

/-- 把环路同伦商类视为基本群元素后再转回道路视角，严格得到原商类。-/
theorem fundamentalGroup_toPath_fromPath
    (p : Path.Homotopic.Quotient x x) :
    FundamentalGroup.toPath (FundamentalGroup.fromPath p) = p :=
  rfl

/-- 把基本群元素转成环路同伦商类后再恢复，严格得到原元素。-/
theorem fundamentalGroup_fromPath_toPath (g : FundamentalGroup X x) :
    FundamentalGroup.fromPath (FundamentalGroup.toPath g) = g :=
  rfl

end SandronesLibrary.Topology
