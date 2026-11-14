/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupOperationsStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 子群对应覆盖的道路类承载

给定基点 `x0` 与子群 `H ≤ π₁(X, x0)`，本模块先收集所有从 `x0` 出发、终点可变的道路同伦类，
再把在起点前拼接 `H` 中环路所产生的道路类识别。所得轨道商是覆盖空间分类中与 `H` 对应的候选
总空间承载；端点给出一个集合层投影到 `X`。

当前条目：

* `topology.covering.subgroup-path-class-standard`。

本文件严格止于类型承载、轨道等价关系和端点投影。它不赋予商类型拓扑，不证明投影连续或为
covering map，也不发布依赖端点 equality cast 的差环路刻画。
-/

namespace SandronesLibrary.Topology

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] (x0 : X)

/-- 从固定基点 `x0` 出发、终点可变的道路同伦类。

字段 `endpoint` 记录终点；`path` 直接复用 Mathlib 的端点固定道路同伦商。

> **Entry**: topology.covering.subgroup-path-class-standard-/
structure CoveringSubgroupBasedPath where
  endpoint : X
  path : Path.Homotopic.Quotient x0 endpoint

namespace CoveringSubgroupBasedPath

variable {x0} (H : Subgroup (FundamentalGroup X x0))

/-- 在 based path 的起点前拼接一个属于 `H` 的环路；终点保持不变。-/
def prepend (h : H) (a : CoveringSubgroupBasedPath x0) :
    CoveringSubgroupBasedPath x0 where
  endpoint := a.endpoint
  path := h.1.trans a.path

/-- 子群 `H` 在 based paths 上的轨道关系。-/
def Related (a b : CoveringSubgroupBasedPath x0) : Prop :=
  ∃ h : H, prepend H h a = b

/-- 单位环路在起点前拼接不改变 based path。
@isnad1 id=eq.0h4v.s7.23f3a78cf5b3 from=translated src=- shape=fd891daf vocab=598f7380
-/
theorem prepend_one (a : CoveringSubgroupBasedPath x0) :
    prepend H 1 a = a := by
  rcases a with ⟨y, gamma⟩
  unfold prepend
  congr 1
  change (Path.Homotopic.Quotient.refl x0).trans gamma = gamma
  exact Path.Homotopic.Quotient.refl_trans gamma

/-- `prepend` 遵循由 Mathlib 基本群乘法次序产生的反作用律。

Mathlib 中 `h * k` 的道路代表是先走 `k`、再走 `h`，所以一次拼接 `h * k` 等于先作用 `h`、
再作用 `k`。
@isnad1 id=eq.0h6v.s8.ae74d65db42b from=translated src=- shape=aed35809 vocab=9b3efee4
-/
theorem prepend_mul (h k : H) (a : CoveringSubgroupBasedPath x0) :
    prepend H (h * k) a = prepend H k (prepend H h a) := by
  rcases a with ⟨y, gamma⟩
  unfold prepend
  congr 1
  change (k.1.trans h.1).trans gamma = k.1.trans (h.1.trans gamma)
  exact Path.Homotopic.Quotient.trans_assoc k.1 h.1 gamma

/-- 每个 based path 与自身相关。
@isnad1 id=related.0h4v.s5.b0ba9e87f9e4 from=translated src=- shape=2ee0929a vocab=4d31d8ec
-/
theorem related_refl (a : CoveringSubgroupBasedPath x0) : Related H a a :=
  ⟨1, prepend_one H a⟩

/-- 子群轨道关系是对称的。
@isnad1 id=related.1h5v.s5.7534654dcf8d from=translated src=- shape=d618a354 vocab=4d31d8ec
-/
theorem related_symm {a b : CoveringSubgroupBasedPath x0} :
    Related H a b → Related H b a := by
  rintro ⟨h, rfl⟩
  refine ⟨h⁻¹, ?_⟩
  rw [← prepend_mul]
  simpa using prepend_one H a

/-- 子群轨道关系是传递的。
@isnad1 id=related.2h6v.s5.8aab6731c37e from=translated src=- shape=8ed3e52f vocab=4d31d8ec
-/
theorem related_trans {a b c : CoveringSubgroupBasedPath x0} :
    Related H a b → Related H b c → Related H a c := by
  rintro ⟨h, rfl⟩ ⟨k, rfl⟩
  exact ⟨h * k, prepend_mul H h k a⟩

/-- 子群轨道关系构成等价关系。
@isnad1 id=equivale.0h3v.s5.dbcb7531cba9 from=translated src=- shape=b0773581 vocab=147d9e82
-/
theorem related_equivalence : Equivalence (Related H) :=
  ⟨related_refl H, related_symm H, related_trans H⟩

/-- 子群 `H` 的 based-path 轨道 setoid。-/
def orbitSetoid : Setoid (CoveringSubgroupBasedPath x0) where
  r := Related H
  iseqv := related_equivalence H

/-- 相关的 based paths 具有相同终点。
@isnad1 id=eq.1h5v.s5.6ee30d9ecfe7 from=translated src=- shape=2d455793 vocab=75e0d1ef
-/
theorem endpoint_eq_of_related {a b : CoveringSubgroupBasedPath x0}
    (hab : Related H a b) : a.endpoint = b.endpoint := by
  obtain ⟨h, rfl⟩ := hab
  rfl

end CoveringSubgroupBasedPath

/-- 从 `x0` 出发的道路同伦类关于子群 `H` 起点拼接作用的轨道商。-/
def CoveringSubgroupPathClass (H : Subgroup (FundamentalGroup X x0)) :=
  Quotient (CoveringSubgroupBasedPath.orbitSetoid H)

namespace CoveringSubgroupPathClass

variable {x0} (H : Subgroup (FundamentalGroup X x0))

/-- 把子群道路类送到其终点的集合层投影。-/
def projection : CoveringSubgroupPathClass x0 H → X :=
  Quotient.lift CoveringSubgroupBasedPath.endpoint fun a b hab => by
    change CoveringSubgroupBasedPath.Related H a b at hab
    exact CoveringSubgroupBasedPath.endpoint_eq_of_related H hab

end CoveringSubgroupPathClass

end

end SandronesLibrary.Topology
