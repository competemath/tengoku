/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringMapStandard
import Tengoku.Seed.Topology.Homotopy.Lifting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 覆盖映射的道路提升

本模块直接复用 Mathlib `IsCoveringMap.liftPath` 的存在唯一性证明，冻结教材中的量词：给定基空间道路
和其起点上方的一个点，存在唯一以该点为初值的连续提升。另将该连续映射薄封装为标准 `Path`，终点
由提升在时间一的值决定。

当前条目：

* `topology.covering.path-lifting-standard`。

本文件不另写提升算法、不指定目标 fiber 中的终点，也不包含同伦提升或 monodromy。
-/

open Set Function
open scoped unitInterval

namespace SandronesLibrary.Topology

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/-- 给定基道路和其起点上方的一个点，存在唯一以该点为初值的连续提升。

> **Entry**: topology.covering.path-lifting-standard
@isnad1 id=existsun.2h7v.s7.f0987878f6f5 from=translated src=- shape=c2024dee vocab=ba000154
-/
theorem existsUnique_coveringMap_pathLift
    (cov : IsCoveringMap p) {x y : X} (gamma : Path x y)
    (e : E) (he : p e = x) :
    ∃! Gamma : C(unitInterval, E),
      Gamma 0 = e ∧ p ∘ Gamma = gamma := by
  let hzero : gamma 0 = p e := gamma.source.trans he.symm
  refine ⟨cov.liftPath gamma e hzero,
    ⟨cov.liftPath_zero gamma e hzero, cov.liftPath_lifts gamma e hzero⟩, ?_⟩
  intro Gamma hGamma
  exact (cov.eq_liftPath_iff' hzero).mpr ⟨hGamma.2, hGamma.1⟩

/-- 把 Mathlib 的连续提升视为标准的端点索引 `Path`；目标点定义为唯一提升在时间一的值。-/
noncomputable def coveringMapPathLift
    (cov : IsCoveringMap p) {x y : X} (gamma : Path x y)
    (e : E) (he : p e = x) :
    Path e (cov.liftPath gamma e (gamma.source.trans he.symm) 1) where
  toFun := cov.liftPath gamma e (gamma.source.trans he.symm)
  continuous_toFun := (cov.liftPath gamma e (gamma.source.trans he.symm)).continuous
  source' := cov.liftPath_zero gamma e (gamma.source.trans he.symm)
  target' := rfl

/-- 标准道路视图经覆盖映射逐点投影回原基道路。
@isnad1 id=eq.2h8v.s8.1190f7aa74ab from=translated src=- shape=964d10f0 vocab=568a8793
-/
theorem coveringMapPathLift_lifts
    (cov : IsCoveringMap p) {x y : X} (gamma : Path x y)
    (e : E) (he : p e = x) (t : unitInterval) :
    p (coveringMapPathLift cov gamma e he t) = gamma t :=
  congr_fun (cov.liftPath_lifts gamma e (gamma.source.trans he.symm)) t

/-- 道路提升所决定的终点位于基道路终点的 fiber 中。
@isnad1 id=eq.2h7v.s8.90a6e7176eea from=translated src=- shape=f3ac5d0b vocab=568a8793
-/
theorem coveringMapPathLift_endpoint_mem_fiber
    (cov : IsCoveringMap p) {x y : X} (gamma : Path x y)
    (e : E) (he : p e = x) :
    p (coveringMapPathLift cov gamma e he 1) = y :=
  (coveringMapPathLift_lifts cov gamma e he 1).trans gamma.target

end SandronesLibrary.Topology
