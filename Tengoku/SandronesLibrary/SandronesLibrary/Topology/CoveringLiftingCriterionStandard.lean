/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringMonodromyStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 覆盖映射的提升判据

Mathlib 已证明基本群像包含条件足以给出保持指定基点的唯一连续提升。本模块补充教材判据的必要方向：
若全局提升已经存在，则由提升诱导的基本群元素提供覆盖投影像中的原像。二者合并后得到 Hatcher
Proposition 1.33 的存在 iff 与存在唯一 iff。

当前条目：

* `topology.covering.lifting-criterion-standard`。

这里不以 simply connected 特例代替一般判据，也不构造 universal cover 或覆盖空间分类。
-/

open Function

namespace SandronesLibrary.Topology

universe u v w

variable {E : Type u} {X : Type v} {A : Type w}
variable [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
variable {p : E → X}

set_option backward.isDefEq.respectTransparency.types false in
/-- 若 `f` 已有保持指定基点的连续提升，则 `f` 的基本群像包含在覆盖投影的基本群像中。

> **Entry**: topology.covering.lifting-criterion-standard
@isnad1 id=le.3h7v.s8.c9ae3e9ce149 from=translated src=- shape=5e69dfa0 vocab=123857f8
-/
theorem coveringMap_lift_range_le_of_exists
    (cov : IsCoveringMap p) {f : C(A, X)} {a0 : A} {e0 : E} (he : p e0 = f a0)
    (hex : ∃ F : C(A, E), F a0 = e0 ∧ p ∘ F = f) :
    (FundamentalGroup.map f a0).range ≤
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  obtain ⟨F, hF0, hpF⟩ := hex
  subst e0
  have hmap : (⟨p, cov.continuous⟩ : C(E, X)).comp F = f :=
    ContinuousMap.ext fun a => congr_fun hpF a
  subst f
  cases he
  rintro g ⟨q, rfl⟩
  refine ⟨FundamentalGroup.map F a0 q, ?_⟩
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    FundamentalGroup.map_apply]
  have hcomp : Path.Homotopic.Quotient.map q
      ((⟨p, cov.continuous⟩ : C(E, X)).comp F) =
      Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map q F)
        (⟨p, cov.continuous⟩ : C(E, X)) :=
    Path.Homotopic.Quotient.map_comp
  simpa using hcomp.symm

/-- 对道路连通且局部道路连通的定义域，保持指定基点的连续提升存在，当且仅当基本群像满足包含条件。
@isnad1 id=iff.2h7v.s8.0bb5241da7a0 from=translated src=- shape=1022b774 vocab=55840b0a
-/
theorem exists_coveringMap_lift_iff_range_le
    (cov : IsCoveringMap p) [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a0 : A} {e0 : E} (he : p e0 = f a0) :
    (∃ F : C(A, E), F a0 = e0 ∧ p ∘ F = f) ↔
      (FundamentalGroup.map f a0).range ≤
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  constructor
  · exact coveringMap_lift_range_le_of_exists cov he
  · exact fun h => (cov.existsUnique_continuousMap_lifts_of_range_le he h).exists

/-- 在相同假设下，唯一连续提升的存在也恰好等价于基本群像包含条件。
@isnad1 id=iff.2h7v.s8.0c7fc0bfa3c6 from=translated src=- shape=1022b774 vocab=64b3d769
-/
theorem existsUnique_coveringMap_lift_iff_range_le
    (cov : IsCoveringMap p) [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a0 : A} {e0 : E} (he : p e0 = f a0) :
    (∃! F : C(A, E), F a0 = e0 ∧ p ∘ F = f) ↔
      (FundamentalGroup.map f a0).range ≤
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  constructor
  · intro h
    exact coveringMap_lift_range_le_of_exists cov he h.exists
  · exact cov.existsUnique_continuousMap_lifts_of_range_le he

end SandronesLibrary.Topology
