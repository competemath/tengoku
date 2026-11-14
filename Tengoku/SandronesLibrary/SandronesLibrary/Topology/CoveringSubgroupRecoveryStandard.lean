/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringMapStandard
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupFunctorialityStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 从 pointed connected covering 恢复基本群子群

本文件捆绑一个道路连通 total space 上的 covering projection，以及投影到给定
basepoint 的 lift point。对应子群定义为投影诱导的基本群同态之像，并证明保持
base 和 lift point 的 covering 同胚不改变该子群。

当前条目：

* `topology.covering.pointed-recovered-subgroup`。

这只是 covering-to-subgroup 方向。本文件不证明 C5c 构造的 cover 恢复出原子群，
不建立 pointed/unpointed 分类双射，也不构造 universal cover。
-/

open Set

namespace SandronesLibrary.Topology

noncomputable section

universe u v w

private theorem fundamentalGroup_mapOfEq_comp_apply
    {A : Type u} {B : Type v} {Z : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    (f : C(A, B)) (g : C(B, Z)) {a : A} {b : B} {z : Z}
    (hf : f a = b) (hg : g b = z) (p : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf p) =
      FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) p := by
  cases hf
  cases hg
  simp only [FundamentalGroup.mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_cast]
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  exact (Path.Homotopic.Quotient.map_comp (p := p) (f := f) (g := g)).symm

private theorem fundamentalGroup_mapOfEq_congr
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (hfg : f = g) {a : A} {b : B}
    (hf : f a = b) (hg : g a = b) (p : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq f hf p = FundamentalGroup.mapOfEq g hg p := by
  subst g
  have hproof : hf = hg := Subsingleton.elim _ _
  subst hg
  rfl

/-- 一个道路连通 total space 上的 covering projection，配有给定 basepoint 上的选定点。

> **Entry**: topology.covering.pointed-recovered-subgroup-/
structure PointedCovering (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) where
  Total : Type v
  topology : TopologicalSpace Total
  pathConnected : @PathConnectedSpace Total topology
  projection : Total → X
  isCoveringMap : @IsCoveringMap Total X topology inferInstance projection
  point : Total
  projection_point : projection point = x0

namespace PointedCovering

variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {x0 : X}

instance (C : PointedCovering X x0) : TopologicalSpace C.Total := C.topology

def projectionContinuousMap (C : PointedCovering X x0) : C(C.Total, X) :=
  ⟨C.projection, C.isCoveringMap.continuous⟩

/--
@isnad1 id=eq.0h3v.s6.96d0c0696f5f from=translated src=- shape=8fd877db vocab=5c266168
-/
theorem projectionContinuousMap_point (C : PointedCovering X x0) :
    C.projectionContinuousMap C.point = x0 := C.projection_point

/-- pointed covering 恢复的子群是投影诱导的基本群同态之像。

> **Entry**: topology.covering.pointed-recovered-subgroup-/
def recoveredSubgroup (C : PointedCovering X x0) : Subgroup (FundamentalGroup X x0) :=
  (FundamentalGroup.mapOfEq C.projectionContinuousMap C.projectionContinuousMap_point).range

/-- pointed coverings 的等价是严格保持 base projection 和选定 lift point 的 total-space
homeomorphism。

> **Entry**: topology.covering.pointed-recovered-subgroup-/
structure Equiv (C D : PointedCovering X x0) where
  toHomeomorph : C.Total ≃ₜ D.Total
  projection_commutes : D.projection ∘ toHomeomorph = C.projection
  point_eq : toHomeomorph C.point = D.point

namespace Equiv

variable {C D : PointedCovering X x0}

def refl (C : PointedCovering X x0) : C.Equiv C where
  toHomeomorph := Homeomorph.refl C.Total
  projection_commutes := rfl
  point_eq := rfl

def totalContinuousMap (e : C.Equiv D) : C(C.Total, D.Total) := e.toHomeomorph

/--
@isnad1 id=eq.0h5v.s7.c3e9806afd8f from=translated src=- shape=74908990 vocab=7c2f00f8
-/
theorem totalContinuousMap_point (e : C.Equiv D) :
    e.totalContinuousMap C.point = D.point := e.point_eq

/--
@isnad1 id=eq.0h5v.s6.8fc1a5e2d31b from=translated src=- shape=71888af5 vocab=7568fd11
-/
theorem projectionContinuousMap_comp (e : C.Equiv D) :
    D.projectionContinuousMap.comp e.totalContinuousMap = C.projectionContinuousMap := by
  ext z
  exact congrFun e.projection_commutes z

def symm (e : C.Equiv D) : D.Equiv C where
  toHomeomorph := e.toHomeomorph.symm
  projection_commutes := by
    funext z
    have hz := congrFun e.projection_commutes (e.toHomeomorph.symm z)
    simpa using hz.symm
  point_eq := by
    apply e.toHomeomorph.injective
    simpa using e.point_eq.symm

def trans {A B C : PointedCovering X x0} (e : A.Equiv B) (f : B.Equiv C) :
    A.Equiv C where
  toHomeomorph := e.toHomeomorph.trans f.toHomeomorph
  projection_commutes := by
    funext z
    rw [Function.comp_apply, Homeomorph.trans_apply]
    exact (congrFun f.projection_commutes (e.toHomeomorph z)).trans
      (congrFun e.projection_commutes z)
  point_eq := by
    rw [Homeomorph.trans_apply, e.point_eq, f.point_eq]

end Equiv

private theorem recoveredSubgroup_le_of_equiv {C D : PointedCovering X x0} (e : Equiv C D) :
    recoveredSubgroup C ≤ recoveredSubgroup D := by
  rintro g ⟨a, rfl⟩
  refine ⟨FundamentalGroup.mapOfEq e.totalContinuousMap e.totalContinuousMap_point a, ?_⟩
  rw [fundamentalGroup_mapOfEq_comp_apply]
  apply fundamentalGroup_mapOfEq_congr e.projectionContinuousMap_comp

/-- pointed-cover equivalence 保持由投影恢复的子群。

> **Entry**: topology.covering.pointed-recovered-subgroup
@isnad1 id=eq.0h5v.s5.53b9fe3802d9 from=translated src=- shape=aaf27a80 vocab=7f1613dd
-/
theorem recoveredSubgroup_eq_of_equiv {C D : PointedCovering X x0} (e : Equiv C D) :
    recoveredSubgroup C = recoveredSubgroup D :=
  le_antisymm (recoveredSubgroup_le_of_equiv e)
    (recoveredSubgroup_le_of_equiv e.symm)

end PointedCovering

end

end SandronesLibrary.Topology
