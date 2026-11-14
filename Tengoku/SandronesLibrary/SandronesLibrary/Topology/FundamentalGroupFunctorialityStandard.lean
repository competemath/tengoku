/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupOperationsStandard
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 基本群诱导映射的函子律与同伦自然性

本文件解释连续映射怎样诱导基本群同态、恒等与复合怎样保持，以及两个同伦映射诱导的基本群胚
函子怎样由同伦轨迹自然同构。基点变换和同伦等价不变性留给独立后续文件。

当前条目：

* `topology.fundamental-group.functoriality-standard`。
-/

open CategoryTheory
open scoped ContinuousMap

namespace SandronesLibrary.Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- 连续映射诱导的基本群同态逐个环路作用，就是把道路同伦类沿该连续映射送到目标空间。

> **Entry**: topology.fundamental-group.functoriality-standard
@isnad1 id=eq.0h5v.s8.6f993f6b011c from=translated src=- shape=79bd452a vocab=f94cd098
-/
theorem fundamentalGroup_map_toPath (f : C(X, Y)) (x : X)
    (p : FundamentalGroup X x) :
    FundamentalGroup.toPath ((FundamentalGroup.map f x) p) =
      Path.Homotopic.Quotient.map (FundamentalGroup.toPath p) f :=
  rfl

/-- 恒等连续映射诱导基本群上的恒等群同态。
@isnad1 id=eq.0h2v.s7.bd7d9a14a9f5 from=translated src=- shape=b7cd721a vocab=3c8f5704
-/
theorem fundamentalGroup_map_id (x : X) :
    FundamentalGroup.map (.id X) x = MonoidHom.id (FundamentalGroup X x) := by
  ext p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- 连续映射的复合诱导基本群同态的复合。
@isnad1 id=eq.0h6v.s8.9d56468cb620 from=translated src=- shape=3e80365b vocab=da511d87
-/
theorem fundamentalGroup_map_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  ext p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- 从 `f` 到 `g` 的同伦所给自然同构，在点 `x` 处分量正是 `x` 的同伦轨迹之道路同伦类。
@isnad1 id=eq.0h6v.s7.7c8e697d1d0a from=translated src=- shape=ba2a11db vocab=2643370a
-/
theorem homotopicMapsNatIso_app_eq_pathClass
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H).app (FundamentalGroupoid.mk x) =
      Path.Homotopic.Quotient.mk (H.evalAt x) :=
  rfl

/-- 同伦自然同构在基点环路上的自然性：沿 `f` 送出的环路再走基点轨迹，等于先走基点轨迹再沿
`g` 送出环路。这是两个不同目标基点处诱导同态之间的共轭关系，不是它们的字面相等。
@isnad1 id=eq.0h7v.s8.58ef7d571c7d from=translated src=- shape=5133e9fd vocab=33861278
-/
theorem homotopicMapsNatIso_naturality_loop
    {f g : C(X, Y)} (H : f.Homotopy g) {x : X} (p : FundamentalGroup X x) :
    (FundamentalGroupoid.map f).map p ≫
        (FundamentalGroupoidFunctor.homotopicMapsNatIso H).app (FundamentalGroupoid.mk x) =
      (FundamentalGroupoidFunctor.homotopicMapsNatIso H).app (FundamentalGroupoid.mk x) ≫
        (FundamentalGroupoid.map g).map p :=
  (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality p

end SandronesLibrary.Topology
