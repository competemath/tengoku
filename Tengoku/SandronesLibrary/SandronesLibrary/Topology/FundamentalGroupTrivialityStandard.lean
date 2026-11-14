/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupOperationsStandard
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Tengoku.Seed.Analysis.Convex.Contractible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 单连通与可缩空间的平凡基本群

本文件把单连通空间中道路同伦类唯一这一教材事实落实为基本群元素等于单位元，并专门化到可缩
空间和非空凸集。圆周基本群和积空间计算不在本批范围内。

当前条目：

* `topology.fundamental-group.triviality-standard`。
-/

namespace SandronesLibrary.Topology

universe u

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- 单连通空间中，任意基本群元素都等于单位元。

> **Entry**: topology.fundamental-group.triviality-standard
@isnad1 id=eq.0h3v.s5.ce4cf8ecd2ed from=translated src=- shape=ff99fe8e vocab=63fbc906
-/
theorem fundamentalGroup_eq_one_of_simplyConnected
    [SimplyConnectedSpace X] (g : FundamentalGroup X x) : g = 1 :=
  Subsingleton.elim _ _

/-- 可缩空间是单连通的，因此任意基本群元素都等于单位元。
@isnad1 id=eq.0h3v.s5.8de44a0a6f3f from=translated src=- shape=ff99fe8e vocab=c4e87588
-/
theorem fundamentalGroup_eq_one_of_contractible
    [ContractibleSpace X] (g : FundamentalGroup X x) : g = 1 :=
  Subsingleton.elim _ _

/-- 单连通空间中，任意基点环路的道路同伦商类都等于恒等道路类。
@isnad1 id=eq.0h3v.s4.d7cbd67a7e4b from=translated src=- shape=bc4332d4 vocab=c703f625
-/
theorem loopHomotopyClass_eq_refl_of_simplyConnected
    [SimplyConnectedSpace X] (p : Path.Homotopic.Quotient x x) :
    p = Path.Homotopic.Quotient.refl x :=
  Subsingleton.elim _ _

/-- 实拓扑向量空间中的非空凸集可缩，所以在任意基点处基本群平凡。
@isnad1 id=eq.2h4v.s8.45a2c105d270 from=translated src=- shape=33cefe76 vocab=ea45ebcf
-/
theorem fundamentalGroup_eq_one_of_convex
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty)
    (x : s) (g : FundamentalGroup s x) : g = 1 := by
  let _ : ContractibleSpace s := hs.contractibleSpace hne
  exact Subsingleton.elim _ _

end SandronesLibrary.Topology
