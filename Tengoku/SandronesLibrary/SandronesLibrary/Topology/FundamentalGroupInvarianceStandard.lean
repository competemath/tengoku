/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupFunctorialityStandard
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 基本群的基点变换与同伦等价不变性

本文件解释目标基点相等时的 transport、沿道路改变基点的共轭公式，以及同伦等价在对应基点处
诱导的基本群乘法等价。

当前条目：

* `topology.fundamental-group.invariance-standard`。
-/

open CategoryTheory
open scoped ContinuousMap

namespace SandronesLibrary.Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- 若连续映射把基点 `x` 送到一个命题上相等的指定基点 `y`，则诱导同态在道路商视角中先映射
环路，再沿端点等式作 transport。

> **Entry**: topology.fundamental-group.invariance-standard
@isnad1 id=eq.1h6v.s7.da358ace00ac from=translated src=- shape=7cc3b098 vocab=999eb44d
-/
theorem fundamentalGroup_mapOfEq_toPath
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (p : FundamentalGroup X x) :
    FundamentalGroup.toPath ((FundamentalGroup.mapOfEq f h) p) =
      (Path.Homotopic.Quotient.map (FundamentalGroup.toPath p) f).cast h.symm h.symm :=
  FundamentalGroup.mapOfEq_apply f h p

/-- 沿道路 `p : x₀ ⟶ x₁` 改变基点时，一个 `x₀` 基本群元素变成先走 `p` 的逆道路、再走原环路、
最后走 `p` 的共轭类。等式发生在道路同伦商上。
@isnad1 id=eq.0h5v.s7.cfb782282f43 from=translated src=- shape=05ed81e0 vocab=132a4efa
-/
theorem fundamentalGroup_changeBasepoint_toPath
    {x₀ x₁ : X} (p : Path x₀ x₁) (g : FundamentalGroup X x₀) :
    FundamentalGroup.toPath (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) =
      (Path.Homotopic.Quotient.mk p).symm.trans
        ((FundamentalGroup.toPath g).trans (Path.Homotopic.Quotient.mk p)) := by
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath, Iso.conj_apply]
  rfl

/-- 同伦等价 `e : X ≃ₕ Y` 在对应基点 `x` 与 `e x` 处诱导基本群的乘法等价。

Mathlib 已给出基本群胚的范畴等价；这里使用其正向函子的 fully faithful 性，把基点对象的自同态
群等价取出。-/
noncomputable def fundamentalGroupMulEquivOfHomotopyEquiv
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk x)

/-- 同伦等价所诱导基本群等价的正向作用，就是其正向连续映射诱导的基本群同态。
@isnad1 id=eq.0h5v.s9.bc38b35d84e5 from=translated src=- shape=bcdac65c vocab=0b227808
-/
theorem fundamentalGroupMulEquivOfHomotopyEquiv_apply
    (e : X ≃ₕ Y) (x : X) (g : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfHomotopyEquiv e x g = FundamentalGroup.map e.toFun x g :=
  rfl

end SandronesLibrary.Topology
