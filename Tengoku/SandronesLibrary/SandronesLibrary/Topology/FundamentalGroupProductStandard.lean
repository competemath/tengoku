/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupOperationsStandard
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.Product

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 积空间的基本群

本文件在指定基点 `(x,y)` 处说明积空间基本群由两个坐标基本群逐分量组成。正向映射把两个道路
同伦类组成积道路，反向映射由两个坐标投影诱导；两者互逆。Mathlib 的基本群胚积同构
`FundamentalGroupoidFunctor.prodIso` 在正向等价的定义中被真实使用，并由公开公式展开。

当前条目：

* `topology.fundamental-group.product-standard`。
-/

open CategoryTheory
open scoped FundamentalGroupoid

namespace SandronesLibrary.Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- 两个坐标投影在指定积基点处诱导一个从积空间基本群到两个基本群之积的同态。

> **Entry**: topology.fundamental-group.product-standard-/
noncomputable def fundamentalGroupProdProjections (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) →* FundamentalGroup X x × FundamentalGroup Y y :=
  (FundamentalGroup.map ⟨Prod.fst, continuous_fst⟩ (x, y)).prod
    (FundamentalGroup.map ⟨Prod.snd, continuous_snd⟩ (x, y))

/-- 基本群胚的积比较同构在对象 `(x,y)` 的自同态群上给出基本群乘法等价。正向映射直接使用
`FundamentalGroupoidFunctor.prodIso.hom.map`，反向映射取两个投影类。-/
noncomputable def fundamentalGroupProdMulEquiv (x : X) (y : Y) :
    FundamentalGroup X x × FundamentalGroup Y y ≃* FundamentalGroup (X × Y) (x, y) :=
  let E := FundamentalGroupoidFunctor.prodIso (TopCat.of X) (TopCat.of Y)
  let a : FundamentalGroupoid X × FundamentalGroupoid Y :=
    (FundamentalGroupoid.mk x, FundamentalGroupoid.mk y)
  {
    toFun := fun gh ↦ E.hom.map (X := a) (Y := a) gh
    invFun := fun k ↦ (Path.Homotopic.projLeft k, Path.Homotopic.projRight k)
    left_inv := fun gh ↦ by
      apply Prod.ext
      · exact Path.Homotopic.projLeft_prod gh.1 gh.2
      · exact Path.Homotopic.projRight_prod gh.1 gh.2
    right_inv := fun k ↦ by
      exact Path.Homotopic.prod_projLeft_projRight k
    map_mul' := fun gh₀ gh₁ ↦ by
      change Path.Homotopic.prod (gh₁.1.trans gh₀.1) (gh₁.2.trans gh₀.2) =
        (Path.Homotopic.prod gh₁.1 gh₁.2).trans
          (Path.Homotopic.prod gh₀.1 gh₀.2)
      exact (Path.Homotopic.comp_prod_eq_prod_comp gh₁.1 gh₁.2 gh₀.1 gh₀.2).symm
  }

/-- 在指定基点 `(x,y)`，积空间基本群等价把 `(g,h)` 送到逐点配对所得的积道路同伦类。
@isnad1 id=eq.0h6v.s8.44b1c3c350a5 from=translated src=- shape=3d4021c4 vocab=d590632f
-/
theorem fundamentalGroupProdMulEquiv_apply (x : X) (y : Y)
    (g : FundamentalGroup X x) (h : FundamentalGroup Y y) :
    fundamentalGroupProdMulEquiv x y (g, h) = Path.Homotopic.prod g h := by
  rfl

/-- 投影同态在道路同伦商上的作用就是分别取道路的两个坐标。
@isnad1 id=eq.0h5v.s8.662db97ceddf from=translated src=- shape=49a8adb9 vocab=6a38bb5a
-/
theorem fundamentalGroupProdProjections_apply (x : X) (y : Y)
    (k : FundamentalGroup (X × Y) (x, y)) :
    fundamentalGroupProdProjections x y k =
      (Path.Homotopic.projLeft k, Path.Homotopic.projRight k) := by
  rfl

/-- 先组成积道路再投影，恢复原来的两个基本群元素。
@isnad1 id=eq.0h4v.s9.6c53290ece7d from=translated src=- shape=44572578 vocab=ee70a6d5
-/
theorem fundamentalGroupProdProjections_comp_equiv (x : X) (y : Y) :
    (fundamentalGroupProdProjections x y).comp
      (fundamentalGroupProdMulEquiv x y).toMonoidHom = MonoidHom.id _ := by
  apply MonoidHom.ext
  rintro ⟨g, h⟩
  apply Prod.ext
  · change Path.Homotopic.projLeft (Path.Homotopic.prod g h) = g
    exact Path.Homotopic.projLeft_prod g h
  · change Path.Homotopic.projRight (Path.Homotopic.prod g h) = h
    exact Path.Homotopic.projRight_prod g h

/-- 先投影一个积空间环路类再组成积道路，恢复原环路类。
@isnad1 id=eq.0h4v.s9.aef9a0f5bdb2 from=translated src=- shape=21e16fce vocab=ee70a6d5
-/
theorem fundamentalGroupProdMulEquiv_comp_projections (x : X) (y : Y) :
    (fundamentalGroupProdMulEquiv x y).toMonoidHom.comp
      (fundamentalGroupProdProjections x y) = MonoidHom.id _ := by
  ext k
  change Path.Homotopic.prod (Path.Homotopic.projLeft k)
    (Path.Homotopic.projRight k) = k
  exact Path.Homotopic.prod_projLeft_projRight k

end SandronesLibrary.Topology
