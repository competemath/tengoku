/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenCommonSharedEdge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 方格中异标签小格的公共边比较

本文件处理水平或竖直相邻小格标签不同时的公共边：先把整条公共边提升到覆盖交集，使用交集道路
连通性选择端点 connector，再以 Pushout 的定义关系识别它在两个覆盖成员基本群中的像，最终结合
两侧换 connector 公式得到真实单格边元素的精确非交换关系。

当前条目：

* `topology.fundamental-group.van-kampen-switch-shared-edge`。

本文件不统一同标签与异标签 transition，不进行有限 telescope，也不证明 kernel 消失、单射或
van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 水平相邻异标签格的规范公共竖边提升到覆盖交集。

> **Entry**: topology.fundamental-group.van-kampen-switch-shared-edge-/
def BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeInIntersection
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    Path
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero]
          using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩ : ↥(U ∩ V))
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one]
          using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩ : ↥(U ∩ V)) :=
  pathCodRestrict (U ∩ V)
    (squareGridVerticalEdge H D.steps D.steps_pos i.succ j)
    (by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0)
    (by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1)
    (D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch)

/-- 竖直相邻异标签格的规范公共横边提升到覆盖交集。-/
def BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeInIntersection
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    Path
      (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero]
          using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩ : ↥(U ∩ V))
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one]
          using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩ : ↥(U ∩ V)) :=
  pathCodRestrict (U ∩ V)
    (squareGridHorizontalEdge H D.steps D.steps_pos i j.succ)
    (by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0)
    (by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1)
    (D.verticalSwitchEdge_mem_intersection i j l hshared hswitch)

/--
@isnad1 id=eq.2h9v.s9.2da268d02cf0 from=translated src=- shape=31a9ad72 vocab=555ea71f
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_horizontalSwitchEdgeInIntersection
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (t : unitInterval) :
    ((D.horizontalSwitchEdgeInIntersection i k j hshared hswitch t : ↥(U ∩ V)) : X) =
      squareGridVerticalEdge H D.steps D.steps_pos i.succ j t := rfl

/--
@isnad1 id=eq.2h9v.s9.d40350b0e2b7 from=translated src=- shape=2fff9685 vocab=01406c06
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_verticalSwitchEdgeInIntersection
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (t : unitInterval) :
    ((D.verticalSwitchEdgeInIntersection i j l hshared hswitch t : ↥(U ∩ V)) : X) =
      squareGridHorizontalEdge H D.steps D.steps_pos i j.succ t := rfl

/-- 在覆盖交集中，从公共基点连接到任意给定交集点。-/
def binaryOpenCoverIntersectionConnector
    {x₀ : X} {U V : Set X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (z : ↥(U ∩ V)) :
    Path (binaryOpenCoverIntersectionBasepoint hxU hxV) z := by
  classical
  exact if hz : z = binaryOpenCoverIntersectionBasepoint hxU hxV then
      (Path.refl (binaryOpenCoverIntersectionBasepoint hxU hxV)).cast rfl hz
    else by
      let q := (hUV.joinedIn x₀ ⟨hxU, hxV⟩ z.1 z.2).somePath
      exact pathCodRestrict (U ∩ V) q ⟨hxU, hxV⟩ z.2
        (hUV.joinedIn x₀ ⟨hxU, hxV⟩ z.1 z.2).somePath_mem

/--
@isnad1 id=eq.3h4v.s7.cc6feee9f2f9 from=translated src=- shape=bc13983e vocab=7077ef03
-/
@[simp] theorem binaryOpenCoverIntersectionConnector_basepoint
    {x₀ : X} {U V : Set X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V)) :
    binaryOpenCoverIntersectionConnector hxU hxV hUV
        (binaryOpenCoverIntersectionBasepoint hxU hxV) =
      Path.refl (binaryOpenCoverIntersectionBasepoint hxU hxV) := by
  classical
  simp [binaryOpenCoverIntersectionConnector]

/-- 将交集中的道路映入指定覆盖成员。-/
def binaryOpenCoverIntersectionPathToPiece
    {U V : Set X} (b : Bool) {z w : ↥(U ∩ V)} (p : Path z w) :
    Path (binaryOpenCoverIntersectionToPiece U V b z)
      (binaryOpenCoverIntersectionToPiece U V b w) :=
  p.map (binaryOpenCoverIntersectionToPiece U V b).continuous

/--
@isnad1 id=eq.0h8v.s9.43948127afa5 from=translated src=- shape=3098076a vocab=84891495
-/
@[simp] theorem coe_binaryOpenCoverIntersectionPathToPiece
    {U V : Set X} (b : Bool) {z w : ↥(U ∩ V)} (p : Path z w)
    (t : unitInterval) :
    ((binaryOpenCoverIntersectionPathToPiece b p t :
      binaryOpenCoverPiece U V b) : X) = p t := by
  cases b <;> rfl

/-- 将交集公共基点连接映入指定覆盖成员。-/
def binaryOpenCoverIntersectionConnectorInPiece
    {x₀ : X} {U V : Set X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (b : Bool) (z : ↥(U ∩ V)) :
    Path
      (binaryOpenCoverIntersectionToPiece U V b
        (binaryOpenCoverIntersectionBasepoint hxU hxV))
      (binaryOpenCoverIntersectionToPiece U V b z) :=
  binaryOpenCoverIntersectionPathToPiece b
    (binaryOpenCoverIntersectionConnector hxU hxV hUV z)

/--
@isnad1 id=eq.3h7v.s9.6eb729dbcb7d from=translated src=- shape=8e3bb18b vocab=61e5a3c0
-/
@[simp] theorem coe_binaryOpenCoverIntersectionConnectorInPiece
    {x₀ : X} {U V : Set X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (b : Bool) (z : ↥(U ∩ V)) (t : unitInterval) :
    ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z t :
      binaryOpenCoverPiece U V b) : X) =
      binaryOpenCoverIntersectionConnector hxU hxV hUV z t := by
  exact coe_binaryOpenCoverIntersectionPathToPiece b _ t

/--
@isnad1 id=eq.2h5v.s7.a45f68f62e66 from=translated src=- shape=34955f71 vocab=855cf3a8
-/
theorem binaryOpenCoverBasepoint_eq_intersectionToPiece
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (b : Bool) :
    binaryOpenCoverBasepoint hxU hxV b =
      binaryOpenCoverIntersectionToPiece U V b
        (binaryOpenCoverIntersectionBasepoint hxU hxV) := by
  cases b <;> rfl

/-- The normalized intersection connector at the distinguished basepoint maps
to the constant connector in either cover member.
@isnad1 id=eq.3h5v.s8.7bfa07463e84 from=translated src=- shape=24bff487 vocab=ebb73381
-/
theorem binaryOpenCoverIntersectionConnectorInPiece_basepoint
    {x₀ : X} {U V : Set X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (b : Bool) :
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b
      (binaryOpenCoverIntersectionBasepoint hxU hxV)).cast
        (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b)
        (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b) =
      Path.refl (binaryOpenCoverBasepoint hxU hxV b) := by
  apply Path.ext
  funext u
  apply Subtype.ext
  rw [Path.cast_coe]
  simp only [coe_binaryOpenCoverIntersectionConnectorInPiece,
    binaryOpenCoverIntersectionConnector_basepoint, Path.refl_apply]
  cases b <;> rfl

/--
@isnad1 id=eq.0h5v.s7.dbb8d5bf2c12 from=translated src=- shape=874427b7 vocab=cbbf00f6
-/
@[simp] theorem coe_binaryOpenCoverIntersectionToPiece
    {U V : Set X} (b : Bool) (z : ↥(U ∩ V)) :
    ((binaryOpenCoverIntersectionToPiece U V b z :
      binaryOpenCoverPiece U V b) : X) = z := by
  cases b <;> rfl

/-- 水平异标签公共边从交集映入指定覆盖成员。-/
def BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (b : Bool) :=
  binaryOpenCoverIntersectionPathToPiece b
    (D.horizontalSwitchEdgeInIntersection i k j hshared hswitch)

/-- 竖直异标签公共边从交集映入指定覆盖成员。-/
def BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (b : Bool) :=
  binaryOpenCoverIntersectionPathToPiece b
    (D.verticalSwitchEdgeInIntersection i j l hshared hswitch)

/--
@isnad1 id=eq.2h10v.s10.e453bfca3a09 from=translated src=- shape=5ad8a345 vocab=dcf0a051
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_horizontalSwitchEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (b : Bool) (t : unitInterval) :
    ((D.horizontalSwitchEdgeInPiece i k j hshared hswitch b t :
      binaryOpenCoverPiece U V b) : X) =
      squareGridVerticalEdge H D.steps D.steps_pos i.succ j t := by
  rw [BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeInPiece,
    coe_binaryOpenCoverIntersectionPathToPiece,
    D.coe_horizontalSwitchEdgeInIntersection]

/--
@isnad1 id=eq.2h10v.s10.8a4bb03ad0f1 from=translated src=- shape=20f891ab vocab=206e6fc6
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_verticalSwitchEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (b : Bool) (t : unitInterval) :
    ((D.verticalSwitchEdgeInPiece i j l hshared hswitch b t :
      binaryOpenCoverPiece U V b) : X) =
      squareGridHorizontalEdge H D.steps D.steps_pos i j.succ t := by
  rw [BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeInPiece,
    coe_binaryOpenCoverIntersectionPathToPiece,
    D.coe_verticalSwitchEdgeInIntersection]

/-- 任意交集基本群元素经两个覆盖成员送入二元推送后相等。
@isnad1 id=eq.2h5v.s12.a4331dbcf229 from=translated src=- shape=316166ca vocab=4dddc1f2
-/
theorem binaryVanKampenPushout_of_intersection_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (g : FundamentalGroup (↥(U ∩ V))
      (binaryOpenCoverIntersectionBasepoint hxU hxV)) :
    (Monoid.PushoutI.of false
        (binaryOpenCoverIntersectionMaps U V hxU hxV false g) :
      binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of true
        (binaryOpenCoverIntersectionMaps U V hxU hxV true g) :
      binaryVanKampenPushout U V hxU hxV) := by
  rw [Monoid.PushoutI.of_apply_eq_base, Monoid.PushoutI.of_apply_eq_base]

/-- 水平异标签公共边在交集公共基点处确定的基本群元素。-/
def BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeIntersectionElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    FundamentalGroup (↥(U ∩ V)) (binaryOpenCoverIntersectionBasepoint hxU hxV) :=
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (binaryOpenCoverIntersectionConnector hxU hxV hUV z)
    (D.horizontalSwitchEdgeInIntersection i k j hshared hswitch)
    (binaryOpenCoverIntersectionConnector hxU hxV hUV w)⟧

/-- 竖直异标签公共边在交集公共基点处确定的基本群元素。-/
def BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeIntersectionElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    FundamentalGroup (↥(U ∩ V)) (binaryOpenCoverIntersectionBasepoint hxU hxV) :=
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (binaryOpenCoverIntersectionConnector hxU hxV hUV z)
    (D.verticalSwitchEdgeInIntersection i j l hshared hswitch)
    (binaryOpenCoverIntersectionConnector hxU hxV hUV w)⟧

/-- 水平异标签公共边的交集元素从两侧进入推送所得元素相等。
@isnad1 id=other.5h9v.s12.204a9a5d1cb2 from=translated src=- shape=01c99bfb vocab=68a92f6a
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_pushout_images_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let g := D.horizontalSwitchEdgeIntersectionElement hxU hxV hUV
      i k j hshared hswitch
    (Monoid.PushoutI.of false
        (binaryOpenCoverIntersectionMaps U V hxU hxV false g) :
      binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of true
        (binaryOpenCoverIntersectionMaps U V hxU hxV true g) :
      binaryVanKampenPushout U V hxU hxV) := by
  exact binaryVanKampenPushout_of_intersection_eq hxU hxV _

/-- 竖直异标签公共边的交集元素从两侧进入推送所得元素相等。
@isnad1 id=other.5h9v.s12.93bfd5f562be from=translated src=- shape=3954d239 vocab=3d8afa42
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_pushout_images_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let g := D.verticalSwitchEdgeIntersectionElement hxU hxV hUV
      i j l hshared hswitch
    (Monoid.PushoutI.of false
        (binaryOpenCoverIntersectionMaps U V hxU hxV false g) :
      binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of true
        (binaryOpenCoverIntersectionMaps U V hxU hxV true g) :
      binaryVanKampenPushout U V hxU hxV) := by
  exact binaryVanKampenPushout_of_intersection_eq hxU hxV _

/-- 基本群映射把修正环路类送到逐条映射后的修正环路类。
@isnad1 id=eq.0h9v.s9.818931c8c2cd from=translated src=- shape=d8136baa vocab=0064f53e
-/
theorem fundamentalGroup_map_correctedLoop
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (f : C(S, T)) {base z w : S}
    (left : Path base z) (segment : Path z w) (right : Path base w) :
    FundamentalGroup.map f base
        (FundamentalGroup.fromPath ⟦Path.correctedLoop left segment right⟧) =
      FundamentalGroup.fromPath ⟦Path.correctedLoop
        (left.map f.continuous) (segment.map f.continuous) (right.map f.continuous)⟧ := by
  change Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk (Path.correctedLoop left segment right)) f =
    Path.Homotopic.Quotient.mk (Path.correctedLoop
      (left.map f.continuous) (segment.map f.continuous) (right.map f.continuous))
  rw [← Path.Homotopic.Quotient.mk_map]
  congr 1
  unfold Path.correctedLoop
  simp only [Path.map_trans, Path.map_symm]

/-- 水平切换边的交集连接与道路整体映入指定覆盖成员所得元素。-/
def BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgePieceImage
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (b : Bool) :
    FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) := by
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩
  cases b
  · let f := binaryOpenCoverIntersectionToPiece U V false
    exact FundamentalGroup.fromPath ⟦Path.correctedLoop
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV z).map f.continuous)
      ((D.horizontalSwitchEdgeInIntersection i k j hshared hswitch).map f.continuous)
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV w).map f.continuous)⟧
  · let f := binaryOpenCoverIntersectionToPiece U V true
    exact FundamentalGroup.fromPath ⟦Path.correctedLoop
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV z).map f.continuous)
      ((D.horizontalSwitchEdgeInIntersection i k j hshared hswitch).map f.continuous)
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV w).map f.continuous)⟧

/-- 水平切换边的显式覆盖成员像就是 `binaryOpenCoverIntersectionMaps` 的值。
@isnad1 id=eq.5h10v.s10.83c416d68a1e from=translated src=- shape=0471a906 vocab=2604427d
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgePieceImage_eq_map
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (b : Bool) :
    D.horizontalSwitchEdgePieceImage hxU hxV hUV i k j hshared hswitch b =
      binaryOpenCoverIntersectionMaps U V hxU hxV b
        (D.horizontalSwitchEdgeIntersectionElement hxU hxV hUV
          i k j hshared hswitch) := by
  cases b <;>
    unfold BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgePieceImage
      BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeIntersectionElement
      binaryOpenCoverIntersectionMaps <;>
    symm <;>
    exact fundamentalGroup_map_correctedLoop _ _ _ _

/-- 竖直切换边的交集连接与道路整体映入指定覆盖成员所得元素。-/
def BinaryOpenCoverSquareSubdivision.verticalSwitchEdgePieceImage
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (b : Bool) :
    FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) := by
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩
  cases b
  · let f := binaryOpenCoverIntersectionToPiece U V false
    exact FundamentalGroup.fromPath ⟦Path.correctedLoop
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV z).map f.continuous)
      ((D.verticalSwitchEdgeInIntersection i j l hshared hswitch).map f.continuous)
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV w).map f.continuous)⟧
  · let f := binaryOpenCoverIntersectionToPiece U V true
    exact FundamentalGroup.fromPath ⟦Path.correctedLoop
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV z).map f.continuous)
      ((D.verticalSwitchEdgeInIntersection i j l hshared hswitch).map f.continuous)
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV w).map f.continuous)⟧

/-- 竖直切换边的显式覆盖成员像就是 `binaryOpenCoverIntersectionMaps` 的值。
@isnad1 id=eq.5h10v.s10.80b30dcb3df3 from=translated src=- shape=1a783b62 vocab=66073940
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdgePieceImage_eq_map
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (b : Bool) :
    D.verticalSwitchEdgePieceImage hxU hxV hUV i j l hshared hswitch b =
      binaryOpenCoverIntersectionMaps U V hxU hxV b
        (D.verticalSwitchEdgeIntersectionElement hxU hxV hUV
          i j l hshared hswitch) := by
  cases b <;>
    unfold BinaryOpenCoverSquareSubdivision.verticalSwitchEdgePieceImage
      BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeIntersectionElement
      binaryOpenCoverIntersectionMaps <;>
    symm <;>
    exact fundamentalGroup_map_correctedLoop _ _ _ _

/-- 水平异标签公共边的两个显式覆盖成员像进入推送后相等。
@isnad1 id=eq.5h9v.s12.30faa75172e8 from=translated src=- shape=1ef5079f vocab=7e922ee3
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_pieceImages_pushout_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    (Monoid.PushoutI.of false
        (D.horizontalSwitchEdgePieceImage hxU hxV hUV
          i k j hshared hswitch false) : binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of true
        (D.horizontalSwitchEdgePieceImage hxU hxV hUV
          i k j hshared hswitch true) : binaryVanKampenPushout U V hxU hxV) := by
  rw [D.horizontalSwitchEdgePieceImage_eq_map hxU hxV hUV
      i k j hshared hswitch false,
    D.horizontalSwitchEdgePieceImage_eq_map hxU hxV hUV
      i k j hshared hswitch true]
  exact D.horizontalSwitchEdge_pushout_images_eq hxU hxV hUV
    i k j hshared hswitch

/-- 竖直异标签公共边的两个显式覆盖成员像进入推送后相等。
@isnad1 id=eq.5h9v.s12.4f061efcbb5c from=translated src=- shape=f1fafeaa vocab=f4b80ace
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_pieceImages_pushout_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    (Monoid.PushoutI.of false
        (D.verticalSwitchEdgePieceImage hxU hxV hUV
          i j l hshared hswitch false) : binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of true
        (D.verticalSwitchEdgePieceImage hxU hxV hUV
          i j l hshared hswitch true) : binaryVanKampenPushout U V hxU hxV) := by
  rw [D.verticalSwitchEdgePieceImage_eq_map hxU hxV hUV
      i j l hshared hswitch false,
    D.verticalSwitchEdgePieceImage_eq_map hxU hxV hUV
      i j l hshared hswitch true]
  exact D.verticalSwitchEdge_pushout_images_eq hxU hxV hUV
    i j l hshared hswitch

/-- 水平异标签交集边起点映入左格标签成员后等于左格右下角。
@isnad1 id=eq.2h8v.s8.43e987e341e2 from=translated src=- shape=570e5493 vocab=17346914
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_left_source_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    binaryOpenCoverIntersectionToPiece U V (D.label i j)
        (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
          simpa [squareGridVertex, Set.Icc.convexComb_zero]
            using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel i j 1 0 (D.label i j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 水平异标签交集边终点映入左格标签成员后等于左格右上角。
@isnad1 id=eq.2h8v.s8.12c7876161bf from=translated src=- shape=7454ffa5 vocab=75d2b420
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_left_target_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    binaryOpenCoverIntersectionToPiece U V (D.label i j)
        (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_one]
            using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel i j 1 1 (D.label i j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 水平异标签公共边在左格标签成员中，比较交集连接与左格角连接。-/
def BinaryOpenCoverSquareSubdivision.horizontalSwitchLeftConnectorComparison
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) := by
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩
  let b := D.label i j
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b
  exact {
    edgeSource := binaryOpenCoverIntersectionToPiece U V b z
    edgeTarget := binaryOpenCoverIntersectionToPiece U V b w
    edge := D.horizontalSwitchEdgeInPiece i k j hshared hswitch b
    leftStart :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z).cast hb rfl
    leftEnd :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b w).cast hb rfl
    rightStart :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        i j 1 0 b rfl).cast rfl
          (D.horizontalSwitchEdge_left_source_eq i k j hshared hswitch)
    rightEnd :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        i j 1 1 b rfl).cast rfl
          (D.horizontalSwitchEdge_left_target_eq i k j hshared hswitch) }

/-- 水平异标签左格中，交集连接版本与单格连接版本满足换连接关系。
@isnad1 id=other.7h9v.s10.2463005c3258 from=translated src=- shape=4a20dc8a vocab=d95f42e9
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeftConnectorComparison_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    C.endChange⁻¹ * C.leftElement * C.startChange = C.rightElement := by
  exact CommonEdgeConnectorComparison.rightElement_eq _

/-- 水平异标签交集边起点映入右格标签成员后等于右格左下角。
@isnad1 id=eq.2h8v.s8.3324686b7299 from=translated src=- shape=fc68551a vocab=17346914
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_right_source_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    binaryOpenCoverIntersectionToPiece U V (D.label k j)
        (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
          simpa [squareGridVertex, Set.Icc.convexComb_zero]
            using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel k j 0 0 (D.label k j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared]

/-- 水平异标签交集边终点映入右格标签成员后等于右格左上角。
@isnad1 id=eq.2h8v.s8.16965e4f17d7 from=translated src=- shape=f900ddf9 vocab=75d2b420
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_right_target_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    binaryOpenCoverIntersectionToPiece U V (D.label k j)
        (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_one]
            using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel k j 0 1 (D.label k j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared, hone]

/-- 水平异标签公共边在右格标签成员中，比较交集连接与右格角连接。-/
def BinaryOpenCoverSquareSubdivision.horizontalSwitchRightConnectorComparison
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V (D.label k j))
      (binaryOpenCoverBasepoint hxU hxV (D.label k j)) := by
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩
  let b := D.label k j
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b
  exact {
    edgeSource := binaryOpenCoverIntersectionToPiece U V b z
    edgeTarget := binaryOpenCoverIntersectionToPiece U V b w
    edge := D.horizontalSwitchEdgeInPiece i k j hshared hswitch b
    leftStart :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z).cast hb rfl
    leftEnd :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b w).cast hb rfl
    rightStart :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        k j 0 0 b rfl).cast rfl
          (D.horizontalSwitchEdge_right_source_eq i k j hshared hswitch)
    rightEnd :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        k j 0 1 b rfl).cast rfl
          (D.horizontalSwitchEdge_right_target_eq i k j hshared hswitch) }

/-- 水平异标签右格中，交集连接版本与单格连接版本满足换连接关系。
@isnad1 id=other.7h9v.s10.52a66783e366 from=translated src=- shape=9b2f6fe8 vocab=d3d108b6
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRightConnectorComparison_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    C.endChange⁻¹ * C.leftElement * C.startChange = C.rightElement := by
  exact CommonEdgeConnectorComparison.rightElement_eq _

/-- 用统一基点 cast 表示水平切换边在任一覆盖成员中的显式像。-/
def BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgePieceImageNormalized
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (b : Bool) :
    FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) :=
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z).cast hb rfl)
    (D.horizontalSwitchEdgeInPiece i k j hshared hswitch b)
    ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b w).cast hb rfl)⟧

/-- 左侧比较对象的交集连接元素就是统一基点表示的左覆盖成员像。
@isnad1 id=eq.7h9v.s8.ea409394b1c5 from=translated src=- shape=00198635 vocab=dce8c98e
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeftComparison_leftElement_normalized
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    (D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch).leftElement =
      D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
        i k j hshared hswitch (D.label i j) := by
  rfl

/-- 右侧比较对象的交集连接元素就是统一基点表示的右覆盖成员像。
@isnad1 id=eq.7h9v.s8.f66a3e420dde from=translated src=- shape=6e3bedfb vocab=3047dd10
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRightComparison_leftElement_normalized
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    (D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch).leftElement =
      D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
        i k j hshared hswitch (D.label k j) := by
  rfl

/-- 统一基点表示与按 Bool 分支定义的显式覆盖成员像一致。
@isnad1 id=eq.5h10v.s8.86344411258b from=translated src=- shape=b4b76e08 vocab=959b3e7e
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgePieceImageNormalized_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (b : Bool) :
    D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
        i k j hshared hswitch b =
      D.horizontalSwitchEdgePieceImage hxU hxV hUV
        i k j hshared hswitch b := by
  cases b <;> rfl

/-- 水平异标签公共边在左格成员中的像等于左格局部右竖边经端点 transport。
@isnad1 id=eq.2h8v.s11.7277a0837a2f from=translated src=- shape=859113c1 vocab=f108c50a
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeInLeftPiece_eq_cellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    D.horizontalSwitchEdgeInPiece i k j hshared hswitch (D.label i j) =
      (((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece i j).continuous).cast
          (D.horizontalSwitchEdge_left_source_eq i k j hshared hswitch)
          (D.horizontalSwitchEdge_left_target_eq i k j hshared hswitch)) := by
  let q := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece i j).continuous
  let hs := D.horizontalSwitchEdge_left_source_eq i k j hshared hswitch
  let ht := D.horizontalSwitchEdge_left_target_eq i k j hshared hswitch
  apply Path.ext
  calc
    (D.horizontalSwitchEdgeInPiece i k j hshared hswitch (D.label i j) :
        unitInterval → binaryOpenCoverPiece U V (D.label i j)) =
        (q : unitInterval → binaryOpenCoverPiece U V (D.label i j)) := by
      funext t
      apply Subtype.ext
      have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
        simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
      have hqt : q t = D.gridCellMapInPiece i j
          (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
            1 unitSquareOnePos 1 0 t) := by
        rfl
      rw [D.coe_horizontalSwitchEdgeInPiece]
      rw [hqt]
      simp [squareGridVerticalEdge,
        BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
        unitSquareCellPoint, hone]
      rfl
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
      (Path.cast_coe q hs ht).symm

/-- 左侧比较对象的单格连接元素就是左格原四边词中的右竖边。
@isnad1 id=eq.7h9v.s8.e66ab0db5c50 from=translated src=- shape=2f171545 vocab=acf089b0
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeftComparison_rightElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    (D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch).rightElement =
      D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1 := by
  let l := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 1 0 (D.label i j) rfl
  let q := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece i j).continuous
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 1 1 (D.label i j) rfl
  let hs := D.horizontalSwitchEdge_left_source_eq i k j hshared hswitch
  let ht := D.horizontalSwitchEdge_left_target_eq i k j hshared hswitch
  have hp : Path.correctedLoop (l.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop l q r := correctedLoop_cast l q r hs ht
  unfold CommonEdgeConnectorComparison.rightElement
    BinaryOpenCoverSquareSubdivision.horizontalSwitchLeftConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPiece
  dsimp only [CommonEdgeConnectorComparison.rightStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.rightEnd]
  rw [D.horizontalSwitchEdgeInLeftPiece_eq_cellEdge i k j hshared hswitch]
  exact congrArg Path.Homotopic.Quotient.mk hp

/-- 水平异标签左格真实边由交集公共边像经端点换连接得到。
@isnad1 id=other.7h9v.s10.96f55d4b5b54 from=translated src=- shape=72a56aa2 vocab=65dc97f6
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeft_pieceElement_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    C.endChange⁻¹ *
        D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
          i k j hshared hswitch (D.label i j) *
        C.startChange =
      D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1 := by
  dsimp only
  rw [← D.horizontalSwitchLeftComparison_leftElement_normalized
    hxU hxV hUV hU hV i k j hshared hswitch]
  rw [D.horizontalSwitchLeftConnectorComparison_relation
    hxU hxV hUV hU hV i k j hshared hswitch]
  exact D.horizontalSwitchLeftComparison_rightElement
    hxU hxV hUV hU hV i k j hshared hswitch

/-- 水平异标签公共边在右格成员中的像等于右格局部左竖边经端点 transport。
@isnad1 id=eq.2h8v.s11.7683bd5b85ba from=translated src=- shape=7f0f30ca vocab=e50ed34d
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeInRightPiece_eq_cellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    D.horizontalSwitchEdgeInPiece i k j hshared hswitch (D.label k j) =
      (((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece k j).continuous).cast
          (D.horizontalSwitchEdge_right_source_eq i k j hshared hswitch)
          (D.horizontalSwitchEdge_right_target_eq i k j hshared hswitch)) := by
  let q := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece k j).continuous
  let hs := D.horizontalSwitchEdge_right_source_eq i k j hshared hswitch
  let ht := D.horizontalSwitchEdge_right_target_eq i k j hshared hswitch
  apply Path.ext
  calc
    (D.horizontalSwitchEdgeInPiece i k j hshared hswitch (D.label k j) :
        unitInterval → binaryOpenCoverPiece U V (D.label k j)) =
        (q : unitInterval → binaryOpenCoverPiece U V (D.label k j)) := by
      funext t
      apply Subtype.ext
      have hqt : q t = D.gridCellMapInPiece k j
          (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
            1 unitSquareOnePos 0 0 t) := by
        rfl
      have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
        simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
      rw [D.coe_horizontalSwitchEdgeInPiece]
      rw [hqt]
      simp [squareGridVerticalEdge,
        BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
        unitSquareCellPoint, hshared, hone]
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label k j)) :=
      (Path.cast_coe q hs ht).symm

/-- 右侧比较对象的单格连接元素就是右格原四边词中的左竖边。
@isnad1 id=eq.7h9v.s8.903c0df77987 from=translated src=- shape=3e81e9b4 vocab=a0508aad
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRightComparison_rightElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    (D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch).rightElement =
      D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0 := by
  let l := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    k j 0 0 (D.label k j) rfl
  let q := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece k j).continuous
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    k j 0 1 (D.label k j) rfl
  let hs := D.horizontalSwitchEdge_right_source_eq i k j hshared hswitch
  let ht := D.horizontalSwitchEdge_right_target_eq i k j hshared hswitch
  have hp : Path.correctedLoop (l.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop l q r := correctedLoop_cast l q r hs ht
  unfold CommonEdgeConnectorComparison.rightElement
    BinaryOpenCoverSquareSubdivision.horizontalSwitchRightConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPiece
  dsimp only [CommonEdgeConnectorComparison.rightStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.rightEnd]
  rw [D.horizontalSwitchEdgeInRightPiece_eq_cellEdge i k j hshared hswitch]
  exact congrArg Path.Homotopic.Quotient.mk hp

/-- 水平异标签右格真实边由交集公共边像经端点换连接得到。
@isnad1 id=other.7h9v.s10.44a41f8505f9 from=translated src=- shape=2fb4b1f1 vocab=759aa150
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRight_pieceElement_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    C.endChange⁻¹ *
        D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
          i k j hshared hswitch (D.label k j) *
        C.startChange =
      D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0 := by
  dsimp only
  rw [← D.horizontalSwitchRightComparison_leftElement_normalized
    hxU hxV hUV hU hV i k j hshared hswitch]
  rw [D.horizontalSwitchRightConnectorComparison_relation
    hxU hxV hUV hU hV i k j hshared hswitch]
  exact D.horizontalSwitchRightComparison_rightElement
    hxU hxV hUV hU hV i k j hshared hswitch

/-- 水平异标签公共边的 normalized 两侧像按两格实际标签进入推送后相等。
@isnad1 id=eq.5h9v.s12.8438d36c24f5 from=translated src=- shape=de3f907b vocab=6aed3f7c
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_normalized_pushout_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    (Monoid.PushoutI.of (D.label i j)
        (D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
          i k j hshared hswitch (D.label i j)) :
      binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of (D.label k j)
        (D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
          i k j hshared hswitch (D.label k j)) :
      binaryVanKampenPushout U V hxU hxV) := by
  cases hli : D.label i j <;> cases hlk : D.label k j
  · exact False.elim (hswitch (hli.trans hlk.symm))
  · rw [D.horizontalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i k j hshared hswitch false,
      D.horizontalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i k j hshared hswitch true]
    exact D.horizontalSwitchEdge_pieceImages_pushout_eq hxU hxV hUV
      i k j hshared hswitch
  · rw [D.horizontalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i k j hshared hswitch true,
      D.horizontalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i k j hshared hswitch false]
    exact (D.horizontalSwitchEdge_pieceImages_pushout_eq hxU hxV hUV
      i k j hshared hswitch).symm
  · exact False.elim (hswitch (hli.trans hlk.symm))

/-- 两套换连接关系及公共边相等，推出两侧单格边元素的精确非交换关系。
@isnad1 id=eq.3h9v.s7.261760409e3e from=translated src=- shape=f718242a vocab=9f72dee7
-/
theorem edgeElements_eq_of_change_relations
    {G : Type*} [Group G] (endL startL commonL cellL : G)
    (endR startR commonR cellR : G)
    (hL : endL⁻¹ * commonL * startL = cellL)
    (hR : endR⁻¹ * commonR * startR = cellR)
    (hcommon : commonL = commonR) :
    cellL = endL⁻¹ * (endR * cellR * startR⁻¹) * startL := by
  have hsolve : commonR = endR * cellR * startR⁻¹ := by
    calc
      commonR = endR * (endR⁻¹ * commonR * startR) * startR⁻¹ := by
        simp [mul_assoc]
      _ = endR * cellR * startR⁻¹ := by rw [hR]
  calc
    cellL = endL⁻¹ * commonL * startL := hL.symm
    _ = endL⁻¹ * commonR * startL := by rw [hcommon]
    _ = endL⁻¹ * (endR * cellR * startR⁻¹) * startL := by rw [hsolve]

/-- 水平异标签内部边在推送中的最终换连接关系。
@isnad1 id=other.7h9v.s14.bcd6897052cd from=translated src=- shape=275067c2 vocab=54daae3b
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_pushout_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let CL := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    let CR := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of (D.label i j) CL.endChange)⁻¹ *
        ((Monoid.PushoutI.of (D.label k j) CR.endChange) *
          (Monoid.PushoutI.of (D.label k j)
            (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0)) *
          (Monoid.PushoutI.of (D.label k j) CR.startChange)⁻¹) *
        Monoid.PushoutI.of (D.label i j) CL.startChange := by
  dsimp only
  let CL := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
    i k j hshared hswitch
  let CR := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
    i k j hshared hswitch
  let fL := (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
        (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  let fR := (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label k j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label k j))
        (binaryOpenCoverBasepoint hxU hxV (D.label k j)) →*
      binaryVanKampenPushout U V hxU hxV)
  have hL := congrArg fL
    (D.horizontalSwitchLeft_pieceElement_relation hxU hxV hUV hU hV
      i k j hshared hswitch)
  have hR := congrArg fR
    (D.horizontalSwitchRight_pieceElement_relation hxU hxV hUV hU hV
      i k j hshared hswitch)
  simp only [map_mul, map_inv] at hL hR
  have hcommon := D.horizontalSwitchEdge_normalized_pushout_eq hxU hxV hUV
    i k j hshared hswitch
  exact edgeElements_eq_of_change_relations
    (fL CL.endChange) (fL CL.startChange)
    (fL (D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
      i k j hshared hswitch (D.label i j)))
    (fL (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1))
    (fR CR.endChange) (fR CR.startChange)
    (fR (D.horizontalSwitchEdgePieceImageNormalized hxU hxV hUV
      i k j hshared hswitch (D.label k j)))
    (fR (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0))
    hL hR hcommon

/-- 竖直异标签交集边起点映入下格标签成员后等于下格左上角。
@isnad1 id=eq.2h8v.s8.bd0712eefb5b from=translated src=- shape=4e20efc6 vocab=5f28be29
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_bottom_source_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    binaryOpenCoverIntersectionToPiece U V (D.label i j)
        (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_zero]
            using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel i j 0 1 (D.label i j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 竖直异标签交集边终点映入下格标签成员后等于下格右上角。
@isnad1 id=eq.2h8v.s8.30ba8fa43337 from=translated src=- shape=082718a7 vocab=eaf62a60
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_bottom_target_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    binaryOpenCoverIntersectionToPiece U V (D.label i j)
        (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_one]
            using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel i j 1 1 (D.label i j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 竖直异标签交集边起点映入上格标签成员后等于上格左下角。
@isnad1 id=eq.2h8v.s8.cdc23e5f64d3 from=translated src=- shape=99da96d7 vocab=5f28be29
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_top_source_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    binaryOpenCoverIntersectionToPiece U V (D.label i l)
        (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_zero]
            using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel i l 0 0 (D.label i l) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared]

/-- 竖直异标签交集边终点映入上格标签成员后等于上格右下角。
@isnad1 id=eq.2h8v.s8.64b706ee525a from=translated src=- shape=c53d9e72 vocab=eaf62a60
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_top_target_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    binaryOpenCoverIntersectionToPiece U V (D.label i l)
        (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_one]
            using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩ :
          ↥(U ∩ V)) =
      D.gridCellVertexInPieceOfLabel i l 1 0 (D.label i l) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared, hone]

/-- 竖直异标签公共边在下格标签成员中，比较交集连接与下格角连接。-/
def BinaryOpenCoverSquareSubdivision.verticalSwitchBottomConnectorComparison
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) := by
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩
  let b := D.label i j
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b
  exact {
    edgeSource := binaryOpenCoverIntersectionToPiece U V b z
    edgeTarget := binaryOpenCoverIntersectionToPiece U V b w
    edge := D.verticalSwitchEdgeInPiece i j l hshared hswitch b
    leftStart :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z).cast hb rfl
    leftEnd :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b w).cast hb rfl
    rightStart :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        i j 0 1 b rfl).cast rfl
          (D.verticalSwitchEdge_bottom_source_eq i j l hshared hswitch)
    rightEnd :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        i j 1 1 b rfl).cast rfl
          (D.verticalSwitchEdge_bottom_target_eq i j l hshared hswitch) }

/--
@isnad1 id=other.7h9v.s10.166be31c662b from=translated src=- shape=29a42372 vocab=e160c2ca
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottomConnectorComparison_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    C.endChange⁻¹ * C.leftElement * C.startChange = C.rightElement := by
  exact CommonEdgeConnectorComparison.rightElement_eq _

/-- 竖直异标签公共边在上格标签成员中，比较交集连接与上格角连接。-/
def BinaryOpenCoverSquareSubdivision.verticalSwitchTopConnectorComparison
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V (D.label i l))
      (binaryOpenCoverBasepoint hxU hxV (D.label i l)) := by
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩
  let b := D.label i l
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b
  exact {
    edgeSource := binaryOpenCoverIntersectionToPiece U V b z
    edgeTarget := binaryOpenCoverIntersectionToPiece U V b w
    edge := D.verticalSwitchEdgeInPiece i j l hshared hswitch b
    leftStart :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z).cast hb rfl
    leftEnd :=
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b w).cast hb rfl
    rightStart :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        i l 0 0 b rfl).cast rfl
          (D.verticalSwitchEdge_top_source_eq i j l hshared hswitch)
    rightEnd :=
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        i l 1 0 b rfl).cast rfl
          (D.verticalSwitchEdge_top_target_eq i j l hshared hswitch) }

/--
@isnad1 id=other.7h9v.s10.c30a9a5c678f from=translated src=- shape=f7b94db9 vocab=9e3f386c
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTopConnectorComparison_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    C.endChange⁻¹ * C.leftElement * C.startChange = C.rightElement := by
  exact CommonEdgeConnectorComparison.rightElement_eq _

/-- 用统一基点 cast 表示竖直切换边在任一覆盖成员中的显式像。-/
def BinaryOpenCoverSquareSubdivision.verticalSwitchEdgePieceImageNormalized
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (b : Bool) :
    FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) := by
  let z : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_zero]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩
  let w : ↥(U ∩ V) :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b
  exact FundamentalGroup.fromPath ⟦Path.correctedLoop
    ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z).cast hb rfl)
    (D.verticalSwitchEdgeInPiece i j l hshared hswitch b)
    ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b w).cast hb rfl)⟧

/--
@isnad1 id=eq.7h9v.s8.1ca68f9aa134 from=translated src=- shape=7813451f vocab=9f63ef6d
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottomComparison_leftElement_normalized
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    (D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch).leftElement =
      D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
        i j l hshared hswitch (D.label i j) := by
  rfl

/--
@isnad1 id=eq.7h9v.s8.9b16dc83e0e9 from=translated src=- shape=a77627c5 vocab=6e116f08
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTopComparison_leftElement_normalized
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    (D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch).leftElement =
      D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
        i j l hshared hswitch (D.label i l) := by
  rfl

/--
@isnad1 id=eq.5h10v.s8.7c635315c4f0 from=translated src=- shape=3096af66 vocab=9e9f0b3a
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdgePieceImageNormalized_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (b : Bool) :
    D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
        i j l hshared hswitch b =
      D.verticalSwitchEdgePieceImage hxU hxV hUV
        i j l hshared hswitch b := by
  cases b <;> rfl

/-- 竖直异标签公共边在下格成员中的像等于下格局部上横边经端点 transport。
@isnad1 id=eq.2h8v.s11.5178be23c449 from=translated src=- shape=1db2826e vocab=be0a8e1b
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeInBottomPiece_eq_cellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    D.verticalSwitchEdgeInPiece i j l hshared hswitch (D.label i j) =
      (((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous).cast
          (D.verticalSwitchEdge_bottom_source_eq i j l hshared hswitch)
          (D.verticalSwitchEdge_bottom_target_eq i j l hshared hswitch)) := by
  let q := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous
  let hs := D.verticalSwitchEdge_bottom_source_eq i j l hshared hswitch
  let ht := D.verticalSwitchEdge_bottom_target_eq i j l hshared hswitch
  apply Path.ext
  calc
    (D.verticalSwitchEdgeInPiece i j l hshared hswitch (D.label i j) :
        unitInterval → binaryOpenCoverPiece U V (D.label i j)) =
        (q : unitInterval → binaryOpenCoverPiece U V (D.label i j)) := by
      funext t
      apply Subtype.ext
      have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
        simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
      have hqt : q t = D.gridCellMapInPiece i j
          (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
            1 unitSquareOnePos 0 1 t) := by
        rfl
      rw [D.coe_verticalSwitchEdgeInPiece]
      rw [hqt]
      simp [squareGridHorizontalEdge,
        BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
        unitSquareCellPoint, hone]
      rfl
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
      (Path.cast_coe q hs ht).symm

/--
@isnad1 id=eq.7h9v.s8.6b0211e3e9fb from=translated src=- shape=cc22b655 vocab=cc15e84d
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottomComparison_rightElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    (D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch).rightElement =
      D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1 := by
  let a := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 0 1 (D.label i j) rfl
  let q := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 1 1 (D.label i j) rfl
  let hs := D.verticalSwitchEdge_bottom_source_eq i j l hshared hswitch
  let ht := D.verticalSwitchEdge_bottom_target_eq i j l hshared hswitch
  have hp : Path.correctedLoop (a.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop a q r := correctedLoop_cast a q r hs ht
  unfold CommonEdgeConnectorComparison.rightElement
    BinaryOpenCoverSquareSubdivision.verticalSwitchBottomConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPiece
  dsimp only [CommonEdgeConnectorComparison.rightStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.rightEnd]
  rw [D.verticalSwitchEdgeInBottomPiece_eq_cellEdge i j l hshared hswitch]
  exact congrArg Path.Homotopic.Quotient.mk hp

/--
@isnad1 id=other.7h9v.s10.5eca7541646b from=translated src=- shape=b77a2d05 vocab=0647549c
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottom_pieceElement_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    C.endChange⁻¹ *
        D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
          i j l hshared hswitch (D.label i j) * C.startChange =
      D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1 := by
  dsimp only
  rw [← D.verticalSwitchBottomComparison_leftElement_normalized
    hxU hxV hUV hU hV i j l hshared hswitch]
  rw [D.verticalSwitchBottomConnectorComparison_relation
    hxU hxV hUV hU hV i j l hshared hswitch]
  exact D.verticalSwitchBottomComparison_rightElement
    hxU hxV hUV hU hV i j l hshared hswitch

/-- 竖直异标签公共边在上格成员中的像等于上格局部下横边经端点 transport。
@isnad1 id=eq.2h8v.s11.68792e149a07 from=translated src=- shape=9b2ef5fe vocab=6a7745bc
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeInTopPiece_eq_cellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    D.verticalSwitchEdgeInPiece i j l hshared hswitch (D.label i l) =
      (((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i l).continuous).cast
          (D.verticalSwitchEdge_top_source_eq i j l hshared hswitch)
          (D.verticalSwitchEdge_top_target_eq i j l hshared hswitch)) := by
  let q := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i l).continuous
  let hs := D.verticalSwitchEdge_top_source_eq i j l hshared hswitch
  let ht := D.verticalSwitchEdge_top_target_eq i j l hshared hswitch
  apply Path.ext
  calc
    (D.verticalSwitchEdgeInPiece i j l hshared hswitch (D.label i l) :
        unitInterval → binaryOpenCoverPiece U V (D.label i l)) =
        (q : unitInterval → binaryOpenCoverPiece U V (D.label i l)) := by
      funext t
      apply Subtype.ext
      have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
        simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
      have hqt : q t = D.gridCellMapInPiece i l
          (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
            1 unitSquareOnePos 0 0 t) := by
        rfl
      rw [D.coe_verticalSwitchEdgeInPiece]
      rw [hqt]
      simp [squareGridHorizontalEdge,
        BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
        unitSquareCellPoint, hshared, hone]
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i l)) :=
      (Path.cast_coe q hs ht).symm

/--
@isnad1 id=eq.7h9v.s8.fde5a68fe630 from=translated src=- shape=28f46b5e vocab=f1d59772
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTopComparison_rightElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    (D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch).rightElement =
      D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0 := by
  let a := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i l 0 0 (D.label i l) rfl
  let q := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i l).continuous
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i l 1 0 (D.label i l) rfl
  let hs := D.verticalSwitchEdge_top_source_eq i j l hshared hswitch
  let ht := D.verticalSwitchEdge_top_target_eq i j l hshared hswitch
  have hp : Path.correctedLoop (a.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop a q r := correctedLoop_cast a q r hs ht
  unfold CommonEdgeConnectorComparison.rightElement
    BinaryOpenCoverSquareSubdivision.verticalSwitchTopConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPiece
  dsimp only [CommonEdgeConnectorComparison.rightStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.rightEnd]
  rw [D.verticalSwitchEdgeInTopPiece_eq_cellEdge i j l hshared hswitch]
  exact congrArg Path.Homotopic.Quotient.mk hp

/--
@isnad1 id=other.7h9v.s10.bb5b847f1f9c from=translated src=- shape=ffffa3bd vocab=ff3464f7
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTop_pieceElement_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    C.endChange⁻¹ *
        D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
          i j l hshared hswitch (D.label i l) * C.startChange =
      D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0 := by
  dsimp only
  rw [← D.verticalSwitchTopComparison_leftElement_normalized
    hxU hxV hUV hU hV i j l hshared hswitch]
  rw [D.verticalSwitchTopConnectorComparison_relation
    hxU hxV hUV hU hV i j l hshared hswitch]
  exact D.verticalSwitchTopComparison_rightElement
    hxU hxV hUV hU hV i j l hshared hswitch

/-- 竖直异标签公共边的 normalized 两侧像按两格实际标签进入推送后相等。
@isnad1 id=eq.5h9v.s12.218d14c5eab2 from=translated src=- shape=12f2e3dd vocab=5f9fc744
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_normalized_pushout_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    (Monoid.PushoutI.of (D.label i j)
        (D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
          i j l hshared hswitch (D.label i j)) :
      binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of (D.label i l)
        (D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
          i j l hshared hswitch (D.label i l)) :
      binaryVanKampenPushout U V hxU hxV) := by
  cases hij : D.label i j <;> cases hil : D.label i l
  · exact False.elim (hswitch (hij.trans hil.symm))
  · rw [D.verticalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i j l hshared hswitch false,
      D.verticalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i j l hshared hswitch true]
    exact D.verticalSwitchEdge_pieceImages_pushout_eq hxU hxV hUV
      i j l hshared hswitch
  · rw [D.verticalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i j l hshared hswitch true,
      D.verticalSwitchEdgePieceImageNormalized_eq hxU hxV hUV
        i j l hshared hswitch false]
    exact (D.verticalSwitchEdge_pieceImages_pushout_eq hxU hxV hUV
      i j l hshared hswitch).symm
  · exact False.elim (hswitch (hij.trans hil.symm))

/-- 竖直异标签内部边在推送中的最终换连接关系。
@isnad1 id=other.7h9v.s14.9c9eb92bbaf0 from=translated src=- shape=ac100818 vocab=448e4e0a
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_pushout_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let CB := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    let CT := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      (Monoid.PushoutI.of (D.label i j) CB.endChange)⁻¹ *
        (Monoid.PushoutI.of (D.label i l) CT.endChange *
          Monoid.PushoutI.of (D.label i l)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0) *
          (Monoid.PushoutI.of (D.label i l) CT.startChange)⁻¹) *
        Monoid.PushoutI.of (D.label i j) CB.startChange := by
  dsimp only
  let CB := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
    i j l hshared hswitch
  let CT := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
    i j l hshared hswitch
  let fB := (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
      FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
        (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  let fT := (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i l) :
      FundamentalGroup (binaryOpenCoverPiece U V (D.label i l))
        (binaryOpenCoverBasepoint hxU hxV (D.label i l)) →*
      binaryVanKampenPushout U V hxU hxV)
  have hB := congrArg fB
    (D.verticalSwitchBottom_pieceElement_relation hxU hxV hUV hU hV
      i j l hshared hswitch)
  have hT := congrArg fT
    (D.verticalSwitchTop_pieceElement_relation hxU hxV hUV hU hV
      i j l hshared hswitch)
  simp only [map_mul, map_inv] at hB hT
  have hcommon := D.verticalSwitchEdge_normalized_pushout_eq hxU hxV hUV
    i j l hshared hswitch
  exact edgeElements_eq_of_change_relations
    (fB CB.endChange) (fB CB.startChange)
    (fB (D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
      i j l hshared hswitch (D.label i j)))
    (fB (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1))
    (fT CT.endChange) (fT CT.startChange)
    (fT (D.verticalSwitchEdgePieceImageNormalized hxU hxV hUV
      i j l hshared hswitch (D.label i l)))
    (fT (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0))
    hB hT hcommon

end SandronesLibrary.Topology
