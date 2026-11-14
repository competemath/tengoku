/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenDualPathPotential

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 同路局部表示的统一 gauge 比较

本文件把方格边和字母边对同一几何道路的局部表示统一写成 endpoint vertex potentials 的 rebase。
异标签情况使用交集道路，等标签情况使用共同成员 connector comparison。它不进行左边界 telescope，
也不证明 kernel、单射或最终 van Kampen 同构。

当前条目：

* `topology.fundamental-group.van-kampen-path-gauge-comparison`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 水平异标签公共边在左格下端的 comparison potential，是共享交集顶点处左格 connector 的统一
vertex potential。

> **Entry**: topology.fundamental-group.van-kampen-path-gauge-comparison-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeft_startPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchLeftConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩
    let w := C.edgeSource
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z = w := rfl
    ((Monoid.PushoutI.of (D.label i j) C.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label i j) w C.rightStart hz := by
  dsimp only
  let C := D.horizontalSwitchLeftConnectorComparison
    hxU hxV hUV hU hV i k j hshared hswitch
  rw [C.map_startChange_inv]
  rfl

/-- 水平异标签公共边在右格下端的 comparison potential，是同一共享交集顶点处右格 connector
的统一 vertex potential。-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRight_startPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchRightConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩
    let w := C.edgeSource
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label k j) z = w := rfl
    ((Monoid.PushoutI.of (D.label k j) C.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label k j) w C.rightStart hz := by
  dsimp only
  let C := D.horizontalSwitchRightConnectorComparison
    hxU hxV hUV hU hV i k j hshared hswitch
  rw [C.map_startChange_inv]
  rfl

namespace BinaryOpenCoverSquareSubdivision

/-- 水平异标签公共边的真实起点 transition 已经是左右 comparison potentials 的比值。-/
theorem horizontalSwitchEdgeTransitions_start_eq_comparisonPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let CL := D.horizontalSwitchLeftConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let CR := D.horizontalSwitchRightConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let T := D.horizontalSwitchEdgeTransitions
      hxU hxV hUV hU hV i k j hshared hswitch
    T.startChange = transitionFromPotentials
      ((Monoid.PushoutI.of (D.label i j) CL.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of (D.label k j) CR.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  simp [BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions,
    transitionFromPotentials]

end BinaryOpenCoverSquareSubdivision

/-- 水平异标签公共边在左格上端的 comparison potential，是共享交集顶点处左格 connector 的统一
vertex potential。-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeft_endPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchLeftConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩
    let w := C.edgeTarget
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z = w := rfl
    ((Monoid.PushoutI.of (D.label i j) C.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label i j) w C.rightEnd hz := by
  dsimp only
  let C := D.horizontalSwitchLeftConnectorComparison
    hxU hxV hUV hU hV i k j hshared hswitch
  rw [C.map_endChange_inv]
  rfl

/-- 水平异标签公共边在右格上端的 comparison potential，是同一共享交集顶点处右格 connector
的统一 vertex potential。-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRight_endPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let C := D.horizontalSwitchRightConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩
    let w := C.edgeTarget
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label k j) z = w := rfl
    ((Monoid.PushoutI.of (D.label k j) C.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label k j) w C.rightEnd hz := by
  dsimp only
  let C := D.horizontalSwitchRightConnectorComparison
    hxU hxV hUV hU hV i k j hshared hswitch
  rw [C.map_endChange_inv]
  rfl

/-- 水平异标签公共边的真实终点 transition 是左右 comparison end potentials 的比值。-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions_end_eq_comparisonPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let CL := D.horizontalSwitchLeftConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let CR := D.horizontalSwitchRightConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    let T := D.horizontalSwitchEdgeTransitions
      hxU hxV hUV hU hV i k j hshared hswitch
    T.endChange = transitionFromPotentials
      ((Monoid.PushoutI.of (D.label i j) CL.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of (D.label k j) CR.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  simp [BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions,
    transitionFromPotentials]

/-- 竖直异标签公共边在下格右端的 comparison potential，是共享交集顶点处下格 connector 的统一
vertex potential。-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottom_endPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩
    let w := C.edgeTarget
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z = w := rfl
    ((Monoid.PushoutI.of (D.label i j) C.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label i j) w C.rightEnd hz := by
  dsimp only
  let C := D.verticalSwitchBottomConnectorComparison
    hxU hxV hUV hU hV i j l hshared hswitch
  rw [C.map_endChange_inv]
  rfl

/-- 上格右端的对称版本。-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTop_endPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩
    let w := C.edgeTarget
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label i l) z = w := rfl
    ((Monoid.PushoutI.of (D.label i l) C.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label i l) w C.rightEnd hz := by
  dsimp only
  let C := D.verticalSwitchTopConnectorComparison
    hxU hxV hUV hU hV i j l hshared hswitch
  rw [C.map_endChange_inv]
  rfl

/-- 竖直异标签公共边在下格左端的 comparison potential，是共享交集顶点处下格 connector 的统一
vertex potential。-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottom_startPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩
    let w := C.edgeSource
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z = w := rfl
    ((Monoid.PushoutI.of (D.label i j) C.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label i j) w C.rightStart hz := by
  dsimp only
  let C := D.verticalSwitchBottomConnectorComparison
    hxU hxV hUV hU hV i j l hshared hswitch
  rw [C.map_startChange_inv]
  rfl

/-- 竖直异标签公共边在上格左端的 comparison potential，是同一交集顶点处上格 connector 的统一
vertex potential。-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTop_startPotential_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let C := D.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩
    let w := C.edgeSource
    let hz : binaryOpenCoverIntersectionToPiece U V (D.label i l) z = w := rfl
    ((Monoid.PushoutI.of (D.label i l) C.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (D.label i l) w C.rightStart hz := by
  dsimp only
  let C := D.verticalSwitchTopConnectorComparison
    hxU hxV hUV hU hV i j l hshared hswitch
  rw [C.map_startChange_inv]
  rfl

/-- 上一定理的实际单格角版本：若任意交集点分别识别为下格左上角与上格左下角，则同标签竖直
transition 是两格各自实际标签 vertex potentials 之比。-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdgeTransitions_start_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l)
    (z : ↥(U ∩ V))
    (hzBottom : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 0 1)
    (hzTop : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPiece i l 0 0) :
    let T := D.verticalCommonEdgeTransitions hxU hxV hU hV
      i j l hshared hlabel
    T.startChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 0 1 hzBottom)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i l 0 0 hzTop) := by
  let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
    i j l hshared hlabel
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  have hzTop' : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel i l 0 0 (D.label i j) hlabel.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel]
    simpa only [coe_binaryOpenCoverIntersectionToPiece] using
      congrArg Subtype.val hzTop
  have href : C.edgeSource =
      binaryOpenCoverIntersectionToPiece U V (D.label i j) z :=
    (D.verticalCommonEdge_source_eq_bottom i j l hshared hlabel).trans
      hzBottom.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)) href
  change (f C.startChange)⁻¹ = _
  rw [C.map_startChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftStart) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label i j) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
            hzBottom.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 1))
    apply congrArg f
    rw [show C.leftStart =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 1).cast rfl
        (D.verticalCommonEdge_source_eq_bottom i j l hshared hlabel) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
      hzBottom href (D.verticalCommonEdge_source_eq_bottom i j l hshared hlabel)
  · let explicitTop := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z i l 0 0 (D.label i j) hlabel.symm hzTop'
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z i l 0 0
      (D.label i j) (D.label i l) hlabel.symm rfl hzTop' hzTop
    calc
      f (connectorChange reference C.rightStart) = explicitTop := by
        unfold explicitTop
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightStart =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            i l 0 0 (D.label i j) hlabel.symm).cast rfl
              (D.verticalCommonEdge_source_eq_top i j l hshared hlabel) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
          hzTop' href (D.verticalCommonEdge_source_eq_top i j l hshared hlabel)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z i l 0 0 (D.label i l) rfl hzTop := hactual
      _ = D.gridCellVertexPotentialFromIntersection hxU hxV hUV hU hV
          z i l 0 0 hzTop := rfl

/-- 同一异标签几何边配上两侧任意局部 connectors 后，其两侧 Pushout 元素满足统一端点 gauge
关系。方格左边界比较只需实例化这一个定理。-/
theorem binaryOpenCoverDualPath_localElements_pushout_rebase
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c)) :
    let CB := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hb bStart bEnd
    let CC := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hc cStart cEnd
    (Monoid.PushoutI.of b CB.rightElement :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge
        ((Monoid.PushoutI.of c CC.startChange)⁻¹ *
          Monoid.PushoutI.of b CB.startChange)
        ((Monoid.PushoutI.of c CC.endChange)⁻¹ *
          Monoid.PushoutI.of b CB.endChange)
        (Monoid.PushoutI.of c CC.rightElement) := by
  dsimp only
  let CB := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    q hb hc hne hb bStart bEnd
  let CC := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    q hb hc hne hc cStart cEnd
  let fB := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) b)
  let fC := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) c)
  have hB := congrArg fB
    (binaryOpenCoverDualPathConnectorComparison_relation hxU hxV hUV
      q hb hc hne hb bStart bEnd)
  have hC := congrArg fC
    (binaryOpenCoverDualPathConnectorComparison_relation hxU hxV hUV
      q hb hc hne hc cStart cEnd)
  simp only [map_mul, map_inv] at hB hC
  have hcommon := binaryOpenCoverDualPathPieceElements_pushout_eq
    hxU hxV hUV q hb hc hne
  exact edgeElements_eq_rebaseEdge_of_change_relations
    (fB CB.endChange) (fB CB.startChange)
    (fB (binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne b))
    (fB CB.rightElement)
    (fC CC.endChange) (fC CC.startChange)
    (fC (binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne c))
    (fC CC.rightElement) hB hC hcommon

/-- 同标签时，同一几何道路的两套局部 connector 直接在共同覆盖成员中比较。-/
noncomputable def binaryOpenCoverSamePathConnectorComparison
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c)) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) := by
  subst c
  exact
    { edgeSource := ⟨z, by simpa using hb 0⟩
      edgeTarget := ⟨w, by simpa using hb 1⟩
      edge := binaryOpenCoverPathInPiece q hb
      leftStart := bStart
      leftEnd := bEnd
      rightStart := cStart
      rightEnd := cEnd }

/-- 同标签 comparison 的终点就是由左侧成员性证明给出的道路终点。把这一投影公式显式冻结，
避免具体 Bool 标签等式在调用点留下 `Eq.rec`。-/
theorem binaryOpenCoverSamePathConnectorComparison_edgeTarget
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c)) :
    (binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd).edgeTarget =
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b) := by
  subst c
  rfl

/-- 同标签 comparison 的起点就是由左侧成员性证明给出的道路起点。-/
theorem binaryOpenCoverSamePathConnectorComparison_edgeSource
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c)) :
    (binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd).edgeSource =
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b) := by
  subst c
  rfl

/-- same-path comparison 的左起点 connector 送回环境空间后就是输入的左 connector。-/
@[simp] theorem coe_binaryOpenCoverSamePathConnectorComparison_leftStart
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c))
    (u : unitInterval) :
    ((binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd).leftStart u : X) = bStart u := by
  subst c
  rfl

/-- same-path comparison 的右起点 connector 送回环境空间后就是输入的右 connector。-/
@[simp] theorem coe_binaryOpenCoverSamePathConnectorComparison_rightStart
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c))
    (u : unitInterval) :
    ((binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd).rightStart u : X) = cStart u := by
  subst c
  rfl

/-- same-path comparison 的左终点 connector 送回环境空间后就是输入的左 connector。-/
@[simp] theorem coe_binaryOpenCoverSamePathConnectorComparison_leftEnd
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c))
    (u : unitInterval) :
    ((binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd).leftEnd u : X) = bEnd u := by
  subst c
  rfl

/-- same-path comparison 的右终点 connector 送回环境空间后就是输入的右 connector；该形式越过
标签等式 transport，正适合后续 `Path.ext`。-/
@[simp] theorem coe_binaryOpenCoverSamePathConnectorComparison_rightEnd
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c))
    (u : unitInterval) :
    ((binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd).rightEnd u : X) = cEnd u := by
  subst c
  rfl

/-- 同标签道路两套局部元素进入 Pushout 后的端点 gauge 关系。-/
theorem binaryOpenCoverSamePath_localElements_pushout_rebase
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c)) :
    let C := binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd
    (Monoid.PushoutI.of b C.leftElement :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge
        (Monoid.PushoutI.of b C.startChange)⁻¹
        (Monoid.PushoutI.of b C.endChange)⁻¹
        (Monoid.PushoutI.of b C.rightElement) := by
  subst c
  dsimp only
  let C := binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc rfl
    bStart bEnd cStart cEnd
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) b)
  have h := congrArg f C.rightElement_eq
  simp only [map_mul, map_inv] at h
  apply eq_rebaseEdge_of_rebaseEdge_eq (f C.startChange) (f C.endChange)
  simpa [rebaseEdge] using h

end SandronesLibrary.Topology
