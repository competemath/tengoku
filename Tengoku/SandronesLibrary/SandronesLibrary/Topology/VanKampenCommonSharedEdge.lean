/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenHomotopySquareBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 方格中同标签小格的公共边比较

本文件处理两个水平或竖直相邻小格标签相同时的公共几何边。它把公共边提升到共同覆盖成员，比较
两格各自角 connector 产生的修正环路，并给出精确的非交换群换 connector 公式。

当前条目：

* `topology.fundamental-group.van-kampen-common-shared-edge`。

本文件不处理异标签 switch edge，不使用交集道路连通性或 Pushout 关系，也不宣称内部边已全局
消去。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 同一条定向边使用两套端点连接时，两个修正环路由左右端点的连接差精确联系。

> **Entry**: topology.fundamental-group.van-kampen-common-shared-edge
@isnad1 id=eq.0h9v.s7.0d308eace022 from=translated src=- shape=9c555f38 vocab=7863b9fe
-/
theorem correctedLoop_change_connectors {x₀ z w : X}
    (left left' : Path x₀ z) (segment : Path z w) (right right' : Path x₀ w) :
    (FundamentalGroup.fromPath
        ⟦Path.correctedLoop right' (Path.refl w) right⟧)⁻¹ *
        FundamentalGroup.fromPath ⟦Path.correctedLoop left segment right⟧ *
        FundamentalGroup.fromPath
          ⟦Path.correctedLoop left' (Path.refl z) left⟧ =
      FundamentalGroup.fromPath ⟦Path.correctedLoop left' segment right'⟧ := by
  rw [← correctedLoop_reverse_eq_inv right' (Path.refl w) right]
  rw [Path.correctedLoop_product, Path.correctedLoop_product]
  unfold Path.correctedLoop FundamentalGroup.fromPath FundamentalGroup.fromArrow
  simp

/-- 同时 transport 修正环路的两条连接和中间边，不改变所得基环路。
@isnad1 id=eq.2h9v.s6.f3733b89df63 from=translated src=- shape=79d3d024 vocab=c8e14545
-/
theorem correctedLoop_cast {x₀ z w z' w' : X}
    (left : Path x₀ z) (segment : Path z w) (right : Path x₀ w)
    (hz : z' = z) (hw : w' = w) :
    Path.correctedLoop (left.cast rfl hz) (segment.cast hz hw) (right.cast rfl hw) =
      Path.correctedLoop left segment right := by
  apply Path.ext
  unfold Path.correctedLoop
  funext t
  simp only [Path.trans_apply, Path.symm_apply]
  rfl

/-- `correctedLoop_cast` 的证明无关版本：四个端点 transport 证明可以分别给出。
@isnad1 id=eq.4h9v.s6.0cf6f730b7ae from=translated src=- shape=9c5ab0d4 vocab=c8e14545
-/
theorem correctedLoop_cast_proof_irrel {x₀ z w z' w' : X}
    (left : Path x₀ z) (segment : Path z w) (right : Path x₀ w)
    (hzLeft hzSegment : z' = z) (hwSegment hwRight : w' = w) :
    Path.correctedLoop (left.cast rfl hzLeft) (segment.cast hzSegment hwSegment)
        (right.cast rfl hwRight) =
      Path.correctedLoop left segment right := by
  rw [Subsingleton.elim hzLeft hzSegment, Subsingleton.elim hwRight hwSegment]
  exact correctedLoop_cast left segment right hzSegment hwSegment

/-- 水平相邻两格共享的竖边，提升到左格标签指定的覆盖成员。-/
def BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    Path
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc,
        by
          simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
            using D.cell_mem i j 1 0⟩ : binaryOpenCoverPiece U V (D.label i j))
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ,
        by
          simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
            using D.cell_mem i j 1 1⟩ : binaryOpenCoverPiece U V (D.label i j)) :=
  pathCodRestrict (binaryOpenCoverPiece U V (D.label i j))
    (squareGridVerticalEdge H D.steps D.steps_pos i.succ j)
    (by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 0)
    (by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 1)
    (by
      intro t
      change H (unitIntervalMeshPoint D.steps D.steps_pos i.succ,
        Set.Icc.convexComb (unitIntervalMeshPoint D.steps D.steps_pos j.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos j.succ) t) ∈
        binaryOpenCoverPiece U V (D.label i j)
      rw [hlabel]
      simpa only [unitSquareCellPoint, Set.Icc.convexComb_zero, hshared]
        using D.cell_mem k j 0 t)

/--
@isnad1 id=eq.2h9v.s9.c90d28f211c1 from=translated src=- shape=f0e90850 vocab=10e08bdd
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_horizontalCommonEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) (t : unitInterval) :
    ((D.horizontalCommonEdgeInPiece i k j hshared hlabel t :
      binaryOpenCoverPiece U V (D.label i j)) : X) =
      squareGridVerticalEdge H D.steps D.steps_pos i.succ j t := rfl

/-- 竖直相邻两格共享的横边，提升到下格标签指定的覆盖成员。-/
def BinaryOpenCoverSquareSubdivision.verticalCommonEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    Path
      (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ,
        by
          simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
            using D.cell_mem i j 0 1⟩ : binaryOpenCoverPiece U V (D.label i j))
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ,
        by
          simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
            using D.cell_mem i j 1 1⟩ : binaryOpenCoverPiece U V (D.label i j)) :=
  pathCodRestrict (binaryOpenCoverPiece U V (D.label i j))
    (squareGridHorizontalEdge H D.steps D.steps_pos i j.succ)
    (by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 0 1)
    (by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 1)
    (by
      intro t
      change H (Set.Icc.convexComb
          (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ) t,
        unitIntervalMeshPoint D.steps D.steps_pos j.succ) ∈
        binaryOpenCoverPiece U V (D.label i j)
      rw [hlabel]
      simpa only [unitSquareCellPoint, Set.Icc.convexComb_zero, hshared]
        using D.cell_mem i l t 0)

/-- 同一条定向边配备两套公共基点到端点的连接。-/
structure CommonEdgeConnectorComparison (S : Type*) [TopologicalSpace S] (base : S) where
  edgeSource : S
  edgeTarget : S
  edge : Path edgeSource edgeTarget
  leftStart : Path base edgeSource
  leftEnd : Path base edgeTarget
  rightStart : Path base edgeSource
  rightEnd : Path base edgeTarget

def CommonEdgeConnectorComparison.leftElement
    {S : Type*} [TopologicalSpace S] {base : S}
    (C : CommonEdgeConnectorComparison S base) : FundamentalGroup S base :=
  FundamentalGroup.fromPath ⟦Path.correctedLoop C.leftStart C.edge C.leftEnd⟧

def CommonEdgeConnectorComparison.rightElement
    {S : Type*} [TopologicalSpace S] {base : S}
    (C : CommonEdgeConnectorComparison S base) : FundamentalGroup S base :=
  FundamentalGroup.fromPath ⟦Path.correctedLoop C.rightStart C.edge C.rightEnd⟧

def CommonEdgeConnectorComparison.startChange
    {S : Type*} [TopologicalSpace S] {base : S}
    (C : CommonEdgeConnectorComparison S base) : FundamentalGroup S base :=
  FundamentalGroup.fromPath
    ⟦Path.correctedLoop C.rightStart (Path.refl C.edgeSource) C.leftStart⟧

def CommonEdgeConnectorComparison.endChange
    {S : Type*} [TopologicalSpace S] {base : S}
    (C : CommonEdgeConnectorComparison S base) : FundamentalGroup S base :=
  FundamentalGroup.fromPath
    ⟦Path.correctedLoop C.rightEnd (Path.refl C.edgeTarget) C.leftEnd⟧

/-- 同标签公共边两侧的修正元素由端点连接差控制。
@isnad1 id=eq.0h3v.s7.6930935186e1 from=translated src=- shape=7249f0aa vocab=db2245af
-/
theorem CommonEdgeConnectorComparison.rightElement_eq
    {S : Type*} [TopologicalSpace S] {base : S}
    (C : CommonEdgeConnectorComparison S base) :
    C.endChange⁻¹ * C.leftElement * C.startChange = C.rightElement := by
  exact correctedLoop_change_connectors C.leftStart C.rightStart C.edge C.leftEnd C.rightEnd

/--
@isnad1 id=eq.1h10v.s7.f1884f8a6008 from=translated src=- shape=757be8e0 vocab=14354e08
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_gridCellVertexInPieceOfLabel
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (a b : Fin 2) (label : Bool) (hlabel : D.label i j = label) :
    ((D.gridCellVertexInPieceOfLabel i j a b label hlabel :
      binaryOpenCoverPiece U V label) : X) = D.gridCellVertexInPiece i j a b := by
  cases hlabel
  rfl

/-- 用显式标签等式把单格映射放到指定的共同覆盖成员中。-/
def BinaryOpenCoverSquareSubdivision.gridCellMapInPieceOfLabel
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (label : Bool) (hlabel : D.label i j = label) :
    C(unitInterval × unitInterval, binaryOpenCoverPiece U V label) := by
  cases hlabel
  exact D.gridCellMapInPiece i j

/--
@isnad1 id=eq.1h9v.s8.959f38fb1b6f from=translated src=- shape=d56e98ef vocab=2f704f15
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_gridCellMapInPieceOfLabel
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (label : Bool) (hlabel : D.label i j = label)
    (z : unitInterval × unitInterval) :
    ((D.gridCellMapInPieceOfLabel i j label hlabel z :
      binaryOpenCoverPiece U V label) : X) =
      H (unitSquareCellPoint D.steps D.steps_pos i j z.1 z.2) := by
  cases hlabel
  rfl

/--
@isnad1 id=eq.1h10v.s8.a9defaa58c9b from=translated src=- shape=4f8c1e3c vocab=9d821488
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellMapInPieceOfLabel_unitSquareGridVertex
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (a b : Fin 2) (label : Bool) (hlabel : D.label i j = label) :
    D.gridCellMapInPieceOfLabel i j label hlabel (unitSquareGridVertex a b) =
      D.gridCellVertexInPieceOfLabel i j a b label hlabel := by
  apply Subtype.ext
  rw [D.coe_gridCellMapInPieceOfLabel, D.coe_gridCellVertexInPieceOfLabel]
  rfl

/-- 左格右下角与规范水平公共边起点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.b56245146cd3 from=translated src=- shape=05123da0 vocab=4ba1498f
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_source_eq_left
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (_hshared : i.succ = k.castSucc)
    (_hlabel : D.label i j = D.label k j) :
    (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc,
      by
        simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
          using D.cell_mem i j 1 0⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel i j 1 0 (D.label i j) rfl := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 右格左下角与规范水平公共边起点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.5c87f880ef2f from=translated src=- shape=3d9038ea vocab=a6387fab
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_source_eq_right
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc,
      by
        simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
          using D.cell_mem i j 1 0⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel k j 0 0 (D.label i j) hlabel.symm := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared]

/-- 左格右上角与规范水平公共边终点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.2aa14cd83cdf from=translated src=- shape=9d2ecdb9 vocab=f9a5aadb
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_target_eq_left
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (_hshared : i.succ = k.castSucc)
    (_hlabel : D.label i j = D.label k j) :
    (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ,
      by
        simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
          using D.cell_mem i j 1 1⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel i j 1 1 (D.label i j) rfl := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 右格左上角与规范水平公共边终点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.5691269073da from=translated src=- shape=871fa1e3 vocab=f5e71134
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_target_eq_right
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ,
      by
        simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
          using D.cell_mem i j 1 1⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel k j 0 1 (D.label i j) hlabel.symm := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared, hone]

/-- 下格左上角与规范竖直公共边起点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.ddcc6472576a from=translated src=- shape=037acbfd vocab=4ba1498f
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_source_eq_bottom
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (_hshared : j.succ = l.castSucc)
    (_hlabel : D.label i j = D.label i l) :
    (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 0 1⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel i j 0 1 (D.label i j) rfl := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 上格左下角与规范竖直公共边起点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.d4906dae545d from=translated src=- shape=69d5bb39 vocab=a6387fab
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_source_eq_top
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 0 1⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel i l 0 0 (D.label i j) hlabel.symm := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared]

/-- 下格右上角与规范竖直公共边终点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.49612d11e2d7 from=translated src=- shape=14b36f7b vocab=f9a5aadb
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_target_eq_bottom
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (_hshared : j.succ = l.castSucc)
    (_hlabel : D.label i j = D.label i l) :
    (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 1⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel i j 1 1 (D.label i j) rfl := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 上格右下角与规范竖直公共边终点是同一个子空间点。
@isnad1 id=eq.2h8v.s8.a63755241e4e from=translated src=- shape=c5e32fea vocab=f5e71134
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_target_eq_top
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 1⟩ : binaryOpenCoverPiece U V (D.label i j)) =
      D.gridCellVertexInPieceOfLabel i l 1 0 (D.label i j) hlabel.symm := by
  apply Subtype.ext
  rw [D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hshared, hone]

/-- 竖直相邻同标签小格围绕规范公共横边形成的两套连接比较数据。-/
def BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) where
  edgeSource :=
    ⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 0 1⟩
  edgeTarget :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 1⟩
  edge := D.verticalCommonEdgeInPiece i j l hshared hlabel
  leftStart :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV i j 0 1
      (D.label i j) rfl).cast rfl
        (D.verticalCommonEdge_source_eq_bottom i j l hshared hlabel)
  leftEnd :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV i j 1 1
      (D.label i j) rfl).cast rfl
        (D.verticalCommonEdge_target_eq_bottom i j l hshared hlabel)
  rightStart :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV i l 0 0
      (D.label i j) hlabel.symm).cast rfl
        (D.verticalCommonEdge_source_eq_top i j l hshared hlabel)
  rightEnd :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV i l 1 0
      (D.label i j) hlabel.symm).cast rfl
        (D.verticalCommonEdge_target_eq_top i j l hshared hlabel)

/-- 竖直同标签公共边两侧的修正元素满足精确的端点换连接关系。
@isnad1 id=other.6h9v.s10.5cf7b2bc19da from=translated src=- shape=ac663894 vocab=71b1475f
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
      i j l hshared hlabel
    C.endChange⁻¹ * C.leftElement * C.startChange = C.rightElement := by
  exact CommonEdgeConnectorComparison.rightElement_eq _

/--
@isnad1 id=eq.2h9v.s9.b0b583eeac47 from=translated src=- shape=4497a07e vocab=763c8d71
-/
@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_verticalCommonEdgeInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) (t : unitInterval) :
    ((D.verticalCommonEdgeInPiece i j l hshared hlabel t :
      binaryOpenCoverPiece U V (D.label i j)) : X) =
      squareGridHorizontalEdge H D.steps D.steps_pos i j.succ t := rfl

/-- 规范竖直公共边与下格局部上横边在端点 transport 后相同。
@isnad1 id=eq.2h8v.s11.5d42286e4670 from=translated src=- shape=4cf22e5c vocab=bd87ba96
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_eq_bottomCellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    D.verticalCommonEdgeInPiece i j l hshared hlabel =
      (((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous).cast
          (D.verticalCommonEdge_source_eq_bottom i j l hshared hlabel)
          (D.verticalCommonEdge_target_eq_bottom i j l hshared hlabel)) := by
  let q := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous
  let hs := D.verticalCommonEdge_source_eq_bottom i j l hshared hlabel
  let ht := D.verticalCommonEdge_target_eq_bottom i j l hshared hlabel
  apply Path.ext
  calc
    (D.verticalCommonEdgeInPiece i j l hshared hlabel :
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
      rw [D.coe_verticalCommonEdgeInPiece]
      rw [hqt]
      simp [squareGridHorizontalEdge,
        BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
        unitSquareCellPoint, hone]
      rfl
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
      (Path.cast_coe q hs ht).symm

/-- 规范竖直公共边与上格局部下横边在标签和端点 transport 后相同。
@isnad1 id=eq.2h8v.s11.5c6fd4d77935 from=translated src=- shape=a859a7a0 vocab=40405122
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_eq_topCellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    D.verticalCommonEdgeInPiece i j l hshared hlabel =
      (((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0).map
          (D.gridCellMapInPieceOfLabel i l (D.label i j) hlabel.symm).continuous).cast
          ((D.verticalCommonEdge_source_eq_top i j l hshared hlabel).trans
            (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i l 0 0
              (D.label i j) hlabel.symm).symm)
          ((D.verticalCommonEdge_target_eq_top i j l hshared hlabel).trans
            (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i l 1 0
              (D.label i j) hlabel.symm).symm)) := by
  let q := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map
      (D.gridCellMapInPieceOfLabel i l (D.label i j) hlabel.symm).continuous
  let hs := (D.verticalCommonEdge_source_eq_top i j l hshared hlabel).trans
    (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i l 0 0
      (D.label i j) hlabel.symm).symm
  let ht := (D.verticalCommonEdge_target_eq_top i j l hshared hlabel).trans
    (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i l 1 0
      (D.label i j) hlabel.symm).symm
  apply Path.ext
  calc
    (D.verticalCommonEdgeInPiece i j l hshared hlabel :
        unitInterval → binaryOpenCoverPiece U V (D.label i j)) =
        (q : unitInterval → binaryOpenCoverPiece U V (D.label i j)) := by
      funext t
      apply Subtype.ext
      have hqt : q t = D.gridCellMapInPieceOfLabel i l (D.label i j) hlabel.symm
          (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
            1 unitSquareOnePos 0 0 t) := by
        rfl
      have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
        simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
      rw [D.coe_verticalCommonEdgeInPiece]
      rw [hqt, D.coe_gridCellMapInPieceOfLabel]
      simp [squareGridHorizontalEdge, unitSquareCellPoint, hshared, hone]
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
      (Path.cast_coe q hs ht).symm

/-- 以显式标签构造单格局部横边元素，供同标签相邻格在同一群中比较。-/
def BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPieceOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (row : Fin 2) (label : Bool)
    (hlabel : D.label i j = label) :
    FundamentalGroup (binaryOpenCoverPiece U V label)
      (binaryOpenCoverBasepoint hxU hxV label) :=
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
      i j 0 row label hlabel)
    (((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 row).map
        (D.gridCellMapInPieceOfLabel i j label hlabel).continuous).cast
      (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i j 0 row label hlabel).symm
      (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i j 1 row label hlabel).symm)
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
      i j 1 row label hlabel)⟧

/-- 竖直公共边比较对象的左元素就是下格四边词中的上横边元素。
@isnad1 id=eq.6h9v.s8.20b7bdf6c99e from=translated src=- shape=a0de0369 vocab=d6ad3578
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdgeComparison_leftElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    (D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
      i j l hshared hlabel).leftElement =
      D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1 := by
  let p := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 0 1 (D.label i j) rfl
  let q := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 1 1 (D.label i j) rfl
  let hs := D.verticalCommonEdge_source_eq_bottom i j l hshared hlabel
  let ht := D.verticalCommonEdge_target_eq_bottom i j l hshared hlabel
  have hp : Path.correctedLoop (p.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop p q r := correctedLoop_cast p q r hs ht
  unfold CommonEdgeConnectorComparison.leftElement
    BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPiece
  rw [D.verticalCommonEdge_eq_bottomCellEdge i j l hshared hlabel]
  dsimp only [CommonEdgeConnectorComparison.leftStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.leftEnd]
  exact congrArg Path.Homotopic.Quotient.mk hp

/-- 竖直公共边比较对象的右元素就是上格在共同显式标签中的下横边元素。
@isnad1 id=eq.6h9v.s8.70198d3d321c from=translated src=- shape=8cdeeaaf vocab=da3b7414
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdgeComparison_rightElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    (D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
      i j l hshared hlabel).rightElement =
      D.gridCellBasedHorizontalEdgeInPieceOfLabel hxU hxV hU hV
        i l 0 (D.label i j) hlabel.symm := by
  let p := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i l 0 0 (D.label i j) hlabel.symm
  let q₀ := (squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map
      (D.gridCellMapInPieceOfLabel i l (D.label i j) hlabel.symm).continuous
  let hv₀ := (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i l 0 0
    (D.label i j) hlabel.symm).symm
  let hv₁ := (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i l 1 0
    (D.label i j) hlabel.symm).symm
  let q := q₀.cast hv₀ hv₁
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i l 1 0 (D.label i j) hlabel.symm
  let hs := D.verticalCommonEdge_source_eq_top i j l hshared hlabel
  let ht := D.verticalCommonEdge_target_eq_top i j l hshared hlabel
  let hsQ := hs.trans hv₀
  let htQ := ht.trans hv₁
  have hsegment : q₀.cast hsQ htQ = q.cast hs ht := by
    apply Path.ext
    calc
      (q₀.cast hsQ htQ : unitInterval → binaryOpenCoverPiece U V (D.label i j)) =
          (q₀ : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
        Path.cast_coe q₀ hsQ htQ
      _ = (q : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
        (Path.cast_coe q₀ hv₀ hv₁).symm
      _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
        (Path.cast_coe q hs ht).symm
  have hp : Path.correctedLoop (p.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop p q r := correctedLoop_cast p q r hs ht
  unfold CommonEdgeConnectorComparison.rightElement
    BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPieceOfLabel
  rw [D.verticalCommonEdge_eq_topCellEdge i j l hshared hlabel]
  dsimp only [CommonEdgeConnectorComparison.rightStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.rightEnd]
  rw [hsegment]
  exact congrArg Path.Homotopic.Quotient.mk hp

/-- 竖直同标签内部边的两侧真实局部生成元满足完整的换连接关系。
@isnad1 id=other.6h9v.s10.c8a1bcc970da from=translated src=- shape=ed1adb8e vocab=14876f3f
-/
theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_pieceElements_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
      i j l hshared hlabel
    C.endChange⁻¹ *
        D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1 *
        C.startChange =
      D.gridCellBasedHorizontalEdgeInPieceOfLabel hxU hxV hU hV
        i l 0 (D.label i j) hlabel.symm := by
  dsimp only
  rw [← D.verticalCommonEdgeComparison_leftElement hxU hxV hU hV
    i j l hshared hlabel]
  rw [D.verticalCommonEdgeConnectorComparison_relation hxU hxV hU hV
    i j l hshared hlabel]
  exact D.verticalCommonEdgeComparison_rightElement hxU hxV hU hV
    i j l hshared hlabel

/-- 水平相邻同标签小格围绕其规范公共边形成的两套连接比较数据。-/
def BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) where
  edgeSource :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 0⟩
  edgeTarget :=
    ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
      simpa [squareGridVertex, unitSquareCellPoint, Set.Icc.convexComb_one]
        using D.cell_mem i j 1 1⟩
  edge := D.horizontalCommonEdgeInPiece i k j hshared hlabel
  leftStart :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV i j 1 0
      (D.label i j) rfl).cast rfl
        (D.horizontalCommonEdge_source_eq_left i k j hshared hlabel)
  leftEnd :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV i j 1 1
      (D.label i j) rfl).cast rfl
        (D.horizontalCommonEdge_target_eq_left i k j hshared hlabel)
  rightStart :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV k j 0 0
      (D.label i j) hlabel.symm).cast rfl
        (D.horizontalCommonEdge_source_eq_right i k j hshared hlabel)
  rightEnd :=
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV k j 0 1
      (D.label i j) hlabel.symm).cast rfl
        (D.horizontalCommonEdge_target_eq_right i k j hshared hlabel)

/-- 水平同标签公共边两侧的修正元素满足精确的端点换连接关系。
@isnad1 id=other.6h9v.s10.f48580b02d1d from=translated src=- shape=d99ce754 vocab=9035c10a
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
      i k j hshared hlabel
    C.endChange⁻¹ * C.leftElement * C.startChange = C.rightElement := by
  exact CommonEdgeConnectorComparison.rightElement_eq _

/-- 规范水平公共边与左格局部右竖边在端点 transport 后相同。
@isnad1 id=eq.2h8v.s11.d3738ca47d91 from=translated src=- shape=842384d8 vocab=2cca75a4
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_eq_leftCellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    D.horizontalCommonEdgeInPiece i k j hshared hlabel =
      (((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece i j).continuous).cast
          (D.horizontalCommonEdge_source_eq_left i k j hshared hlabel)
          (D.horizontalCommonEdge_target_eq_left i k j hshared hlabel)) := by
  let q := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece i j).continuous
  let hs := D.horizontalCommonEdge_source_eq_left i k j hshared hlabel
  let ht := D.horizontalCommonEdge_target_eq_left i k j hshared hlabel
  apply Path.ext
  calc
    (D.horizontalCommonEdgeInPiece i k j hshared hlabel :
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
      rw [D.coe_horizontalCommonEdgeInPiece]
      rw [hqt]
      simp [squareGridVerticalEdge,
        BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
        unitSquareCellPoint, hone]
      rfl
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
      (Path.cast_coe q hs ht).symm

/-- 规范水平公共边与右格局部左竖边在标签和端点 transport 后相同。
@isnad1 id=eq.2h8v.s11.b45dc849a920 from=translated src=- shape=efed14a1 vocab=b7783e76
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_eq_rightCellEdge
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    D.horizontalCommonEdgeInPiece i k j hshared hlabel =
      (((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0).map
          (D.gridCellMapInPieceOfLabel k j (D.label i j) hlabel.symm).continuous).cast
          ((D.horizontalCommonEdge_source_eq_right i k j hshared hlabel).trans
            (D.gridCellMapInPieceOfLabel_unitSquareGridVertex k j 0 0
              (D.label i j) hlabel.symm).symm)
          ((D.horizontalCommonEdge_target_eq_right i k j hshared hlabel).trans
            (D.gridCellMapInPieceOfLabel_unitSquareGridVertex k j 0 1
              (D.label i j) hlabel.symm).symm)) := by
  let q := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map
      (D.gridCellMapInPieceOfLabel k j (D.label i j) hlabel.symm).continuous
  let hs := (D.horizontalCommonEdge_source_eq_right i k j hshared hlabel).trans
    (D.gridCellMapInPieceOfLabel_unitSquareGridVertex k j 0 0
      (D.label i j) hlabel.symm).symm
  let ht := (D.horizontalCommonEdge_target_eq_right i k j hshared hlabel).trans
    (D.gridCellMapInPieceOfLabel_unitSquareGridVertex k j 0 1
      (D.label i j) hlabel.symm).symm
  apply Path.ext
  calc
    (D.horizontalCommonEdgeInPiece i k j hshared hlabel :
        unitInterval → binaryOpenCoverPiece U V (D.label i j)) =
        (q : unitInterval → binaryOpenCoverPiece U V (D.label i j)) := by
      funext t
      apply Subtype.ext
      have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
        simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
      have hqt : q t = D.gridCellMapInPieceOfLabel k j (D.label i j) hlabel.symm
          (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
            1 unitSquareOnePos 0 0 t) := by
        rfl
      rw [D.coe_horizontalCommonEdgeInPiece]
      rw [hqt, D.coe_gridCellMapInPieceOfLabel]
      simp [squareGridVerticalEdge, unitSquareCellPoint, hshared, hone]
    _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
      (Path.cast_coe q hs ht).symm

/-- 水平公共边比较对象的左元素就是左格四边词中的右竖边元素。
@isnad1 id=eq.6h9v.s8.15f7f2a37065 from=translated src=- shape=af50b2eb vocab=5812abf3
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeComparison_leftElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    (D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
      i k j hshared hlabel).leftElement =
      D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1 := by
  let l := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 1 0 (D.label i j) rfl
  let q := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece i j).continuous
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    i j 1 1 (D.label i j) rfl
  let hs := D.horizontalCommonEdge_source_eq_left i k j hshared hlabel
  let ht := D.horizontalCommonEdge_target_eq_left i k j hshared hlabel
  have hp : Path.correctedLoop (l.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop l q r := correctedLoop_cast l q r hs ht
  unfold CommonEdgeConnectorComparison.leftElement
    BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPiece
  rw [D.horizontalCommonEdge_eq_leftCellEdge i k j hshared hlabel]
  dsimp only [CommonEdgeConnectorComparison.leftStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.leftEnd]
  exact congrArg Path.Homotopic.Quotient.mk hp

/-- 以显式标签构造单格局部竖边元素，供同标签相邻格在同一群中比较。-/
def BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPieceOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (column : Fin 2) (label : Bool)
    (hlabel : D.label i j = label) :
    FundamentalGroup (binaryOpenCoverPiece U V label)
      (binaryOpenCoverBasepoint hxU hxV label) :=
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
      i j column 0 label hlabel)
    (((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos column 0).map
        (D.gridCellMapInPieceOfLabel i j label hlabel).continuous).cast
      (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i j column 0 label hlabel).symm
      (D.gridCellMapInPieceOfLabel_unitSquareGridVertex i j column 1 label hlabel).symm)
    (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
      i j column 1 label hlabel)⟧

/-- 水平同标签公共边的换连接公式，左侧已经识别为左格四边词中的真实生成元。
@isnad1 id=other.6h9v.s10.e433b545de6a from=translated src=- shape=a08c25f2 vocab=70df2da1
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_leftCell_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
      i k j hshared hlabel
    C.endChange⁻¹ *
        D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1 *
        C.startChange = C.rightElement := by
  rw [← D.horizontalCommonEdgeComparison_leftElement hxU hxV hU hV
    i k j hshared hlabel]
  exact D.horizontalCommonEdgeConnectorComparison_relation hxU hxV hU hV
    i k j hshared hlabel

/-- 水平公共边比较对象的右元素就是右格在共同显式标签中的左竖边元素。
@isnad1 id=eq.6h9v.s8.9e97ab4d0594 from=translated src=- shape=94ddb9f4 vocab=f1114534
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeComparison_rightElement
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    (D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
      i k j hshared hlabel).rightElement =
      D.gridCellBasedVerticalEdgeInPieceOfLabel hxU hxV hU hV
        k j 0 (D.label i j) hlabel.symm := by
  let l := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    k j 0 0 (D.label i j) hlabel.symm
  let q₀ := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map
      (D.gridCellMapInPieceOfLabel k j (D.label i j) hlabel.symm).continuous
  let hv₀ := (D.gridCellMapInPieceOfLabel_unitSquareGridVertex k j 0 0
    (D.label i j) hlabel.symm).symm
  let hv₁ := (D.gridCellMapInPieceOfLabel_unitSquareGridVertex k j 0 1
    (D.label i j) hlabel.symm).symm
  let q := q₀.cast hv₀ hv₁
  let r := D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
    k j 0 1 (D.label i j) hlabel.symm
  let hs := D.horizontalCommonEdge_source_eq_right i k j hshared hlabel
  let ht := D.horizontalCommonEdge_target_eq_right i k j hshared hlabel
  let hsQ := hs.trans hv₀
  let htQ := ht.trans hv₁
  have hsegment : q₀.cast hsQ htQ = q.cast hs ht := by
    apply Path.ext
    calc
      (q₀.cast hsQ htQ : unitInterval → binaryOpenCoverPiece U V (D.label i j)) =
          (q₀ : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
        Path.cast_coe q₀ hsQ htQ
      _ = (q : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
        (Path.cast_coe q₀ hv₀ hv₁).symm
      _ = (q.cast hs ht : unitInterval → binaryOpenCoverPiece U V (D.label i j)) :=
        (Path.cast_coe q hs ht).symm
  have hp : Path.correctedLoop (l.cast rfl hs) (q.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop l q r := correctedLoop_cast l q r hs ht
  unfold CommonEdgeConnectorComparison.rightElement
    BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison
    BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPieceOfLabel
  rw [D.horizontalCommonEdge_eq_rightCellEdge i k j hshared hlabel]
  dsimp only [CommonEdgeConnectorComparison.rightStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.rightEnd]
  rw [hsegment]
  exact congrArg Path.Homotopic.Quotient.mk hp

/-- 水平同标签内部边的两侧真实局部生成元满足完整的换连接关系。
@isnad1 id=other.6h9v.s10.ba38770f4904 from=translated src=- shape=0467ca00 vocab=a92be05d
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_pieceElements_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
      i k j hshared hlabel
    C.endChange⁻¹ *
        D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1 *
        C.startChange =
      D.gridCellBasedVerticalEdgeInPieceOfLabel hxU hxV hU hV
        k j 0 (D.label i j) hlabel.symm := by
  dsimp only
  rw [D.horizontalCommonEdge_leftCell_relation hxU hxV hU hV
    i k j hshared hlabel]
  exact D.horizontalCommonEdgeComparison_rightElement hxU hxV hU hV
    i k j hshared hlabel

end SandronesLibrary.Topology
