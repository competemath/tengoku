/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenVertexPotential

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 网格混合标签顶点的 transition coherence

本文件在四格标签不全相同时，以中央交集点及统一 connector 构造四个格角 potentials；在标签全同
时复用同一覆盖成员内的 common coherence。最终统一两种分支，证明任意相邻四格的真实内部边
transitions 在中央顶点满足方格关系。

当前条目：

* `topology.fundamental-group.van-kampen-mixed-vertex-coherence`。

本文件不执行整行或整网格 telescope，也不证明 kernel、单射或 van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 若中央顶点周围四格不全同标签，则该中央顶点落在覆盖交集。

> **Entry**: topology.fundamental-group.van-kampen-mixed-vertex-coherence-/
theorem BinaryOpenCoverSquareSubdivision.centralVertex_mem_intersection_of_not_all_eq
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    squareGridVertex H D.steps D.steps_pos i.succ j.succ ∈ U ∩ V := by
  by_cases hBottom : D.label i j = D.label k j
  · by_cases hLeft : D.label i j = D.label i l
    · have hRight : D.label k j ≠ D.label k l := by
        intro h
        exact hmixed ⟨hBottom, hLeft, hBottom.trans h⟩
      simpa [squareGridVertex, hHorizontal, Set.Icc.convexComb_zero]
        using D.verticalSwitchEdge_mem_intersection k j l hVertical hRight 0
    · simpa [squareGridVertex, Set.Icc.convexComb_one]
        using D.verticalSwitchEdge_mem_intersection i j l hVertical hLeft 1
  · simpa [squareGridVertex, Set.Icc.convexComb_one]
      using D.horizontalSwitchEdge_mem_intersection i k j hHorizontal hBottom 1

/-- 混合标签中央点作为覆盖交集的规范 subtype 点。-/
def BinaryOpenCoverSquareSubdivision.centralIntersectionVertex
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) : ↥(U ∩ V) :=
  ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ,
    D.centralVertex_mem_intersection_of_not_all_eq
      i k j l hHorizontal hVertical hmixed⟩

@[simp] theorem BinaryOpenCoverSquareSubdivision.coe_centralIntersectionVertex
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    ((D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed : ↥(U ∩ V)) : X) =
      squareGridVertex H D.steps D.steps_pos i.succ j.succ := rfl

/-- 混合标签中央点使用的一条统一交集 connector。-/
def BinaryOpenCoverSquareSubdivision.centralIntersectionConnector
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    Path (binaryOpenCoverIntersectionBasepoint hxU hxV)
      (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed) :=
  binaryOpenCoverIntersectionConnector hxU hxV hUV
    (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed)

/-- 统一交集中央点映入左下格标签成员后就是该格右上角。-/
private theorem BinaryOpenCoverSquareSubdivision.centralIntersectionVertex_toPiece_eq_bottomLeft
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryOpenCoverIntersectionToPiece U V (D.label i j)
        (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed) =
      D.gridCellVertexInPieceOfLabel i j 1 1 (D.label i j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
    BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hone]

/-- 统一交集中央点映入右下格标签成员后就是该格左上角。-/
private theorem BinaryOpenCoverSquareSubdivision.centralIntersectionVertex_toPiece_eq_bottomRight
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryOpenCoverIntersectionToPiece U V (D.label k j)
        (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed) =
      D.gridCellVertexInPieceOfLabel k j 0 1 (D.label k j) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
    BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hHorizontal, hone]

/-- 统一交集中央点映入左上格标签成员后就是该格右下角。-/
private theorem BinaryOpenCoverSquareSubdivision.centralIntersectionVertex_toPiece_eq_topLeft
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryOpenCoverIntersectionToPiece U V (D.label i l)
        (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed) =
      D.gridCellVertexInPieceOfLabel i l 1 0 (D.label i l) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
    BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hVertical, hone]

/-- 统一交集中央点映入右上格标签成员后就是该格左下角。-/
private theorem BinaryOpenCoverSquareSubdivision.centralIntersectionVertex_toPiece_eq_topRight
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryOpenCoverIntersectionToPiece U V (D.label k l)
        (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed) =
      D.gridCellVertexInPieceOfLabel k l 0 0 (D.label k l) rfl := by
  apply Subtype.ext
  rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
  simp [BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
    BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
    unitSquareCellPoint, hHorizontal, hVertical]

/-- 以统一交集 connector 为参考，得到一个单格角 connector 的 Pushout potential。-/
def BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (z : ↥(U ∩ V)) (i j : Fin D.steps) (a b : Fin 2)
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel i j a b (D.label i j) rfl) :
    binaryVanKampenPushout U V hxU hxV :=
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j) z).cast hb hz.symm
  Monoid.PushoutI.of (D.label i j)
    (connectorChange reference
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j a b))

/-- 混合中央点处左下格的规范 potential。-/
private def BinaryOpenCoverSquareSubdivision.centralPotentialBottomLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryVanKampenPushout U V hxU hxV :=
  D.gridCellVertexPotentialFromIntersection hxU hxV hUV hU hV
    (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed)
    i j 1 1
    (D.centralIntersectionVertex_toPiece_eq_bottomLeft
      i k j l hHorizontal hVertical hmixed)

/-- 混合中央点处右下格的规范 potential。-/
private def BinaryOpenCoverSquareSubdivision.centralPotentialBottomRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryVanKampenPushout U V hxU hxV :=
  D.gridCellVertexPotentialFromIntersection hxU hxV hUV hU hV
    (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed)
    k j 0 1
    (D.centralIntersectionVertex_toPiece_eq_bottomRight
      i k j l hHorizontal hVertical hmixed)

/-- 混合中央点处左上格的规范 potential。-/
private def BinaryOpenCoverSquareSubdivision.centralPotentialTopLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryVanKampenPushout U V hxU hxV :=
  D.gridCellVertexPotentialFromIntersection hxU hxV hUV hU hV
    (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed)
    i l 1 0
    (D.centralIntersectionVertex_toPiece_eq_topLeft
      i k j l hHorizontal hVertical hmixed)

/-- 混合中央点处右上格的规范 potential。-/
private def BinaryOpenCoverSquareSubdivision.centralPotentialTopRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    binaryVanKampenPushout U V hxU hxV :=
  D.gridCellVertexPotentialFromIntersection hxU hxV hUV hU hV
    (D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed)
    k l 0 0
    (D.centralIntersectionVertex_toPiece_eq_topRight
      i k j l hHorizontal hVertical hmixed)

/-- 同一交集点的两种 subtype/端点证明给出的 piece connector 在 transport 后相同。-/
private theorem binaryOpenCoverIntersectionConnectorInPiece_cast_eq
    {x₀ : X} {U V : Set X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (b : Bool) {z w : ↥(U ∩ V)} (hzw : z = w)
    {target : binaryOpenCoverPiece U V b}
    (hz : target = binaryOpenCoverIntersectionToPiece U V b z)
    (hw : target = binaryOpenCoverIntersectionToPiece U V b w) :
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b z).cast
        (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b) hz =
      (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV b w).cast
        (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV b) hw := by
  subst w
  rw [Subsingleton.elim hz hw]

/-- 同时规范 source 与 target transport，并选第二条 connector 的两个端点。-/
theorem connectorChange_cast_four_endpoints_right
    {a z w x v : X} (p : Path a z) (q : Path x w)
    (hxa : x = a) (hzw : z = w)
    (hpz : v = z) (hqw : v = w) :
    connectorChange (p.cast hxa hpz) (q.cast rfl hqw) =
      connectorChange (p.cast hxa hzw.symm) q := by
  subst a
  subst w
  simpa using connectorChange_cast_proof_irrel p q hpz hqw

/-- 水平切换边左格的中央端 potential 等于规范左下格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeft_endPotential_eq_central
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hBottom : D.label i j ≠ D.label k j)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hHorizontal hBottom
    ((Monoid.PushoutI.of (D.label i j) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
    i k j hHorizontal hBottom).map_endChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.horizontalSwitchLeftConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftEnd,
    CommonEdgeConnectorComparison.rightEnd]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece
      hxU hxV (D.label i j))
    (D.horizontalSwitchEdge_left_target_eq i k j hHorizontal hBottom)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialBottomLeft
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label i j))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one]
          using D.horizontalSwitchEdge_mem_intersection
            i k j hHorizontal hBottom 1⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      rfl
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label i j) hzc
      (D.horizontalSwitchEdge_left_target_eq i k j hHorizontal hBottom).symm
      (D.centralIntersectionVertex_toPiece_eq_bottomLeft
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 水平切换边右格的中央端 potential 等于规范右下格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRight_endPotential_eq_central
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hBottom : D.label i j ≠ D.label k j)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hHorizontal hBottom
    ((Monoid.PushoutI.of (D.label k j) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
    i k j hHorizontal hBottom).map_endChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.horizontalSwitchRightConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftEnd,
    CommonEdgeConnectorComparison.rightEnd]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece
      hxU hxV (D.label k j))
    (D.horizontalSwitchEdge_right_target_eq i k j hHorizontal hBottom)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialBottomRight
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label k j))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one]
          using D.horizontalSwitchEdge_mem_intersection
            i k j hHorizontal hBottom 1⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      rfl
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label k j) hzc
      (D.horizontalSwitchEdge_right_target_eq i k j hHorizontal hBottom).symm
      (D.centralIntersectionVertex_toPiece_eq_bottomRight
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 下方水平边切换标签时，其中央端 transition 是两个规范中央 potentials 的比值。-/
private theorem
    BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions_end_centralPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hBottom : D.label i j ≠ D.label k j)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.horizontalSwitchEdgeTransitions hxU hxV hUV hU hV
      i k j hHorizontal hBottom
    T.endChange = transitionFromPotentials
      (D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  dsimp only
  rw [D.horizontalSwitchEdgeTransitions_end_potential hxU hxV hUV hU hV
    i k j hHorizontal hBottom]
  rw [D.horizontalSwitchLeft_endPotential_eq_central hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hBottom hmixed,
    D.horizontalSwitchRight_endPotential_eq_central hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hBottom hmixed]

/-- 右侧竖直切换边下格的中央端 potential 等于规范右下格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottom_startPotential_eq_centralRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hRight : D.label k j ≠ D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      k j l hVertical hRight
    ((Monoid.PushoutI.of (D.label k j) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
    k j l hVertical hRight).map_startChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchBottomConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftStart,
    CommonEdgeConnectorComparison.rightStart]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label k j))
    (D.verticalSwitchEdge_bottom_source_eq k j l hVertical hRight)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialBottomRight
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label k j))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos k.castSucc j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero]
          using D.verticalSwitchEdge_mem_intersection k j l hVertical hRight 0⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      change squareGridVertex H D.steps D.steps_pos k.castSucc j.succ =
        squareGridVertex H D.steps D.steps_pos i.succ j.succ
      rw [hHorizontal]
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label k j) hzc
      (D.verticalSwitchEdge_bottom_source_eq k j l hVertical hRight).symm
      (D.centralIntersectionVertex_toPiece_eq_bottomRight
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 右侧竖直切换边上格的中央端 potential 等于规范右上格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTop_startPotential_eq_centralRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hRight : D.label k j ≠ D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      k j l hVertical hRight
    ((Monoid.PushoutI.of (D.label k l) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
    k j l hVertical hRight).map_startChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchTopConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftStart,
    CommonEdgeConnectorComparison.rightStart]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label k l))
    (D.verticalSwitchEdge_top_source_eq k j l hVertical hRight)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialTopRight
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label k l))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos k.castSucc j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero]
          using D.verticalSwitchEdge_mem_intersection k j l hVertical hRight 0⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      change squareGridVertex H D.steps D.steps_pos k.castSucc j.succ =
        squareGridVertex H D.steps D.steps_pos i.succ j.succ
      rw [hHorizontal]
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label k l) hzc
      (D.verticalSwitchEdge_top_source_eq k j l hVertical hRight).symm
      (D.centralIntersectionVertex_toPiece_eq_topRight
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 右侧竖直边切换标签时，其中央端 transition 是两个规范中央 potentials 的比值。-/
private theorem
    BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions_start_centralPotentialRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hRight : D.label k j ≠ D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.verticalSwitchEdgeTransitions hxU hxV hUV hU hV
      k j l hVertical hRight
    T.startChange = transitionFromPotentials
      (D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  dsimp only
  rw [D.verticalSwitchEdgeTransitions_start_potential hxU hxV hUV hU hV
    k j l hVertical hRight]
  rw [D.verticalSwitchBottom_startPotential_eq_centralRight hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hRight hmixed,
    D.verticalSwitchTop_startPotential_eq_centralRight hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hRight hmixed]

/-- 左侧竖直切换边下格的中央端 potential 等于规范左下格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalSwitchBottom_endPotential_eq_centralLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hLeft : D.label i j ≠ D.label i l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hVertical hLeft
    ((Monoid.PushoutI.of (D.label i j) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
    i j l hVertical hLeft).map_endChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchBottomConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftEnd,
    CommonEdgeConnectorComparison.rightEnd]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
    (D.verticalSwitchEdge_bottom_target_eq i j l hVertical hLeft)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialBottomLeft
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label i j))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one]
          using D.verticalSwitchEdge_mem_intersection i j l hVertical hLeft 1⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      rfl
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label i j) hzc
      (D.verticalSwitchEdge_bottom_target_eq i j l hVertical hLeft).symm
      (D.centralIntersectionVertex_toPiece_eq_bottomLeft
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 左侧竖直切换边上格的中央端 potential 等于规范左上格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalSwitchTop_endPotential_eq_centralLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hLeft : D.label i j ≠ D.label i l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hVertical hLeft
    ((Monoid.PushoutI.of (D.label i l) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
    i j l hVertical hLeft).map_endChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchTopConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftEnd,
    CommonEdgeConnectorComparison.rightEnd]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i l))
    (D.verticalSwitchEdge_top_target_eq i j l hVertical hLeft)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialTopLeft
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label i l))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one]
          using D.verticalSwitchEdge_mem_intersection i j l hVertical hLeft 1⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      rfl
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label i l) hzc
      (D.verticalSwitchEdge_top_target_eq i j l hVertical hLeft).symm
      (D.centralIntersectionVertex_toPiece_eq_topLeft
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 左侧竖直边切换标签时，其中央端 transition 是两个规范中央 potentials 的比值。-/
private theorem
    BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions_end_centralPotentialLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hLeft : D.label i j ≠ D.label i l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.verticalSwitchEdgeTransitions hxU hxV hUV hU hV
      i j l hVertical hLeft
    T.endChange = transitionFromPotentials
      (D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  dsimp only
  rw [D.verticalSwitchEdgeTransitions_end_potential hxU hxV hUV hU hV
    i j l hVertical hLeft]
  rw [D.verticalSwitchBottom_endPotential_eq_centralLeft hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hLeft hmixed,
    D.verticalSwitchTop_endPotential_eq_centralLeft hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hLeft hmixed]

/-- 上方水平切换边左格的中央端 potential 等于规范左上格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchLeft_startPotential_eq_centralTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hTop : D.label i l ≠ D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k l hHorizontal hTop
    ((Monoid.PushoutI.of (D.label i l) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
    i k l hHorizontal hTop).map_startChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.horizontalSwitchLeftConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftStart,
    CommonEdgeConnectorComparison.rightStart]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i l))
    (D.horizontalSwitchEdge_left_source_eq i k l hHorizontal hTop)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialTopLeft
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label i l))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ l.castSucc, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero]
          using D.horizontalSwitchEdge_mem_intersection i k l hHorizontal hTop 0⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      change squareGridVertex H D.steps D.steps_pos i.succ l.castSucc =
        squareGridVertex H D.steps D.steps_pos i.succ j.succ
      rw [hVertical]
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label i l) hzc
      (D.horizontalSwitchEdge_left_source_eq i k l hHorizontal hTop).symm
      (D.centralIntersectionVertex_toPiece_eq_topLeft
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 上方水平切换边右格的中央端 potential 等于规范右上格 potential。-/
private theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchRight_startPotential_eq_centralTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hTop : D.label i l ≠ D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let C := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k l hHorizontal hTop
    ((Monoid.PushoutI.of (D.label k l) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed := by
  dsimp only
  rw [(D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
    i k l hHorizontal hTop).map_startChange_inv]
  unfold BinaryOpenCoverSquareSubdivision.horizontalSwitchRightConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftStart,
    CommonEdgeConnectorComparison.rightStart]
  rw [connectorChange_cast_four_endpoints_right _ _
    (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label k l))
    (D.horizontalSwitchEdge_right_source_eq i k l hHorizontal hTop)]
  unfold BinaryOpenCoverSquareSubdivision.centralPotentialTopRight
    BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
  apply congrArg (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (D.label k l))
  apply congrArg₂ connectorChange
  · let z : ↥(U ∩ V) :=
      ⟨squareGridVertex H D.steps D.steps_pos i.succ l.castSucc, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero]
          using D.horizontalSwitchEdge_mem_intersection i k l hHorizontal hTop 0⟩
    have hzc : z = D.centralIntersectionVertex
        i k j l hHorizontal hVertical hmixed := by
      apply Subtype.ext
      change squareGridVertex H D.steps D.steps_pos i.succ l.castSucc =
        squareGridVertex H D.steps D.steps_pos i.succ j.succ
      rw [hVertical]
    exact binaryOpenCoverIntersectionConnectorInPiece_cast_eq hxU hxV hUV
      (D.label k l) hzc
      (D.horizontalSwitchEdge_right_source_eq i k l hHorizontal hTop).symm
      (D.centralIntersectionVertex_toPiece_eq_topRight
        i k j l hHorizontal hVertical hmixed).symm
  · rfl

/-- 上方水平边切换标签时，其中央端 transition 是两个规范中央 potentials 的比值。-/
private theorem
    BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions_start_centralPotentialTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hTop : D.label i l ≠ D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.horizontalSwitchEdgeTransitions hxU hxV hUV hU hV
      i k l hHorizontal hTop
    T.startChange = transitionFromPotentials
      (D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  dsimp only
  rw [D.horizontalSwitchEdgeTransitions_start_potential hxU hxV hUV hU hV
    i k l hHorizontal hTop]
  rw [D.horizontalSwitchLeft_startPotential_eq_centralTop hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hTop hmixed,
    D.horizontalSwitchRight_startPotential_eq_centralTop hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hTop hmixed]

/-- 显式指定单格标签的交集参考 potential，用于同标签相邻格的稳定 transport。-/
def BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (z : ↥(U ∩ V)) (i j : Fin D.steps) (a b : Fin 2)
    (label : Bool) (hlabel : D.label i j = label)
    (hz : binaryOpenCoverIntersectionToPiece U V label z =
      D.gridCellVertexInPieceOfLabel i j a b label hlabel) :
    binaryVanKampenPushout U V hxU hxV :=
  let hb := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV label
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV label z).cast hb hz.symm
  Monoid.PushoutI.of label
    (connectorChange reference
      (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
        i j a b label hlabel))

/-- 显式标签 potential 与标签等式证明无关。-/
theorem BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (z : ↥(U ∩ V)) (i j : Fin D.steps) (a b : Fin 2)
    (label₁ label₂ : Bool)
    (hlabel₁ : D.label i j = label₁) (hlabel₂ : D.label i j = label₂)
    (hz₁ : binaryOpenCoverIntersectionToPiece U V label₁ z =
      D.gridCellVertexInPieceOfLabel i j a b label₁ hlabel₁)
    (hz₂ : binaryOpenCoverIntersectionToPiece U V label₂ z =
      D.gridCellVertexInPieceOfLabel i j a b label₂ hlabel₂) :
    D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
        z i j a b label₁ hlabel₁ hz₁ =
      D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
        z i j a b label₂ hlabel₂ hz₂ := by
  cases hlabel₁
  cases hlabel₂
  rfl

/-- 下方水平边同标签时，其中央端 transition 仍由规范中央 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeTransitions_end_centralPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hBottom : D.label i j = D.label k j)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.horizontalCommonEdgeTransitions hxU hxV hU hV
      i k j hHorizontal hBottom
    T.endChange = transitionFromPotentials
      (D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
    i k j hHorizontal hBottom
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  let z := D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed
  have hzLeft : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel i j 1 1 (D.label i j) rfl :=
    D.centralIntersectionVertex_toPiece_eq_bottomLeft
      i k j l hHorizontal hVertical hmixed
  have hzRight : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel k j 0 1 (D.label i j) hBottom.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
    have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
      simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
    simp [z, BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
      BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
      BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
      unitSquareCellPoint, hHorizontal, hone]
  have href : C.edgeTarget =
      binaryOpenCoverIntersectionToPiece U V (D.label i j) z :=
    (D.horizontalCommonEdge_target_eq_left i k j hHorizontal hBottom).trans hzLeft.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)) href
  change (f C.endChange)⁻¹ = _
  rw [C.map_endChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.centralPotentialBottomLeft
      BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftEnd) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label i j) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
            hzLeft.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1))
    apply congrArg f
    rw [show C.leftEnd =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1).cast rfl
        (D.horizontalCommonEdge_target_eq_left i k j hHorizontal hBottom) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
      hzLeft href (D.horizontalCommonEdge_target_eq_left i k j hHorizontal hBottom)
  · let explicitRight := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z k j 0 1 (D.label i j) hBottom.symm hzRight
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z k j 0 1
      (D.label i j) (D.label k j) hBottom.symm rfl hzRight
      (D.centralIntersectionVertex_toPiece_eq_bottomRight
        i k j l hHorizontal hVertical hmixed)
    calc
      f (connectorChange reference C.rightEnd) = explicitRight := by
        unfold explicitRight
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightEnd =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            k j 0 1 (D.label i j) hBottom.symm).cast rfl
              (D.horizontalCommonEdge_target_eq_right
                i k j hHorizontal hBottom) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
          hzRight href (D.horizontalCommonEdge_target_eq_right i k j hHorizontal hBottom)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z k j 0 1 (D.label k j) rfl
          (D.centralIntersectionVertex_toPiece_eq_bottomRight
            i k j l hHorizontal hVertical hmixed) := hactual
      _ = D.centralPotentialBottomRight hxU hxV hUV hU hV
          i k j l hHorizontal hVertical hmixed := rfl

/-- 右侧竖直边同标签时，其中央端 transition 由规范右侧 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.verticalCommonEdgeTransitions_start_centralPotentialRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hRight : D.label k j = D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.verticalCommonEdgeTransitions hxU hxV hU hV
      k j l hVertical hRight
    T.startChange = transitionFromPotentials
      (D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
    k j l hVertical hRight
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label k j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label k j))
      (binaryOpenCoverBasepoint hxU hxV (D.label k j)) →*
      binaryVanKampenPushout U V hxU hxV)
  let z := D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed
  have hzBottom : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPieceOfLabel k j 0 1 (D.label k j) rfl :=
    D.centralIntersectionVertex_toPiece_eq_bottomRight
      i k j l hHorizontal hVertical hmixed
  have hzTop : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPieceOfLabel k l 0 0 (D.label k j) hRight.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
    simp [z, BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
      BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
      BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
      unitSquareCellPoint, hHorizontal, hVertical]
  have href : C.edgeSource =
      binaryOpenCoverIntersectionToPiece U V (D.label k j) z :=
    (D.verticalCommonEdge_source_eq_bottom k j l hVertical hRight).trans hzBottom.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label k j) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label k j)) href
  change (f C.startChange)⁻¹ = _
  rw [C.map_startChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.centralPotentialBottomRight
      BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftStart) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label k j) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label k j))
            hzBottom.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV k j 0 1))
    apply congrArg f
    rw [show C.leftStart =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV k j 0 1).cast rfl
        (D.verticalCommonEdge_source_eq_bottom k j l hVertical hRight) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label k j))
      hzBottom href (D.verticalCommonEdge_source_eq_bottom k j l hVertical hRight)
  · let explicitTop := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z k l 0 0 (D.label k j) hRight.symm hzTop
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z k l 0 0
      (D.label k j) (D.label k l) hRight.symm rfl hzTop
      (D.centralIntersectionVertex_toPiece_eq_topRight
        i k j l hHorizontal hVertical hmixed)
    calc
      f (connectorChange reference C.rightStart) = explicitTop := by
        unfold explicitTop
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightStart =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            k l 0 0 (D.label k j) hRight.symm).cast rfl
              (D.verticalCommonEdge_source_eq_top k j l hVertical hRight) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label k j))
          hzTop href (D.verticalCommonEdge_source_eq_top k j l hVertical hRight)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z k l 0 0 (D.label k l) rfl
          (D.centralIntersectionVertex_toPiece_eq_topRight
            i k j l hHorizontal hVertical hmixed) := hactual
      _ = D.centralPotentialTopRight hxU hxV hUV hU hV
          i k j l hHorizontal hVertical hmixed := rfl

/-- 左侧竖直边同标签时，其中央端 transition 由规范左侧 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.verticalCommonEdgeTransitions_end_centralPotentialLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hLeft : D.label i j = D.label i l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.verticalCommonEdgeTransitions hxU hxV hU hV
      i j l hVertical hLeft
    T.endChange = transitionFromPotentials
      (D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
    i j l hVertical hLeft
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  let z := D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed
  have hzBottom : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel i j 1 1 (D.label i j) rfl :=
    D.centralIntersectionVertex_toPiece_eq_bottomLeft
      i k j l hHorizontal hVertical hmixed
  have hzTop : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel i l 1 0 (D.label i j) hLeft.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
    have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
      simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
    simp [z, BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
      BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
      BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
      unitSquareCellPoint, hVertical, hone]
  have href : C.edgeTarget =
      binaryOpenCoverIntersectionToPiece U V (D.label i j) z :=
    (D.verticalCommonEdge_target_eq_bottom i j l hVertical hLeft).trans hzBottom.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)) href
  change (f C.endChange)⁻¹ = _
  rw [C.map_endChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.centralPotentialBottomLeft
      BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftEnd) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label i j) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
            hzBottom.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1))
    apply congrArg f
    rw [show C.leftEnd =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1).cast rfl
        (D.verticalCommonEdge_target_eq_bottom i j l hVertical hLeft) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
      hzBottom href (D.verticalCommonEdge_target_eq_bottom i j l hVertical hLeft)
  · let explicitTop := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z i l 1 0 (D.label i j) hLeft.symm hzTop
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z i l 1 0
      (D.label i j) (D.label i l) hLeft.symm rfl hzTop
      (D.centralIntersectionVertex_toPiece_eq_topLeft
        i k j l hHorizontal hVertical hmixed)
    calc
      f (connectorChange reference C.rightEnd) = explicitTop := by
        unfold explicitTop
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightEnd =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            i l 1 0 (D.label i j) hLeft.symm).cast rfl
              (D.verticalCommonEdge_target_eq_top i j l hVertical hLeft) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
          hzTop href (D.verticalCommonEdge_target_eq_top i j l hVertical hLeft)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z i l 1 0 (D.label i l) rfl
          (D.centralIntersectionVertex_toPiece_eq_topLeft
            i k j l hHorizontal hVertical hmixed) := hactual
      _ = D.centralPotentialTopLeft hxU hxV hUV hU hV
          i k j l hHorizontal hVertical hmixed := rfl

/-- 上方水平边同标签时，其中央端 transition 由规范上侧 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeTransitions_start_centralPotentialTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hTop : D.label i l = D.label k l)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.horizontalCommonEdgeTransitions hxU hxV hU hV
      i k l hHorizontal hTop
    T.startChange = transitionFromPotentials
      (D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
    i k l hHorizontal hTop
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i l) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i l))
      (binaryOpenCoverBasepoint hxU hxV (D.label i l)) →*
      binaryVanKampenPushout U V hxU hxV)
  let z := D.centralIntersectionVertex i k j l hHorizontal hVertical hmixed
  have hzLeft : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPieceOfLabel i l 1 0 (D.label i l) rfl :=
    D.centralIntersectionVertex_toPiece_eq_topLeft
      i k j l hHorizontal hVertical hmixed
  have hzRight : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPieceOfLabel k l 0 0 (D.label i l) hTop.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece, D.coe_gridCellVertexInPieceOfLabel]
    simp [z, BinaryOpenCoverSquareSubdivision.centralIntersectionVertex,
      BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece, unitSquareGridVertex,
      BinaryOpenCoverSquareSubdivision.gridCellMapInPiece, squareGridVertex,
      unitSquareCellPoint, hHorizontal, hVertical]
  have href : C.edgeSource =
      binaryOpenCoverIntersectionToPiece U V (D.label i l) z :=
    (D.horizontalCommonEdge_source_eq_left i k l hHorizontal hTop).trans hzLeft.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i l) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i l)) href
  change (f C.startChange)⁻¹ = _
  rw [C.map_startChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.centralPotentialTopLeft
      BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftStart) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label i l) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i l))
            hzLeft.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i l 1 0))
    apply congrArg f
    rw [show C.leftStart =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i l 1 0).cast rfl
        (D.horizontalCommonEdge_source_eq_left i k l hHorizontal hTop) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i l))
      hzLeft href (D.horizontalCommonEdge_source_eq_left i k l hHorizontal hTop)
  · let explicitRight := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z k l 0 0 (D.label i l) hTop.symm hzRight
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z k l 0 0
      (D.label i l) (D.label k l) hTop.symm rfl hzRight
      (D.centralIntersectionVertex_toPiece_eq_topRight
        i k j l hHorizontal hVertical hmixed)
    calc
      f (connectorChange reference C.rightStart) = explicitRight := by
        unfold explicitRight
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightStart =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            k l 0 0 (D.label i l) hTop.symm).cast rfl
              (D.horizontalCommonEdge_source_eq_right
                i k l hHorizontal hTop) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i l))
          hzRight href (D.horizontalCommonEdge_source_eq_right i k l hHorizontal hTop)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z k l 0 0 (D.label k l) rfl
          (D.centralIntersectionVertex_toPiece_eq_topRight
            i k j l hHorizontal hVertical hmixed) := hactual
      _ = D.centralPotentialTopRight hxU hxV hUV hU hV
          i k j l hHorizontal hVertical hmixed := rfl

/-- 混合中央点处，下方内部水平边的中央 transition 统一由规范 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions_end_centralPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k j hHorizontal
    T.endChange = transitionFromPotentials
      (D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  by_cases hBottom : D.label i j = D.label k j
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_left hBottom]
    exact D.horizontalCommonEdgeTransitions_end_centralPotential
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hBottom hmixed
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_right hBottom]
    exact D.horizontalSwitchEdgeTransitions_end_centralPotential
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hBottom hmixed

/-- 混合中央点处，右侧内部竖直边的中央 transition 统一由规范 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions_start_centralPotentialRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      k j l hVertical
    T.startChange = transitionFromPotentials
      (D.centralPotentialBottomRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  by_cases hRight : D.label k j = D.label k l
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_left hRight]
    exact D.verticalCommonEdgeTransitions_start_centralPotentialRight
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hRight hmixed
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_right hRight]
    exact D.verticalSwitchEdgeTransitions_start_centralPotentialRight
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hRight hmixed

/-- 混合中央点处，左侧内部竖直边的中央 transition 统一由规范 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions_end_centralPotentialLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hVertical
    T.endChange = transitionFromPotentials
      (D.centralPotentialBottomLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  by_cases hLeft : D.label i j = D.label i l
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_left hLeft]
    exact D.verticalCommonEdgeTransitions_end_centralPotentialLeft
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hLeft hmixed
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_right hLeft]
    exact D.verticalSwitchEdgeTransitions_end_centralPotentialLeft
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hLeft hmixed

/-- 混合中央点处，上方内部水平边的中央 transition 统一由规范 potentials 给出。-/
private theorem
    BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions_start_centralPotentialTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k l hHorizontal
    T.startChange = transitionFromPotentials
      (D.centralPotentialTopLeft hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed)
      (D.centralPotentialTopRight hxU hxV hUV hU hV
        i k j l hHorizontal hVertical hmixed) := by
  by_cases hTop : D.label i l = D.label k l
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_left hTop]
    exact D.horizontalCommonEdgeTransitions_start_centralPotentialTop
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hTop hmixed
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_right hTop]
    exact D.horizontalSwitchEdgeTransitions_start_centralPotentialTop
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hTop hmixed

/-- 四格不全同标签时，真实内部边 transitions 在中央顶点满足方块 coherence。-/
private theorem BinaryOpenCoverSquareSubdivision.mixedCentralInternalTransitions_square
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hmixed : ¬ (D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l)) :
    let HB := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k j hHorizontal
    let VR := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      k j l hVertical
    let VL := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hVertical
    let HT := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k l hHorizontal
    VR.startChange * HB.endChange = HT.startChange * VL.endChange := by
  apply edgeTransitions_gridVertex_square
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV k j l hVertical)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
    (D.centralPotentialBottomLeft hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hmixed)
    (D.centralPotentialBottomRight hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hmixed)
    (D.centralPotentialTopLeft hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hmixed)
    (D.centralPotentialTopRight hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hmixed)
  · exact D.horizontalInternalEdgeTransitions_end_centralPotential
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hmixed
  · exact D.verticalInternalEdgeTransitions_start_centralPotentialRight
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hmixed
  · exact D.verticalInternalEdgeTransitions_end_centralPotentialLeft
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hmixed
  · exact D.horizontalInternalEdgeTransitions_start_centralPotentialTop
      hxU hxV hUV hU hV i k j l hHorizontal hVertical hmixed

/-- 显式共同标签承载的水平 common transition。-/
private def BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeTransitionsOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (b : Bool) (hleft : D.label i j = b) (hright : D.label k j = b) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  let C := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
    i k j hshared b hleft hright
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) b :
    FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) →*
      binaryVanKampenPushout U V hxU hxV)
  { startChange := (f C.startChange)⁻¹
    endChange := (f C.endChange)⁻¹ }

/-- 显式共同标签承载的竖直 common transition。-/
private def BinaryOpenCoverSquareSubdivision.verticalCommonEdgeTransitionsOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (b : Bool) (hbottom : D.label i j = b) (htop : D.label i l = b) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  let C := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
    i j l hshared b hbottom htop
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) b :
    FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) →*
      binaryVanKampenPushout U V hxU hxV)
  { startChange := (f C.startChange)⁻¹
    endChange := (f C.endChange)⁻¹ }

private theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeTransitionsOfLabel_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (b : Bool) (hleft : D.label i j = b) (hright : D.label k j = b) :
    D.horizontalCommonEdgeTransitionsOfLabel hxU hxV hU hV
        i k j hshared b hleft hright =
      D.horizontalCommonEdgeTransitions hxU hxV hU hV
        i k j hshared (hleft.trans hright.symm) := by
  cases hleft
  rfl

private theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdgeTransitionsOfLabel_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (b : Bool) (hbottom : D.label i j = b) (htop : D.label i l = b) :
    D.verticalCommonEdgeTransitionsOfLabel hxU hxV hU hV
        i j l hshared b hbottom htop =
      D.verticalCommonEdgeTransitions hxU hxV hU hV
        i j l hshared (hbottom.trans htop.symm) := by
  cases hbottom
  rfl

/-- 四格显式共享一个标签时，四条 common transitions 满足中央方块关系。-/
private theorem BinaryOpenCoverSquareSubdivision.commonCentralEdgeTransitionsOfLabel_square
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTL : D.label i l = b) (hTR : D.label k l = b) :
    let HB := D.horizontalCommonEdgeTransitionsOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VR := D.verticalCommonEdgeTransitionsOfLabel hxU hxV hU hV
      k j l hVertical b hBR hTR
    let VL := D.verticalCommonEdgeTransitionsOfLabel hxU hxV hU hV
      i j l hVertical b hBL hTL
    let HT := D.horizontalCommonEdgeTransitionsOfLabel hxU hxV hU hV
      i k l hHorizontal b hTL hTR
    VR.startChange * HB.endChange = HT.startChange * VL.endChange := by
  exact D.commonCentralTransition_square_of_label hxU hxV hU hV
    i k j l hHorizontal hVertical b hBL hBR hTL hTR

/-- 四格全同标签时，真实 internal transitions 满足中央方块关系。-/
private theorem BinaryOpenCoverSquareSubdivision.allCommonCentralInternalTransitions_square
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (hBottom : D.label i j = D.label k j)
    (hLeft : D.label i j = D.label i l)
    (hDiagonal : D.label i j = D.label k l) :
    let HB := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k j hHorizontal
    let VR := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      k j l hVertical
    let VL := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hVertical
    let HT := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k l hHorizontal
    VR.startChange * HB.endChange = HT.startChange * VL.endChange := by
  have hRight : D.label k j = D.label k l := hBottom.symm.trans hDiagonal
  have hTop : D.label i l = D.label k l := hLeft.symm.trans hDiagonal
  have h := D.commonCentralEdgeTransitionsOfLabel_square hxU hxV hU hV
    i k j l hHorizontal hVertical (D.label i j)
    rfl hBottom.symm hLeft.symm hDiagonal.symm
  rw [D.horizontalCommonEdgeTransitionsOfLabel_eq hxU hxV hU hV
      i k j hHorizontal (D.label i j) rfl hBottom.symm,
    D.verticalCommonEdgeTransitionsOfLabel_eq hxU hxV hU hV
      k j l hVertical (D.label i j) hBottom.symm hDiagonal.symm,
    D.verticalCommonEdgeTransitionsOfLabel_eq hxU hxV hU hV
      i j l hVertical (D.label i j) rfl hLeft.symm,
    D.horizontalCommonEdgeTransitionsOfLabel_eq hxU hxV hU hV
      i k l hHorizontal (D.label i j) hLeft.symm hDiagonal.symm] at h
  simp only [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
    dite_eq_left hBottom, dite_eq_left hTop,
    BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
    dite_eq_left hRight, dite_eq_left hLeft]
  exact h

/-- 任意四个相邻小格的真实内部边 transitions 都在中央顶点满足方块 coherence。-/
theorem BinaryOpenCoverSquareSubdivision.centralInternalTransitions_square
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc) :
    let HB := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k j hHorizontal
    let VR := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      k j l hVertical
    let VL := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hVertical
    let HT := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k l hHorizontal
    VR.startChange * HB.endChange = HT.startChange * VL.endChange := by
  by_cases hAll : D.label i j = D.label k j ∧
      D.label i j = D.label i l ∧ D.label i j = D.label k l
  · exact D.allCommonCentralInternalTransitions_square hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hAll.1 hAll.2.1 hAll.2.2
  · exact D.mixedCentralInternalTransitions_square hxU hxV hUV hU hV
      i k j l hHorizontal hVertical hAll

end SandronesLibrary.Topology
